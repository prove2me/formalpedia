-- Prove2me | Definitions.Def_SKAlgorithm_Qudit_Model
-- name    : SKAlgorithm_Qudit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:15.566596+00:00
-- url     : https://prove2.me/theorems/68d1d11d-09ed-4b2b-ac02-36eb1064198b
-- title:
--   Definition 1, p. 2; p. 3; pseudocode, p. 10 — instruction sets, gate sequences, operator-norm distance and the Solovay-Kitaev recursion
-- statement:
--   Throughout, $d \ge 0$ is the dimension of a qudit and $SU(d)$ is the group of $d \times d$ complex unitary matrices of determinant $1$. For a unitary $U$ we write $U^\dagger = U^{-1}$ for its adjoint.
--
--   1. **Distance.** For gates $U, V \in SU(d)$ the distance is
--   $$d(U, V) = \|U - V\| = \sup_{\|\psi\| = 1} \|(U - V)\psi\|,$$
--   the operator norm of the difference (p. 3).
--   2. **Sequences.** A finite sequence $S = g_1, g_2, \dots, g_m$ of gates also denotes the unitary $g_1 g_2 \cdots g_m$ (so the gates are applied in reverse order; the empty sequence denotes $I$). The *inverse sequence* of $S$ is $g_m^\dagger, \dots, g_1^\dagger$; its unitary is $(g_1 \cdots g_m)^\dagger$.
--   3. **Instruction set** (Definition 1). A finite set $\mathcal G \subseteq SU(d)$ is an instruction set if $g^\dagger \in \mathcal G$ for every $g \in \mathcal G$, and $\mathcal G$ is universal: for every $U \in SU(d)$ and every $\epsilon > 0$ there is a finite sequence $S$ of gates from $\mathcal G$ with $d(U, S) < \epsilon$.
--   4. **The Solovay-Kitaev recursion** (pseudocode, p. 10). Fix a lookup routine $\mathrm{basic}$ that returns a gate sequence for each $U \in SU(d)$, and a decomposition routine $\mathrm{gc}$ that, at recursion level $k$, returns a pair $(V, W)$ for each $\Delta \in SU(d)$. Then $\mathrm{SK}(U, 0) = \mathrm{basic}(U)$ and, for $n \ge 0$, with $U_n = \mathrm{SK}(U, n)$, $(V, W) = \mathrm{gc}_n(U U_n^\dagger)$, $V_n = \mathrm{SK}(V, n)$, $W_n = \mathrm{SK}(W, n)$,
--   $$\mathrm{SK}(U, n+1) = V_n\, W_n\, V_n^\dagger\, W_n^\dagger\, U_n,$$
--   the concatenation of the five sequences, a dagger denoting the inverse sequence.
--   5. **Accuracies** (Eq. (1)). For constants $c, \epsilon_0$, the sequence $\epsilon_n$ is defined by $\epsilon_n = c\, \epsilon_{n-1}^{3/2}$.
--
--   These are the objects of Dawson and Nielsen's account of the Solovay-Kitaev theorem and algorithm; every statement of the mission is phrased in them.
--
--   **Formalization Note.** The operator norm is the published `QAlgorithms.specNorm` (the $\ell^2$ operator norm of a matrix), never Mathlib's default entrywise norm. $SU(d)$ is `Matrix.specialUnitaryGroup (Fin d) ℂ`, in which $g^{-1} = g^\dagger$. Universality is the paper's own gloss of part 3 of Definition 1 ("given any quantum gate $U$ … and any accuracy $\epsilon > 0$ there exists a product … which is an $\epsilon$-approximation to $U$"), not the literal density of the generated group; with closure under $\dagger$ the two are equivalent. The decomposition routine carries the recursion level as an extra argument: the pseudocode's call at depth $n+1$ is $\mathrm{gc}_n(U U_n^\dagger)$, because the paper's guarantee for GC-Approx-Decompose is relative to the current accuracy $\epsilon_n$. The power $x^{3/2}$ is the real power `x ^ (3/2 : ℝ)`.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 2, Definition 1; p. 3 (operator norm, sequence convention, inverse sequence); p. 10, pseudocode of §5.1; p. 6, Eq. (1)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

noncomputable section
open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

/-- The special unitary group SU(d) of `d × d` complex unitary matrices of determinant 1. -/
abbrev SU (d : ℕ) := Matrix.specialUnitaryGroup (Fin d) ℂ

/-- p. 3: the distance d(U, S) ≡ ‖U − S‖ between two gates, measured in the operator norm
sup_{‖ψ‖=1} ‖(U − S)ψ‖ (`QAlgorithms.specNorm`, the ℓ²-operator norm of matrices). -/
def opDist {d : ℕ} (U V : SU d) : ℝ :=
  specNorm ((U : Matrix (Fin d) (Fin d) ℂ) - (V : Matrix (Fin d) (Fin d) ℂ))

/-- p. 3: the unitary g₁ g₂ ⋯ g_m corresponding to the instruction sequence g₁, g₂, …, g_m
(so the gates are applied in reverse order). The empty sequence gives the identity. -/
def seqUnitary {d : ℕ} (S : List (SU d)) : SU d := S.prod

/-- p. 3: the reversed sequence of inverse instructions, g_m†, …, g₁†. -/
def invSeq {d : ℕ} (S : List (SU d)) : List (SU d) := (S.map (·⁻¹)).reverse

/-- Definition 1, p. 2: `G` is an instruction set for SU(d): a finite set of gates of SU(d),
closed under g ↦ g† (= g⁻¹ in SU(d)), and universal in the sense of the paper's gloss of part 3:
for every gate U ∈ SU(d) and every accuracy ε > 0 there is a finite sequence of gates from `G`
whose product is an ε-approximation to U, i.e. d(U, S) < ε. -/
def IsInstructionSet {d : ℕ} (G : Finset (SU d)) : Prop :=
  (∀ g ∈ G, g⁻¹ ∈ G) ∧
  ∀ U : SU d, ∀ ε : ℝ, 0 < ε →
    ∃ S : List (SU d), (∀ g ∈ S, g ∈ G) ∧ opDist U (seqUnitary S) < ε

/-- Pseudocode, p. 10 (qudit version of pp. 4–5). `basic U` is the basic ε₀-approximation looked
up at depth 0; `gc k Δ` is the pair (V, W) returned by GC-Approx-Decompose when it is called at
recursion depth k + 1, i.e. on Δ = U U_k† with U_k an ε_k-approximation to U. At depth n + 1:
U_n := SK(U, n); (V, W) := gc n (U U_n†); V_n := SK(V, n); W_n := SK(W, n); and the returned
sequence is V_n W_n V_n† W_n† U_n (sequences concatenated, a dagger meaning `invSeq`). -/
def solovayKitaev {d : ℕ} (basic : SU d → List (SU d)) (gc : ℕ → SU d → SU d × SU d) :
    ℕ → SU d → List (SU d)
  | 0, U => basic U
  | n + 1, U =>
    let Un := solovayKitaev basic gc n U
    let VW := gc n (U * (seqUnitary Un)⁻¹)
    let Vn := solovayKitaev basic gc n VW.1
    let Wn := solovayKitaev basic gc n VW.2
    Vn ++ Wn ++ invSeq Vn ++ invSeq Wn ++ Un

/-- Eq. (1), p. 6 (and Eq. (22), p. 11): the accuracies ε_n = c ε_{n−1}^{3/2} of the recursion,
starting from ε₀. -/
def epsSeq (c ε₀ : ℝ) (n : ℕ) : ℝ := (fun x : ℝ => c * x ^ ((3 : ℝ) / 2))^[n] ε₀

end SKAlgorithm.Qudit


