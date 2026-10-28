-- Prove2me | Definitions.Def_DeFinettiSDP_Hierarchy_Systems
-- name    : DeFinettiSDP_Hierarchy_Systems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:09.779032+00:00
-- url     : https://prove2.me/theorems/58f88bb2-5e5b-48e8-858e-265cc0da0292
-- title:
--   §1, §2.1, pp. 1–4 — systems A ⊗ Bⁿ, the permutation action U^π, linear maps on one factor, measurements, ‖·‖∞
-- statement:
--   This file fixes the multipartite systems and the elementary operations used throughout the paper.
--
--   A $d$-dimensional quantum system is described by the operators $\mathcal S = \mathbb C^{d\times d}$. The bipartite system $A\otimes B$ (dimensions $d_A$, $d_B$) has operators indexed by pairs $(a,b)$, and $N$ copies $B_1\cdots B_N$ of $B$ have operators indexed by words $x=(x_1,\dots,x_N)$ with letters in $\{1,\dots,d_B\}$. The following objects are defined.
--
--   1. **Permutation action** (§2.1, p. 4). For $\pi\in\mathfrak S_N$, $(\mathcal I_A\otimes\mathcal U^\pi_{B_1^N})(W)$ permutes the $N$ copies of $B$ and leaves $A$ fixed:
--   $$\big((\mathcal I_A\otimes\mathcal U^\pi_{B_1^N})W\big)_{(a,x),(a',x')} = W_{(a,x\circ\pi),(a',x'\circ\pi)}.$$
--   2. **Marginals.** $W_{B_1^N}=\mathrm{Tr}_A W$; for $N=n+1$, the reduced state $W_{AB_1}=\mathrm{Tr}_{B_2\cdots B_{n+1}}W$ on $A\otimes B_1$; the view of an operator $V$ on $B_1\cdots B_{n+1}$ as an operator on $(B_1\cdots B_n)\otimes B_{n+1}$; and its marginal $V_{B_1^n}=\mathrm{Tr}_{B_{n+1}}V$.
--   3. **A linear map on one factor.** For a linear map $\Lambda:\mathcal S_A\to\mathcal S_{C_A}$ and an operator $W$ on $A\otimes R$, $(\Lambda\otimes\mathcal I_R)(W)$ applies $\Lambda$ to each $A$-block $(W_{(a,r),(a',r')})_{a,a'}$; similarly $(\mathcal I_L\otimes\Gamma)(V)$ for a linear map $\Gamma:\mathcal S_B\to\mathcal S_{C_B}$ on the last factor. On product operators these are $\Lambda(X)\otimes Y$ and $X\otimes\Gamma(Y)$.
--   4. **Measurements** (p. 4). A measurement with $t$ outcomes is a family of positive semidefinite $M_1,\dots,M_t$ with $\sum_z M_z=\mathbb 1$. For any family $M$ on $B$, $(\mathcal I_A\otimes\mathcal M_B)(\xi)$ is the block-diagonal operator on $A\otimes Z$ with blocks $\mathrm{Tr}_B[(\mathbb 1_A\otimes M_z)\xi]$; for families $M^A$, $M^B$, $(\mathcal M_A\otimes\mathcal M_B)(\xi)$ is the diagonal operator with entries $\mathrm{Tr}[(M^A_x\otimes M^B_y)\xi]$.
--   5. **Schatten $\infty$-norm** (p. 11). $\|G\|_\infty$ is the largest singular value of $G$, i.e. the square root of the largest eigenvalue of $G^\dagger G$.
--
--   These are the building blocks of the hierarchy $\mathrm{SDP}_n$ and of the de Finetti theorem with linear constraints.
--
--   **Formalization Note** Systems are finite index types: $A\otimes B_1\cdots B_N$ is indexed by `Fin dA × (Fin N → Fin dB)`, and $\otimes$ is Mathlib's Kronecker product. The first copy of $B$ is split off with `Fin.cons`, the last with `Fin.snoc`. The permutation action is written with $x\circ\pi$; whether this is $\mathcal U^\pi$ or $\mathcal U^{\pi^{-1}}$ is immaterial because every statement quantifies over all $\pi$. The maps $\Lambda$, $\Gamma$ are arbitrary $\mathbb C$-linear maps, as in the paper. On an empty index set $\|G\|_\infty=0$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §1 (p. 1, problem (2)) and §2.1, pp. 3–4; ‖·‖∞ as used on p. 11

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace

/-!
Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §1 (p. 1) and §2.1 (pp. 3–4): the
multipartite systems, the permutation action, linear maps acting on one tensor factor,
measurements and the Schatten ∞-norm.

Conventions. A `d`-dimensional system is the index type `Fin d`; operators on it are
`Matrix (Fin d) (Fin d) ℂ`. The bipartite system `A ⊗ B` is indexed by `Fin dA × Fin dB`
(Mathlib's Kronecker convention `⊗ₖ`), and `N` copies `B₁ ⋯ B_N` of `B` are indexed by the
words `Fin N → Fin dB`; so `A ⊗ B^N` is indexed by `Fin dA × (Fin N → Fin dB)`.
-/

namespace DeFinettiSDP.Hierarchy

open Matrix
open scoped Kronecker ComplexOrder

/-- The permutation action `(I_A ⊗ U^π_{B₁⋯B_N})` of §2.1, p. 4, on an operator on
`A ⊗ B₁ ⋯ B_N`: it permutes the `N` copies of `B` and leaves `A` fixed. Whether this is
`U^π` or `U^{π⁻¹}` is immaterial: every statement quantifies over all permutations `π`. -/
def permB {dA dB N : ℕ} (π : Equiv.Perm (Fin N))
    (W : Matrix (Fin dA × (Fin N → Fin dB)) (Fin dA × (Fin N → Fin dB)) ℂ) :
    Matrix (Fin dA × (Fin N → Fin dB)) (Fin dA × (Fin N → Fin dB)) ℂ :=
  W.submatrix (fun p => (p.1, p.2 ∘ π)) (fun p => (p.1, p.2 ∘ π))

/-- The marginal `W_{B₁⋯B_N} = Tr_A W` on the `B` systems. -/
def trA {dA dB N : ℕ}
    (W : Matrix (Fin dA × (Fin N → Fin dB)) (Fin dA × (Fin N → Fin dB)) ℂ) :
    Matrix (Fin N → Fin dB) (Fin N → Fin dB) ℂ :=
  WildeQIT.partialTraceLeft W

/-- Regrouping `(A × B₁) × (B₂ ⋯ B_{n+1}) ≃ A × (B₁ ⋯ B_{n+1})`: the first copy `B₁` is
split off with `Fin.cons`. -/
def regroupFirst (dA dB n : ℕ) :
    (Fin dA × Fin dB) × (Fin n → Fin dB) ≃ Fin dA × (Fin (n + 1) → Fin dB) :=
  (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin n → Fin dB)).trans
    (Equiv.prodCongr (Equiv.refl (Fin dA)) (Fin.consEquiv fun _ => Fin dB))

/-- The reduced state `W_{AB₁} = Tr_{B₂ ⋯ B_{n+1}} W` of an operator on `A ⊗ B₁ ⋯ B_{n+1}`. -/
def keepAB1 {dA dB n : ℕ}
    (W : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  WildeQIT.partialTraceRight (W.submatrix (regroupFirst dA dB n) (regroupFirst dA dB n))

/-- An operator on `B₁ ⋯ B_{n+1}` viewed on `(B₁ ⋯ B_n) ⊗ B_{n+1}`: the last copy is split off
with `Fin.snoc`. -/
def splitLast {dB n : ℕ} (V : Matrix (Fin (n + 1) → Fin dB) (Fin (n + 1) → Fin dB) ℂ) :
    Matrix ((Fin n → Fin dB) × Fin dB) ((Fin n → Fin dB) × Fin dB) ℂ :=
  V.submatrix (fun p => Fin.snocEquiv (fun _ => Fin dB) (p.2, p.1))
    (fun p => Fin.snocEquiv (fun _ => Fin dB) (p.2, p.1))

/-- The marginal `V_{B₁ ⋯ B_n} = Tr_{B_{n+1}} V`: the last copy is traced out. -/
def trLast {dB n : ℕ} (V : Matrix (Fin (n + 1) → Fin dB) (Fin (n + 1) → Fin dB) ℂ) :
    Matrix (Fin n → Fin dB) (Fin n → Fin dB) ℂ :=
  WildeQIT.partialTraceRight (splitLast V)

/-- `(Λ ⊗ I_R)(W)` for a linear map `Λ : S_A → S_{C_A}` acting on the first tensor factor of an
operator `W` on `A ⊗ R`: `Λ` is applied blockwise to the `A`-blocks `(W_{(a,r),(a',r')})_{a,a'}`.
On product operators `applyFirst Λ (X ⊗ₖ Y) = Λ X ⊗ₖ Y`. -/
def applyFirst {dA cA : ℕ} {R : Type}
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (W : Matrix (Fin dA × R) (Fin dA × R) ℂ) : Matrix (Fin cA × R) (Fin cA × R) ℂ :=
  Matrix.of fun p q => Λ (Matrix.of fun a a' => W (a, p.2) (a', q.2)) p.1 q.1

/-- `(I_L ⊗ Γ)(V)` for a linear map `Γ : S_B → S_{C_B}` acting on the last tensor factor of an
operator `V` on `L ⊗ B`, blockwise. On product operators `applyLast Γ (X ⊗ₖ Y) = X ⊗ₖ Γ Y`. -/
def applyLast {dB cB : ℕ} {L : Type}
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (V : Matrix (L × Fin dB) (L × Fin dB) ℂ) : Matrix (L × Fin cB) (L × Fin cB) ℂ :=
  Matrix.of fun p q => Γ (Matrix.of fun b b' => V (p.1, b) (q.1, b')) p.2 q.2

/-- A measurement with `t` outcomes on a `d`-dimensional system (§2.1, p. 4): positive
semidefinite effects `M z` summing to the identity. -/
def IsPOVM {d t : ℕ} (M : Fin t → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ z, (M z).PosSemidef) ∧ ∑ z, M z = 1

/-- `(I_A ⊗ M_B)(ξ)` for a family `M` of operators on `B` (§2.1, p. 4,
`M(·) = ∑_z Tr[M_z ·] |z⟩⟨z|`): the block-diagonal operator on `A ⊗ Z` whose `(z, z)` block is
`Tr_B[(1_A ⊗ M_z) ξ]` and whose off-diagonal blocks vanish. Defined for any family `M`, not only
for measurements. -/
def measB {α : Type} [Fintype α] {dB t : ℕ} (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (ξ : Matrix (α × Fin dB) (α × Fin dB) ℂ) : Matrix (α × Fin t) (α × Fin t) ℂ :=
  Matrix.of fun p q =>
    if p.2 = q.2 then ∑ b, ∑ b', M p.2 b' b * ξ (p.1, b) (q.1, b') else 0

/-- `(M_A ⊗ M_B)(ξ)` for families `MA` on `A` and `MB` on `B`: the diagonal operator on the
classical outcome system `Z_A ⊗ Z_B` with entries `Tr[(MA x ⊗ MB y) ξ]`. -/
def measAB {dA dB tA tB : ℕ} (MA : Fin tA → Matrix (Fin dA) (Fin dA) ℂ)
    (MB : Fin tB → Matrix (Fin dB) (Fin dB) ℂ)
    (ξ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix (Fin tA × Fin tB) (Fin tA × Fin tB) ℂ :=
  Matrix.diagonal fun xy => Matrix.trace ((MA xy.1 ⊗ₖ MB xy.2) * ξ)

/-- The Schatten ∞-norm `‖G‖_∞` (p. 11): the largest singular value of `G`, i.e. the square root
of the largest eigenvalue of the positive semidefinite matrix `Gᴴ G` (`0` on an empty index). -/
noncomputable def opNormInf {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt (⨆ i, (Matrix.isHermitian_conjTranspose_mul_self G).eigenvalues i)

end DeFinettiSDP.Hierarchy


