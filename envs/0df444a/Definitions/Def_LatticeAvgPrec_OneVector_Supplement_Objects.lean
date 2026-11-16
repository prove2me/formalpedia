-- Prove2me | Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
-- name    : LatticeAvgPrec_OneVector_Supplement_Objects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:39:40.115202+00:00
-- url     : https://prove2.me/theorems/2be74586-7490-4e62-a255-084bed43fb75
-- title:
--   Smallest singular value, successive minima of $V\Gamma$, bounded short-span extraction (Def. 4.5), polynomial codes
-- statement:
--   This file adds the objects of §§4–6 that the published definitions of the mission do not cover. All other notions (bitwise codes, $\mathrm{bits}$, row bitlengths, $\Lambda(B)$, Euclidean norms, $\lambda_i$, $\|\cdot\|_2$, $\kappa_{\rm col}$, HNF, Smith massagers, $\widetilde O$, $\omega$) are the published ones.
--
--   1. **Smallest singular value.** For a real $a\times b$ matrix $M$, $\sigma_{\min}(M)$ is its $\min(a,b)$-th singular value: for $b\le a$,
--   $$\sigma_{\min}(M)=\inf\{\|Mx\|_2:\|x\|_2=1\},$$
--   and for $a<b$ the same infimum for $M^{\mathsf T}$. On a matrix of full row or full column rank it is positive (pp. 14, 18).
--   2. **Successive minima of $V\Gamma$.** For $\Gamma\subseteq\mathbb Z^r$ and a real $r\times r$ matrix $V$, $\lambda_i(V\Gamma)$ is the least $\rho\ge0$ such that $V\Gamma=\{Vz:z\in\Gamma\}$ contains $i$ linearly independent vectors of Euclidean length at most $\rho$ (pp. 14, 16). For $V=I$ it is the published $\lambda_i$.
--   3. **Integer span.** For real vectors $X_1,\dots,X_s$, $X\mathbb Z^s=\{\sum_i a_iX_i:a\in\mathbb Z^s\}$.
--   4. **Bounded short-span extraction (Definition 4.5, p. 16).** For a rank-$r$ Euclidean lattice $\Lambda$, a radius $B$ and a constant $c$, vectors $X_1,\dots,X_s$ (possibly $s=0$) are a valid output if they are linearly independent vectors of $\Lambda$ with
--   $$\{y\in\Lambda:\|y\|_2\le B\}\subseteq X\mathbb Z^s\subseteq\Lambda,\qquad \|X_i\|_2\le 2^{c\,r\log_2(2r)}B .$$
--   The constant $c$ is the one hidden in Definition 4.5's $2^{O(r\log(2r))}$.
--   5. **Integer polynomials (p. 22).** A polynomial $P\in\mathbb Z[x]$ of degree $N$ is coded by the published code of its coefficient vector $(P_0,\dots,P_N)$; its coefficient bitlength is $\tau=\max_i\mathrm{bits}(P_i)$. A list of factors with multiplicities $((u_1,e_1),\dots,(u_k,e_k))$ is coded by its length followed by the codes of each $u_i$ and $e_i$.
--
--   These objects are used by Lemmas 4.8 and 4.9 ($\sigma_{\min}$), Theorem 4.6 ($\lambda_i(V\Gamma)$, Definition 4.5), Theorem 5.1 (Definition 4.5) and Theorem 1.4 (polynomial codes).
--
--   **Formalization Note** $\sigma_{\min}$ and $\lambda_i(V\Gamma)$ are infima of real sets; they take Lean's default value $0$ only on an empty set (a $0$-column matrix, or $i$ larger than the rank), which no statement of the mission uses. Definition 4.5 is stated as a predicate on the output with its constant as an argument, so that an algorithm "meeting Definition 4.5" can be quantified with its constant fixed before the input.
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), §4 pp.14, 16 (Definition 4.5), 18; §6 p.22

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- The smallest singular value `σ_min(M)` of a real `a × b` matrix (pp.14, 18): its
`min(a, b)`-th singular value. For `b ≤ a` it is `inf {‖Mx‖₂ : ‖x‖₂ = 1}`; for `a < b` it is
`inf {‖Mᵀy‖₂ : ‖y‖₂ = 1}`. On a matrix of full row or column rank it is positive. -/
noncomputable def sigmaMin {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  if b ≤ a then sInf ((fun x : Fin b → ℝ => l2 (M *ᵥ x)) '' {x | l2 x = 1})
  else sInf ((fun y : Fin a → ℝ => l2 (Mᵀ *ᵥ y)) '' {y | l2 y = 1})

/-- The `i`-th successive minimum `λ_i(VΓ)` of the real lattice `VΓ = {Vz : z ∈ Γ}` (p.14, p.16):
the least `ρ ≥ 0` such that `VΓ` contains `i` linearly independent vectors of Euclidean length at
most `ρ`. For `V = I` it is the published `lam`. -/
noncomputable def lamV {r : ℕ} (V : Matrix (Fin r) (Fin r) ℝ) (Γ : Set (Fin r → ℤ)) (i : ℕ) : ℝ :=
  sInf {ρ : ℝ | 0 ≤ ρ ∧ ∃ zs : Fin i → Fin r → ℤ, (∀ j, zs j ∈ Γ) ∧
    LinearIndependent ℝ (fun j => V *ᵥ fun t => ((zs j t : ℤ) : ℝ)) ∧
    ∀ j, l2 (V *ᵥ fun t => ((zs j t : ℤ) : ℝ)) ≤ ρ}

/-- The integer span `XZ^s = {Σ_i a_i X_i : a ∈ ℤ^s}` of real vectors `X_1, …, X_s`. -/
def intSpanR {k s : ℕ} (X : Fin s → Fin k → ℝ) : Set (Fin k → ℝ) :=
  Set.range (fun a : Fin s → ℤ => ∑ i, ((a i : ℤ) : ℝ) • X i)

/-- Definition 4.5 (Bounded short-span extraction, p.16), output condition with the constant `c`
of `2^{O(r log(2r))}` made explicit: for a rank-`r` Euclidean lattice `Λ` and a radius `B`, the
vectors `X_1, …, X_s` (possibly `s = 0`) are linearly independent lattice vectors with
`{y ∈ Λ : ‖y‖₂ ≤ B} ⊆ XZ^s ⊆ Λ` and `‖X_i‖₂ ≤ 2^{c r log₂(2r)} B`. -/
def IsShortSpanExt (c : ℝ) (r : ℕ) {k s : ℕ} (Λ : Set (Fin k → ℝ)) (B : ℝ)
    (X : Fin s → Fin k → ℝ) : Prop :=
  LinearIndependent ℝ X ∧ (∀ i, X i ∈ Λ) ∧ {y | y ∈ Λ ∧ l2 y ≤ B} ⊆ intSpanR X ∧
    intSpanR X ⊆ Λ ∧ ∀ i, l2 (X i) ≤ (2 : ℝ) ^ (c * r * Real.logb 2 (2 * r)) * B

/-- Code of an integer polynomial (p.22): the code of its coefficient vector
`(P_0, …, P_N)`, `N = deg P`, in the published bitwise vector code. -/
noncomputable def polyCode (P : Polynomial ℤ) : List ℕ :=
  vecCode (fun i : Fin (P.natDegree + 1) => P.coeff i)

/-- Coefficient bitlength `τ = max_i bits(P_i)` of an integer polynomial (p.22), with the paper's
signed bitlength `bits`. -/
noncomputable def coeffBits (P : Polynomial ℤ) : ℕ :=
  (Finset.range (P.natDegree + 1)).sup (fun i => bits (P.coeff i))

/-- Code of a list of factors with multiplicities `((u_1, e_1), …, (u_k, e_k))`: its length, then
for each pair the code of `u_i` and the code of `e_i`. -/
noncomputable def factorListCode (l : List (Polynomial ℤ × ℕ)) : List ℕ :=
  natCode l.length ++ l.flatMap (fun u => polyCode u.1 ++ natCode u.2)

end LatticeAvgPrec.OneVector.Supplement


