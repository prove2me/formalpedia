-- Prove2me | Definitions.Def_DNNProj_DNN
-- name    : DNNProj_DNN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:32.636641+00:00
-- url     : https://prove2.me/theorems/27d6f0c8-ccd3-4076-ab30-dd42066c61c0
-- title:
--   The DNN projection problem (P), its dual (D), quadratic growth of (D), and the eigenvalue index sets (15)
-- statement:
--   Let $\mathbb S^n$ be the space of real symmetric $n\times n$ matrices with the Frobenius inner product, $\mathbb S^n_+$ ($\mathbb S^n_-$) the positive (negative) semidefinite cone, and $\mathbb N^n$ the symmetric matrices with nonnegative entries. For $G\in\mathbb S^n$, the DNN projection problem and its dual are
--   $$\text{(P)}\quad\min_{X\in\mathbb S^n}\Big\{\tfrac12\|X-G\|^2\ \Big|\ X\in\mathbb S^n_+,\ X\in\mathbb N^n\Big\},\qquad \text{(D)}\quad-\min_{S,Z\in\mathbb S^n}\Big\{\tfrac12\|S+Z+G\|^2-\tfrac12\|G\|^2\ \Big|\ S\in\mathbb S^n_+,\ Z\in\mathbb N^n\Big\}.$$
--   $\mathrm{SOL_P}$ is the set of minimizers of (P) and $\mathrm{SOL_D}$ the set of minimizers $(S,Z)$ of (D). The **quadratic growth condition of (D)** at $(\bar S,\bar Z)$ is Definition 4 for (D) seen as an instance of (9) with $h(U)=\tfrac12\|U+G\|^2$, $\mathcal F(S,Z)=S+Z$, $p(S,Z)=\delta_{\mathbb S^n_+}(S)+\delta_{\mathbb N^n}(Z)$: there are $\kappa,\varepsilon>0$ with
--   $$\tfrac12\|S+Z+G\|^2\ge\tfrac12\|\bar S+\bar Z+G\|^2+\kappa\operatorname{dist}^2\big((S,Z),\mathrm{SOL_D}\big)$$
--   for all $(S,Z)$ with $S\in\mathbb S^n_+$, $Z\in\mathbb N^n$ and $\|(S,Z)-(\bar S,\bar Z)\|\le\varepsilon$, the norm on $\mathbb S^n\times\mathbb S^n$ being $\|(S,Z)\|^2=\|S\|^2+\|Z\|^2$.
--
--   For $\bar X,\bar S\in\mathbb S^n$, let $\bar\lambda_1,\dots,\bar\lambda_n$ be the eigenvalues of $\bar Z=\bar X-\bar S$; the index sets (15) are $\alpha=\{i\mid\bar\lambda_i>0\}$, $\beta=\{i\mid\bar\lambda_i=0\}$, $\gamma=\{i\mid\bar\lambda_i<0\}$.
--
--   **Formalization Note** $\mathbb S^n$, $\mathbb S^n_\pm$ are the published `SunNLSDP.Equiv.SymMat (Fin n)`, `psdCone`, `nsdCone` (the symmetric subspace of `EuclideanSpace ℝ (Fin n × Fin n)`, whose inherited norm is the Frobenius norm). $\mathbb S^n\times\mathbb S^n$ is `WithLp 2 (Sⁿ × Sⁿ)`. The constant $-\tfrac12\|G\|^2$ and the outer sign of (D) do not change $\mathrm{SOL_D}$ or the growth inequality and are omitted from `dualObj`. Only the cardinalities $|\alpha|,|\beta|,|\gamma|$ are defined; the ordering of eigenvalues plays no role.
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, (P) and (D) p.2; DNN cone p.2; §3.2 p.11 ((D) as an instance of (9), index sets (15))

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace

namespace DNNProj

/-! # The DNN projection problem (P), its dual (D), and the index sets (15)

Y. Cui, L. Liang, D. Sun, K.-C. Toh, *On Degenerate Doubly Nonnegative Projection Problems*,
arXiv:2009.11272v2, §1, pp.1–2 ((P), (D)); §3.2, p.11 ((D) as an instance of (9), (15)).

**Formalization Note.**
* `Sⁿ` is the published `SunNLSDP.Equiv.SymMat (Fin n)`: the symmetric subspace of
  `EuclideanSpace ℝ (Fin n × Fin n)`, whose inherited inner product `∑ᵢⱼ MᵢⱼNᵢⱼ` and norm are the
  Frobenius ones. `Sⁿ₊`, `Sⁿ₋` are the published `psdCone`, `nsdCone`.
* `Nⁿ ∩ Sⁿ` is the set of symmetric matrices with nonnegative entries.
* `Sⁿ × Sⁿ` is `WithLp 2 (Sⁿ × Sⁿ)`, the Euclidean product, with
  `‖(S, Z)‖² = ‖S‖² + ‖Z‖²` and `⟨(S, Z), (S', Z')⟩ = ⟨S, S'⟩ + ⟨Z, Z'⟩`, as for the space `𝕏` of
  the instance of (9) on p.11. -/

noncomputable section

/-- `Sⁿ`: the `n × n` real symmetric matrices with the Frobenius inner product (p.1). -/
abbrev Sym (n : ℕ) : Type := SunNLSDP.Equiv.SymMat (Fin n)

/-- The underlying `n × n` matrix of a point of `Sⁿ`. -/
abbrev toMat {n : ℕ} (M : Sym n) : Matrix (Fin n) (Fin n) ℝ := SunNLSDP.Equiv.SymMat.toMat M

/-- `Sⁿ₊`, the positive semidefinite cone in `Sⁿ` (p.1). -/
abbrev psd (n : ℕ) : Set (Sym n) := SunNLSDP.Equiv.psdCone (Fin n)

/-- `Sⁿ₋ = −Sⁿ₊`, the negative semidefinite cone in `Sⁿ` (Proposition 8, p.11). -/
abbrev nsd (n : ℕ) : Set (Sym n) := SunNLSDP.Equiv.nsdCone (Fin n)

/-- `Nⁿ` inside `Sⁿ`: symmetric matrices with nonnegative entries (p.1, "the nonnegative orthant
in ℝⁿˣⁿ", used for `X, Z ∈ Sⁿ`). -/
def nonneg (n : ℕ) : Set (Sym n) := {M | ∀ i j, 0 ≤ toMat M i j}

/-- The underlying matrix of a point of `Sⁿ` is symmetric (a structural lemma). -/
theorem toMat_isHermitian {n : ℕ} (M : Sym n) : (toMat M).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, toMat, SunNLSDP.Equiv.SymMat.toMat]
  exact M.2 j i

/-- `SOL_P` of (P) (p.2): the minimizers of `½‖X − G‖²` over `X ∈ Sⁿ₊ ∩ Nⁿ`. -/
def solPrimal {n : ℕ} (G : Sym n) : Set (Sym n) :=
  {X | X ∈ psd n ∧ X ∈ nonneg n ∧
    ∀ X' ∈ psd n, X' ∈ nonneg n → ‖X - G‖ ^ 2 / 2 ≤ ‖X' - G‖ ^ 2 / 2}

/-- `Sⁿ × Sⁿ` with the Euclidean product norm. -/
abbrev SymPair (n : ℕ) : Type := WithLp 2 (Sym n × Sym n)

/-- The feasible set `{(S, Z) | S ∈ Sⁿ₊, Z ∈ Nⁿ}` of (D) (p.2). -/
def dualFeasible (n : ℕ) : Set (SymPair n) := {q | q.fst ∈ psd n ∧ q.snd ∈ nonneg n}

/-- The objective of (D) as an instance of (9) (p.11): `θ(S, Z) = h(ℱ(S, Z)) = ½‖S + Z + G‖²` on the
feasible set (where `p = δ_{Sⁿ₊}(S) + δ_{Nⁿ}(Z) = 0`). (D) itself is
`−minimize {½‖S + Z + G‖² − ½‖G‖²}`; the constant `−½‖G‖²` and the outer sign do not change the
solution set or the growth inequality. -/
def dualObj {n : ℕ} (G : Sym n) (q : SymPair n) : ℝ := ‖q.fst + q.snd + G‖ ^ 2 / 2

/-- `SOL_D` of (D) (p.2): the feasible `(S, Z)` minimizing `½‖S + Z + G‖²`. -/
def solDual {n : ℕ} (G : Sym n) : Set (SymPair n) :=
  {q | q ∈ dualFeasible n ∧ ∀ q' ∈ dualFeasible n, dualObj G q ≤ dualObj G q'}

/-- The quadratic growth condition of (D) at `(S̄, Z̄)` (Definition 4, p.9, for the instance of (9)
on p.11): there are `κ > 0`, `ε > 0` with
`½‖S + Z + G‖² ≥ ½‖S̄ + Z̄ + G‖² + κ dist²((S, Z), SOL_D)` for all feasible `(S, Z)` in the closed
ball of radius `ε` around `(S̄, Z̄)` in `Sⁿ × Sⁿ`. -/
def DualQuadGrowthAt {n : ℕ} (G : Sym n) (qbar : SymPair n) : Prop :=
  ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ∀ q ∈ Metric.closedBall qbar ε, q ∈ dualFeasible n →
    dualObj G qbar + κ * Metric.infDist q (solDual G) ^ 2 ≤ dualObj G q

/-- The eigenvalues `λ̄₁, …, λ̄ₙ` of `Z̄ ≜ X̄ − S̄` (p.11); their order plays no role below. -/
def eigZ {n : ℕ} (Xbar Sbar : Sym n) : Fin n → ℝ := (toMat_isHermitian (Xbar - Sbar)).eigenvalues

/-- `|α|` of (15) (p.11): the number of `i` with `λ̄ᵢ > 0`. -/
def cardAlpha {n : ℕ} (Xbar Sbar : Sym n) : ℕ :=
  (Finset.univ.filter fun i => 0 < eigZ Xbar Sbar i).card

/-- `|β|` of (15) (p.11): the number of `i` with `λ̄ᵢ = 0`. -/
def cardBeta {n : ℕ} (Xbar Sbar : Sym n) : ℕ :=
  (Finset.univ.filter fun i => eigZ Xbar Sbar i = 0).card

/-- `|γ|` of (15) (p.11): the number of `i` with `λ̄ᵢ < 0`. -/
def cardGamma {n : ℕ} (Xbar Sbar : Sym n) : ℕ :=
  (Finset.univ.filter fun i => eigZ Xbar Sbar i < 0).card

end

end DNNProj


