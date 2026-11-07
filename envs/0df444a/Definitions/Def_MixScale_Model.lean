-- Prove2me | Definitions.Def_MixScale_Model
-- name    : MixScale_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:09:35.539647+00:00
-- url     : https://prove2.me/theorems/1fdeaf0f-5d85-4b05-85c5-42c6f77c66e5
-- title:
--   The mixture model (1)–(2), the loss $D_{\mathrm{par}}$ (3) and legal outputs
-- statement:
--   A $k$-component parameter tuple on $\mathbb R^d$ is $\Theta=(\mu_j,\Sigma_j,w_j)_{j}$. A component with center $\mu$ and scale matrix $\Sigma$ has characteristic function
--
--   $$\phi_{\mu,\Sigma}(t)=e^{it^\top\mu}\chi\big(\sqrt{t^\top\Sigma t}\big),$$
--
--   and the mixture is $P_\Theta=\sum_jw_jP_{\mu_j,\Sigma_j}$. Condition (2) with bounds $B,\kappa,w_\star,\gamma$ says
--
--   $$\sum_jw_j=1,\quad w_j\ge w_\star,\quad\|\mu_j\|_2\le B,\quad\kappa^{-1}I\preceq\Sigma_j\preceq\kappa I,\quad\|\mu_j-\mu_\ell\|_2\ge\gamma\ (j\ne\ell).$$
--
--   The equal-weight class adds $w_j=1/k$. The loss (3) is
--
--   $$D_{\mathrm{par}}(\Theta,\Theta')=\min_{\pi}\max_j\max\{\|\mu_j-\mu'_{\pi(j)}\|_2,\ \|\Sigma_j-\Sigma'_{\pi(j)}\|_F,\ k|w_j-w'_{\pi(j)}|\}.$$
--
--   A **legal** output has nonnegative weights summing to one and scale matrices in the interval $[\kappa^{-1},\kappa]$; its centers are unconstrained.
--
--   **Formalization Note** A component law is any probability measure with characteristic function (1) (`IsCompLaw`); it is unique, by the uniqueness of characteristic functions. Components are indexed by `Fin k` from zero. Symmetry of $\Sigma_j$ is written explicitly. The Frobenius norm is the published `DDROCS.frobNorm`.
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), §1.1, (1)–(3), p.2 (PDF p.4)

import Mathlib
import Definitions.Def_DDROCS_frobNorm

open MeasureTheory

namespace MixScale

/-!
# The mixture model, condition (2), the parameter loss `D_par`, and legal outputs

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c), §1.1, (1)–(3), p.2 (PDF p.4).

"A component with center `μ ∈ ℝ^d` and positive definite scale matrix `Σ` has characteristic
function `φ_{μ,Σ}(t) = e^{it⊤μ} χ(√(t⊤Σt))`. (1) We observe i.i.d. samples from the `k`-component
mixture `P_Θ = Σ_j w_j P_{μ_j,Σ_j}` […] The learner is given `d`, `k` and valid condition bounds
`B, κ ≥ 1`, `0 < w★ ≤ 1/k`, and `0 < γ ≤ 1`, such that `Σ_j w_j = 1`, `w_j ≥ w★`, `‖μ_j‖₂ ≤ B`,
`κ⁻¹I ⪯ Σ_j ⪯ κI`, `‖μ_j − μ_ℓ‖₂ ≥ γ (j ≠ ℓ)`. (2) […] `D_par(Θ, Θ′) = min_{π∈S_k} max_{j∈[k]}
max{‖μ_j − μ′_{π(j)}‖₂, ‖Σ_j − Σ′_{π(j)}‖_F, k|w_j − w′_{π(j)}|}`. (3) […] The output must be a valid
mixture with nonnegative normalized weights and scale matrices in the prescribed eigenvalue
interval".

**Formalization Note.**
* A parameter tuple `Θ : Params d k` lists, for each component `j : Fin k` (0-based), its center in
  `EuclideanSpace ℝ (Fin d)`, its scale matrix and its weight.
* The Loewner bounds `κ⁻¹I ⪯ Σ ⪯ κI` are `(Σ − κ⁻¹ • 1).PosSemidef ∧ (κ • 1 − Σ).PosSemidef`;
  symmetry of `Σ` is stated explicitly as well (it is also implied).
* `D_par` takes the real `⨅` over the finite nonempty group of permutations and the real `⨆` over
  the components, so both are a minimum and a maximum (for `k = 0` the inner `⨆` is `0`). The
  Frobenius norm is the published `DDROCS.frobNorm`.
* A component law is any probability measure with characteristic function (1) (`IsCompLaw`); it is
  unique by `Measure.ext_of_charFun`. The quadratic form `t⊤Σt` is written as a double sum. The
  mixture law is `Σ_j w_j • P_j` (`ENNReal.ofReal w_j`).
-/

/-- Points of `ℝ^d`. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A `k`-component parameter tuple in dimension `d`: center, scale matrix and weight of each
component `j : Fin k`. -/
abbrev Params (d k : ℕ) := Fin k → Vec d × Matrix (Fin d) (Fin d) ℝ × ℝ

/-- The center `μ_j`. -/
def center {d k : ℕ} (Θ : Params d k) (j : Fin k) : Vec d := (Θ j).1

/-- The scale matrix `Σ_j`. -/
def scale {d k : ℕ} (Θ : Params d k) (j : Fin k) : Matrix (Fin d) (Fin d) ℝ := (Θ j).2.1

/-- The weight `w_j`. -/
def weight {d k : ℕ} (Θ : Params d k) (j : Fin k) : ℝ := (Θ j).2.2

/-- The quadratic form `t⊤ A t = Σ_a Σ_b t_a A_{ab} t_b`. -/
noncomputable def quadForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (t : Vec d) : ℝ :=
  ∑ a, ∑ b, t a * A a b * t b

/-- `A` is symmetric and `κ⁻¹ I ⪯ A ⪯ κ I` in the Loewner order. -/
def InScaleInterval {d : ℕ} (κ : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  A.IsSymm ∧ (A - κ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
    (κ • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef

/-- Condition (2), p.2: weights sum to one and are at least `w★`, centers have norm at most `B`,
scale matrices lie in `[κ⁻¹I, κI]`, and distinct centers are at distance at least `γ`. -/
def Valid {d k : ℕ} (B κ wstar γ : ℝ) (Θ : Params d k) : Prop :=
  (∑ j, weight Θ j = 1) ∧ (∀ j, wstar ≤ weight Θ j) ∧ (∀ j, ‖center Θ j‖ ≤ B) ∧
    (∀ j, InScaleInterval κ (scale Θ j)) ∧
    (∀ j l, j ≠ l → γ ≤ ‖center Θ j - center Θ l‖)

/-- The equal-weight class: `w_j = 1/k` for every `j`. -/
def EqualWeights {d k : ℕ} (Θ : Params d k) : Prop := ∀ j, weight Θ j = 1 / (k : ℝ)

/-- A legal output (p.2): nonnegative weights summing to one, and scale matrices in the prescribed
eigenvalue interval `[κ⁻¹, κ]`. Centers are unconstrained. -/
def IsLegal {d k : ℕ} (κ : ℝ) (Θ : Params d k) : Prop :=
  (∀ j, 0 ≤ weight Θ j) ∧ (∑ j, weight Θ j = 1) ∧ ∀ j, InScaleInterval κ (scale Θ j)

/-- The parameter loss (3), p.2: `min_π max_j max{‖μ_j − μ′_{π j}‖₂, ‖Σ_j − Σ′_{π j}‖_F,
k |w_j − w′_{π j}|}`. -/
noncomputable def Dpar {d k : ℕ} (Θ Θ' : Params d k) : ℝ :=
  ⨅ π : Equiv.Perm (Fin k), ⨆ j : Fin k,
    max ‖center Θ j - center Θ' (π j)‖
      (max (DDROCS.frobNorm (scale Θ j - scale Θ' (π j)))
        ((k : ℝ) * |weight Θ j - weight Θ' (π j)|))

/-- (1), p.2: `P` is a probability measure on `ℝ^d` with characteristic function
`t ↦ e^{i t⊤μ} χ(√(t⊤Σt))`. -/
def IsCompLaw {d : ℕ} (χ : ℝ → ℝ) (μ : Vec d) (Sig : Matrix (Fin d) (Fin d) ℝ)
    (P : Measure (Vec d)) : Prop :=
  IsProbabilityMeasure P ∧
    ∀ t : Vec d, charFun P t =
      Complex.exp ((inner ℝ t μ : ℝ) * Complex.I) * (χ (Real.sqrt (quadForm Sig t)) : ℂ)

/-- Every component of `Θ` has law `P j` in the sense of (1). -/
def IsCompFamily {d k : ℕ} (χ : ℝ → ℝ) (Θ : Params d k) (P : Fin k → Measure (Vec d)) : Prop :=
  ∀ j, IsCompLaw χ (center Θ j) (scale Θ j) (P j)

/-- The mixture law `P_Θ = Σ_j w_j P_j`. -/
noncomputable def mixLaw {d k : ℕ} (Θ : Params d k) (P : Fin k → Measure (Vec d)) :
    Measure (Vec d) :=
  ∑ j, ENNReal.ofReal (weight Θ j) • P j

/-- Projection of `x` onto the interval `[lo, hi]` (for `lo ≤ hi`). -/
def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

end MixScale


