-- Prove2me | Definitions.Def_LagrangeRank_Debias_Supplement_BTL
-- name    : LagrangeRank_Debias_Supplement_BTL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:45:45.609773+00:00
-- url     : https://prove2.me/theorems/6c9836df-ad37-4d96-adb4-ea5fd707252f
-- title:
--   BTL sampling, regularized MLE, realized bordered inverse, remainders and rate conditions
-- statement:
--   Let $n$ be the number of items, $L$ the number of repetitions, $p\in[0,1]$ the comparison probability, and $\theta\in\mathbb R^n$ the centered true log scores. Unordered pairs are indexed once, by $a<b$. Independently draw each graph edge with probability $p$, and independently draw all potential observations with
--   $$P(y_{ab}^{(\ell)}=1)=\frac{e^{\theta_b}}{e^{\theta_a}+e^{\theta_b}}.$$
--   Only observations on present edges enter the loss. Including unused potential observations changes no observed-data law. `Parameter κ θ` requires $\sum_i\theta_i=0$ and $e^{\theta_i-\theta_j}\le\kappa$ for every pair, a shift-invariant bounded dynamic range.
--
--   The averaged loss is $\mathcal L(u)=\sum_{a<b,\,ab\in\mathcal E}[-\bar y_{ab}(u_b-u_a)+\log(1+e^{u_b-u_a})]$. The estimator is an actual minimizer of $\mathcal L(u)+\lambda_0\sum_i u_i^2$, where $\lambda_0=c\sqrt{np\log n/L}$. With $c,p>0$, $n\ge2$ and $L>0$, this objective has a unique minimizer. The definition selects a minimizer; its zero fallback is outside that positive-regularization regime.
--
--   At $u$, take the actual inverse of $\left(\begin{smallmatrix}\nabla^2\mathcal L(u)&\mathbf1\\\mathbf1^T&0\end{smallmatrix}\right)$. The upper-left block at $\theta$ is $\Theta^*_{11}$, while the inverse at $\hat\theta$ gives $\hat\theta^d=\hat\theta-\hat\Theta_{11}\nabla\mathcal L(\hat\theta)$. The published unbundled gradient, Hessian, bordering, debiasing and row-sum norm are reused. The general inverse-estimation Assumptions structure is not imposed on BTL. On singular inputs Matrix.inv returns zero; its exceptional probability vanishes under the sufficiently large density threshold in the new unconditional positive results.
--
--   The file also defines both bordered remainders in (A.7), Euclidean operator norm, both exact scaling expressions of Theorems 3.2 and 3.3, and the signal scale $s=\sqrt{\log n/(npL)}$. `Regime` uses a separate sequence index, with $n,L\to\infty$, $n\ge2$, $L>0$, and $p>0$. `SourceBounds` records the source working event plus Lemma 3.1's initial-error bound used on p. 47. Its corrected (A.11) bounds the inverse on $(v,0)$ with $∑_i v_i=0$, not on the whole bordered Euclidean space. The corrected (A.11) also records invertibility, so the zero inverse cannot satisfy the intended nonsingular premise. The correction and its excluded cases are detailed in DISPROOF.md and MODERATION_NOTES.md.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, pp. 8–9, (2.1); pp. 12–13, (3.1)–(3.2); p. 18, (3.10); pp. 41–42, (A.7)–(A.12)

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}
abbrev Graph (n : ℕ) := Edge n → Bool
abbrev Outcomes (n L : ℕ) := Fin L × Edge n → Bool
abbrev Data (n L : ℕ) := Graph n × Outcomes n L

/-- Probability that the second item beats the first, (2.1). -/
noncomputable def winProb {n : ℕ} (θ : Vec n) (e : Edge n) : unitInterval :=
  ⟨Real.exp (θ e.val.2) / (Real.exp (θ e.val.1) + Real.exp (θ e.val.2)), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).2
      exact le_add_of_nonneg_left (le_of_lt (Real.exp_pos _))⟩

noncomputable def graphLaw (n : ℕ) (p : unitInterval) : Measure (Graph n) :=
  Measure.pi (fun _ => bernoulliMeasure true false p)
noncomputable def outcomeLaw {n : ℕ} (L : ℕ) (θ : Vec n) : Measure (Outcomes n L) :=
  Measure.pi (fun a => bernoulliMeasure true false (winProb θ a.2))
/-- Independent graph and potential comparisons. Unobserved potential outcomes are ignored. -/
noncomputable def dataLaw {n : ℕ} (L : ℕ) (p : unitInterval) (θ : Vec n) : Measure (Data n L) :=
  (graphLaw n p).prod (outcomeLaw L θ)
instance graphLaw_probability (n : ℕ) (p : unitInterval) : IsProbabilityMeasure (graphLaw n p) := by
  unfold graphLaw; infer_instance
instance outcomeLaw_probability {n : ℕ} (L : ℕ) (θ : Vec n) : IsProbabilityMeasure (outcomeLaw L θ) := by
  unfold outcomeLaw; infer_instance
instance dataLaw_probability {n : ℕ} (L : ℕ) (p : unitInterval) (θ : Vec n) :
    IsProbabilityMeasure (dataLaw L p θ) := by unfold dataLaw; infer_instance

/-- Centering preserves all comparison probabilities and the dynamic range. -/
noncomputable def center {n : ℕ} (θ : Vec n) : Vec n :=
  fun i => θ i - (∑ j, θ j) / n

def Parameter {n : ℕ} (κ : ℝ) (θ : Vec n) : Prop :=
  (∑ i, θ i) = 0 ∧ ∀ i j, Real.exp (θ i - θ j) ≤ κ

noncomputable def ybar {n L : ℕ} (y : Outcomes n L) (e : Edge n) : ℝ :=
  (∑ l : Fin L, if y (l,e) then (1 : ℝ) else 0) / L

/-- Averaged negative log likelihood (3.2), with each unoriented pair counted once. -/
noncomputable def loss {n L : ℕ} (s : Data n L) (θ : Vec n) : ℝ :=
  ∑ e : Edge n, if s.1 e then
    -(ybar s.2 e) * (θ e.val.2 - θ e.val.1) +
      Real.log (1 + Real.exp (θ e.val.2 - θ e.val.1)) else 0

noncomputable def lambda0 (n L : ℕ) (p : ℝ) (c : ℝ) : ℝ :=
  c * Real.sqrt ((n : ℝ) * p * Real.log n / L)
noncomputable def objective {n L : ℕ} (p c : ℝ) (s : Data n L) (θ : Vec n) : ℝ :=
  loss s θ + lambda0 n L p c * ∑ i, θ i ^ 2
/-- The actual regularized MLE (3.1), not an estimator postulated to have its rate.
The fallback is used only when a minimum does not exist; λ₀>0 ensures existence and uniqueness. -/
noncomputable def thetaHat {n L : ℕ} (p c : ℝ) (s : Data n L) : Vec n :=
  if h : ∃ θ, ∀ x, objective p c s θ ≤ objective p c s x then h.choose else 0

/-- Realized graph inverse (3.10); Matrix.inv is zero when its determinant is zero. -/
noncomputable def inverseAt {n L : ℕ} (s : Data n L) (θ : Vec n) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  (borderedHessian (hess (loss s) θ) (fun _ => 1))⁻¹
noncomputable def thetaD {n L : ℕ} (p c : ℝ) (s : Data n L) : Vec n :=
  debiased (thetaHat p c s) (inverseAt s (thetaHat p c s)) (grad (loss s) (thetaHat p c s))
noncomputable def trueBlock {n L : ℕ} (s : Data n L) (θ : Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  (inverseAt s θ).toBlocks₁₁
noncomputable def pairVar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  (Pi.single i 1 - Pi.single j 1 : Vec n) ⬝ᵥ (A *ᵥ (Pi.single i 1 - Pi.single j 1 : Vec n))

/-- Operator norm for Euclidean vectors. No ambient matrix norm instance is used. -/
noncomputable def spectralNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : ℝ :=
  ‖(Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ] (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)) A‖

/-- The two full bordered vectors in (A.7), including their last coordinates. -/
noncomputable def I1 {n L : ℕ} (p c : ℝ) (s : Data n L) (θ : Vec n) : Fin n ⊕ Unit → ℝ :=
  let th := thetaHat p c s
  (inverseAt s th - inverseAt s θ) *ᵥ
    Sum.elim (-grad (loss s) th + hess (loss s) th *ᵥ (th - θ)) (fun _ => 0)
noncomputable def I2 {n L : ℕ} (p c : ℝ) (s : Data n L) (θ : Vec n) : Fin n ⊕ Unit → ℝ :=
  let th := thetaHat p c s
  inverseAt s θ *ᵥ
    Sum.elim (grad (loss s) θ - grad (loss s) th + hess (loss s) th *ᵥ (th - θ)) (fun _ => 0)

/-- A.8–A.12 on the working event. A.11 is corrected to its action on zero-sum vectors (v,0).
The initial-estimator rate is the Lemma 3.1 event explicitly used in C.2, p. 47. -/
def SourceBounds {n L : ℕ} (p c K : ℝ) (s : Data n L) (θ : Vec n) : Prop :=
  let th := thetaHat p c s
  ‖th - θ‖ ≤ K * Real.sqrt (Real.log n / ((n : ℝ) * p * L)) ∧
  ‖grad (loss s) θ‖ ≤ K * n * p * Real.sqrt (Real.log n / L) ∧
  ‖grad (loss s) th - grad (loss s) θ - hess (loss s) θ *ᵥ (th - θ)‖ ≤
    K * Real.log n / L ∧
  rowSumNorm (hess (loss s) th - hess (loss s) θ) ≤
    K * n * p * Real.sqrt (Real.log n / ((n : ℝ) * p * L)) ∧
  IsUnit (borderedHessian (hess (loss s) θ) (fun _ => 1)).det ∧
  (∀ v : Vec n, (∑ i, v i) = 0 →
    ‖WithLp.toLp 2 (inverseAt s θ *ᵥ Sum.elim v (fun _ => 0))‖ ≤
    K / ((n : ℝ) * p) * ‖WithLp.toLp 2 v‖) ∧
  spectralNorm (inverseAt s th - inverseAt s θ) ≤
    K / ((n : ℝ) * p) * Real.sqrt (Real.log n / (p * L))

noncomputable def rate32 (n L : ℕ) (p : ℝ) : ℝ :=
  n * Real.log n / Real.sqrt L + Real.log n / Real.sqrt (p * L)
noncomputable def rate33a (n L : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ)^2 * p * Real.log ((n : ℝ) * L)^7 / L
noncomputable def rate33b (n L : ℕ) : ℝ :=
  n * Real.rpow (Real.log n) (3/2 : ℝ) / Real.sqrt L
noncomputable def signalScale (n L : ℕ) (p : ℝ) : ℝ :=
  Real.sqrt (Real.log n / ((n : ℝ) * p * L))

structure Regime (n L : ℕ → ℕ) (p : ℕ → unitInterval) : Prop where
  n_ge : ∀ t, 2 ≤ n t
  L_pos : ∀ t, 0 < L t
  p_pos : ∀ t, 0 < (p t : ℝ)
  n_inf : Tendsto n atTop atTop
  L_inf : Tendsto L atTop atTop

def Density (C0 : ℝ) (n : ℕ → ℕ) (p : ℕ → unitInterval) : Prop :=
  ∀ᶠ t in atTop, C0 * Real.log (n t) / n t ≤ (p t : ℝ)
def Rates32 (n L : ℕ → ℕ) (p : ℕ → unitInterval) : Prop :=
  Tendsto (fun t => rate32 (n t) (L t) (p t)) atTop (𝓝 0)
def Rates33 (n L : ℕ → ℕ) (p : ℕ → unitInterval) : Prop :=
  Tendsto (fun t => rate33a (n t) (L t) (p t)) atTop (𝓝 0) ∧
  Tendsto (fun t => rate33b (n t) (L t)) atTop (𝓝 0)

end LagrangeRank.Debias.Supplement


