-- Prove2me | Definitions.Def_OfflinePolicyLearning_Regret_Setting
-- name    : OfflinePolicyLearning_Regret_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:14.527274+00:00
-- url     : https://prove2.me/theorems/f6b9fd73-8f95-4621-ab10-f2239c6aab47
-- title:
--   §2–§5, pp. 8–21 — potential-outcome model, e_a, μ_a, Q, regret, oracle score Γ_i, V*, cross-fitted AIPW score (5), Q̂, Q̃, Δ, Δ̃, Δ̂, inner product distance
-- statement:
--   The objects of the offline multi-action policy learning problem and of the cross-fitted AIPW learner.
--
--   **Data.** Actions are $1,\dots,d$ (the paper's $a^1,\dots,a^d$, identified with the standard basis vectors $e_1,\dots,e_d$ of $\mathbb R^d$; so for $\gamma\in\mathbb R^d$ the inner product $\langle\pi(x),\gamma\rangle$ is the coordinate $\gamma_{\pi(x)}$). One draw is $\omega=(X,(Y(1),\dots,Y(d)),A)$: features $X\in\mathcal X$, the potential-outcome vector, and the logged action $A$. The observed triple is $(X,A,Y)$ with $Y=Y(A)$.
--
--   **Model.** A probability measure $P_X$ on $\mathcal X$, a Markov kernel $\kappa_Y(x,\cdot)$ (law of the outcome vector given $X=x$) and a Markov kernel $\kappa_A(x,\cdot)$ (law of the action given $X=x$). The joint law of one draw is $P_X\otimes(\kappa_Y\times\kappa_A)$: given $X$, outcomes and action are independent. The sample of size $n$ is $n$ independent draws $D=(\omega_1,\dots,\omega_n)$.
--
--   1. Propensity and mean reward (Definition 1): $e_a(x)=\kappa_A(x,\{a\})$, $\mu_a(x)=\int y_a\,\kappa_Y(x,dy)$.
--   2. Value (Definition 2): $Q(\pi)=\mathbb E[Y(\pi(X))]$; value difference (Definition 7): $\Delta(\pi_1,\pi_2)=Q(\pi_1)-Q(\pi_2)$.
--   3. Regret (Definition 3): $R(\pi)=\sup_{\pi'\in\Pi}Q(\pi')-Q(\pi)$.
--   4. Oracle score (§4): for an observed $(x,a,y)$, $\Gamma_j=\mu_j(x)+\mathbf 1\{a=j\}\,\dfrac{y-\mu_a(x)}{e_a(x)}$.
--   5. $V_*=\sup_{\pi_a,\pi_b\in\Pi}\mathbb E\big[(\Gamma_{\pi_a(X)}-\Gamma_{\pi_b(X)})^2\big]$ (Remark 6).
--   6. Oracle estimate (§4): $\tilde Q(\pi)=\frac1n\sum_{i=1}^n\Gamma_{i,\pi(X_i)}$, $\tilde\Delta(\pi_1,\pi_2)=\tilde Q(\pi_1)-\tilde Q(\pi_2)$.
--   7. **Cross-fitting** with $K$ folds: for each $n$ a fold map $k:\{1,\dots,n\}\to\{1,\dots,K\}$, and for each fold $k$ estimators $\hat\mu^{-k}_a(x)$, $\hat e^{-k}_a(x)$ that are functions of the observed triples outside fold $k$ only.
--   8. The cross-fitted AIPW score (5):
--   $$\hat\Gamma_{i,j}=\hat\mu^{-k(i)}_j(X_i)+\mathbf 1\{A_i=j\}\,\frac{Y_i-\hat\mu^{-k(i)}_{A_i}(X_i)}{\hat e^{-k(i)}_{A_i}(X_i)},$$
--   $\hat Q_{CAIPWL}(\pi)=\frac1n\sum_i\hat\Gamma_{i,\pi(X_i)}$ and $\hat\Delta(\pi_1,\pi_2)=\hat Q_{CAIPWL}(\pi_1)-\hat Q_{CAIPWL}(\pi_2)$ (Definition 8).
--   9. The mean-squared errors of Assumption 2 at sample size $n$: $\mathbb E\big[(\hat\mu^{-k}_a(X)-\mu_a(X))^2\big]$ and $\mathbb E\big[(\hat e^{-k}_a(X)-e_a(X))^2\big]$, the expectation taken over the training data of fold $k$ and an independent $X\sim P_X$.
--   10. Inner product distance (Definition 6): for points $x_1,\dots,x_n$ and weights $\gamma_1,\dots,\gamma_n\in\mathbb R^d$,
--   $$I_\Gamma(\pi_1,\pi_2)=\sqrt{\frac{\sum_i(\gamma_{i,\pi_1(x_i)}-\gamma_{i,\pi_2(x_i)})^2}{\sup_{\pi_a,\pi_b\in\Pi}\sum_i(\gamma_{i,\pi_a(x_i)}-\gamma_{i,\pi_b(x_i)})^2}},\qquad \tfrac00:=0.$$
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Unconfoundedness (Assumption 1.1) is built into the joint law: $Y\perp A\mid X$ is exactly the statement that the conditional law of $(Y,A)$ given $X$ is a product, which is the disintegration used here. Policies are deterministic (endnote 3, p. 45). $\pi^*=\arg\max_{\pi\in\Pi}Q(\pi)$ need not exist, so the regret uses $\sup_{\pi'\in\Pi}Q(\pi')$; it equals $Q(\pi^*)-Q(\pi)$ whenever $\pi^*$ exists. The supremum is over the subtype $\Pi$; under bounded rewards it is a supremum of a bounded family. Lean's division by $0$ returns $0$, which is the paper's convention $0/0=0$ in $I_\Gamma$ and makes $\tilde Q,\hat Q$ equal $0$ at $n=0$. The estimators of fold $k$ take the observed triples indexed by $\{i: k(i)\neq k\}$ as their argument, so they cannot depend on fold $k$ (cross-fitting), and they never see unobserved potential outcomes.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, pp. 8–10, §2, Definitions 1–3; pp. 11–14, §3, (5), Algorithm 1; p. 14, §4 (Q̃, Γ_i); p. 15, Definition 6; p. 18, Remark 6 (V*); p. 19, Definition 7; p. 21, Definition 8; p. 12, Assumption 2 (3)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace OfflinePolicyLearning.Regret

/-- One full draw `ω = (x, (y, a))`: the features `x`, the potential-outcome vector
`y = (Y(a¹), …, Y(a^d))` and the logged action `a` (§2, p. 8; actions are `Fin d`). -/
abbrev Draw (X : Type*) (d : ℕ) := X × ((Fin d → ℝ) × Fin d)

/-- An observed triple `(X_i, A_i, Y_i)` (§2, p. 8). -/
abbrev Obs (X : Type*) (d : ℕ) := X × Fin d × ℝ

/-- The observed triple of a draw: `Y_i = Y_i(A_i)` (§2, p. 8). -/
def obs {X : Type*} {d : ℕ} (ω : Draw X d) : Obs X d := (ω.1, ω.2.2, ω.2.1 ω.2.2)

/-- Definition 6, item 1 (p. 15): the inner product distance between two policies on the points
`x` with weights `γ`, `I_Γ(π₁, π₂) = √(∑_i |⟨γ_i, π₁(x_i) − π₂(x_i)⟩|² / sup_{πa,πb ∈ Π} ∑_i
|⟨γ_i, πa(x_i) − πb(x_i)⟩|²)`, with `0/0 = 0`. -/
noncomputable def innerProdDist {X : Type*} {d n : ℕ} (Pol : Set (X → Fin d)) (x : Fin n → X)
    (γ : Fin n → Fin d → ℝ) (π₁ π₂ : X → Fin d) : ℝ :=
  Real.sqrt ((∑ i, (γ i (π₁ (x i)) - γ i (π₂ (x i))) ^ 2) /
    ⨆ πa : Pol, ⨆ πb : Pol, ∑ i, (γ i (πa.1 (x i)) - γ i (πb.1 (x i))) ^ 2)

/-- The data-generating model of §2: the feature law `PX`, the conditional law `κY` of the
potential-outcome vector given the features, and the conditional law `κA` of the logged action
given the features. -/
structure Model (X : Type*) [MeasurableSpace X] (d : ℕ) where
  PX : Measure X
  κY : Kernel X (Fin d → ℝ)
  κA : Kernel X (Fin d)
  [isProb : IsProbabilityMeasure PX]
  [markovY : IsMarkovKernel κY]
  [markovA : IsMarkovKernel κA]

attribute [instance] Model.isProb Model.markovY Model.markovA

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

namespace Model

/-- The joint law of one draw `(X, (Y(a¹), …, Y(a^d)), A)`: given `X`, the outcome vector and
the action are drawn independently (Assumption 1.1, unconfoundedness, built into the law). -/
noncomputable def law (M : Model X d) : Measure (Draw X d) := M.PX ⊗ₘ (M.κY ×ₖ M.κA)

/-- Definition 1: the propensity `e_a(x) = P[A_i = a | X_i = x]`. -/
noncomputable def e (M : Model X d) (x : X) (a : Fin d) : ℝ := (M.κA x {a}).toReal

/-- Definition 1: the mean reward `μ_a(x) = E[Y_i(a) | X_i = x]`. -/
noncomputable def μ (M : Model X d) (x : X) (a : Fin d) : ℝ := ∫ y, y a ∂(M.κY x)

/-- Definition 2: the policy value `Q(π) = E[Y(π(X))]`. -/
noncomputable def Q (M : Model X d) (π : X → Fin d) : ℝ := ∫ ω, ω.2.1 (π ω.1) ∂M.law

/-- Definition 3: the regret `R(π) = sup_{π' ∈ Π} Q(π') − Q(π)` (the best value in `Pol`). -/
noncomputable def regret (M : Model X d) (Pol : Set (X → Fin d)) (π : X → Fin d) : ℝ :=
  (⨆ π' : Pol, M.Q π'.1) - M.Q π

/-- Definition 7: the policy value difference `Δ(π₁, π₂) = Q(π₁) − Q(π₂)`. -/
noncomputable def Δ (M : Model X d) (π₁ π₂ : X → Fin d) : ℝ := M.Q π₁ - M.Q π₂

/-- §4, p. 14: the `j`-th coordinate of the oracle AIPW score `Γ_i` of the observed triple
`o = (x, a, y)`: `Γ_j = μ_j(x) + 1{a = j} (y − μ_a(x)) / e_a(x)`. -/
noncomputable def Γ (M : Model X d) (o : Obs X d) (j : Fin d) : ℝ :=
  M.μ o.1 j + if o.2.1 = j then (o.2.2 - M.μ o.1 o.2.1) / M.e o.1 o.2.1 else 0

/-- Remark 6: `V* = sup_{πa, πb ∈ Π} E[⟨Γ_i, πa(X_i) − πb(X_i)⟩²]`. -/
noncomputable def Vstar (M : Model X d) (Pol : Set (X → Fin d)) : ℝ :=
  ⨆ πa : Pol, ⨆ πb : Pol,
    ∫ ω, (M.Γ (obs ω) (πa.1 ω.1) - M.Γ (obs ω) (πb.1 ω.1)) ^ 2 ∂M.law

/-- The law of `n` iid draws. -/
noncomputable def sample (M : Model X d) (n : ℕ) : Measure (Fin n → Draw X d) :=
  Measure.pi fun _ : Fin n => M.law

/-- §4, p. 14: the oracle value estimate `Q̃(π) = (1/n) ∑_i ⟨π(X_i), Γ_i⟩`. -/
noncomputable def Qtilde (M : Model X d) {n : ℕ} (D : Fin n → Draw X d) (π : X → Fin d) : ℝ :=
  (1 / n : ℝ) * ∑ i, M.Γ (obs (D i)) (π (D i).1)

/-- Definition 7: `Δ̃(π₁, π₂) = Q̃(π₁) − Q̃(π₂)`. -/
noncomputable def Δtilde (M : Model X d) {n : ℕ} (D : Fin n → Draw X d)
    (π₁ π₂ : X → Fin d) : ℝ :=
  M.Qtilde D π₁ - M.Qtilde D π₂

end Model

/-- Cross-fitting with `K` folds (§3, p. 11; Algorithm 1, p. 14): for each sample size `n` a fold
assignment, and for each fold `k` the estimators `μ̂^{-k}` and `ê^{-k}`, which are functions of the
observed data **outside fold `k` only** and then of a feature point and an action. -/
structure CrossFit (X : Type*) (d K : ℕ) where
  fold : (n : ℕ) → Fin n → Fin K
  μhat : (n : ℕ) → (k : Fin K) → ({i : Fin n // fold n i ≠ k} → Obs X d) → X → Fin d → ℝ
  ehat : (n : ℕ) → (k : Fin K) → ({i : Fin n // fold n i ≠ k} → Obs X d) → X → Fin d → ℝ

namespace CrossFit

variable {K : ℕ}

/-- The training data of fold `k`: the observed triples of the points outside fold `k`. -/
def trainData (C : CrossFit X d K) {n : ℕ} (D : Fin n → Draw X d) (k : Fin K) :
    {i : Fin n // C.fold n i ≠ k} → Obs X d :=
  fun i => obs (D i.1)

/-- `μ̂^{-k(i)}_j(X_i)`: the outcome regression of the fold of point `i`, at `X_i`. -/
noncomputable def μhatAt (C : CrossFit X d K) {n : ℕ} (D : Fin n → Draw X d) (i : Fin n)
    (j : Fin d) : ℝ :=
  C.μhat n (C.fold n i) (C.trainData D (C.fold n i)) (D i).1 j

/-- `ê^{-k(i)}_j(X_i)`: the propensity estimate of the fold of point `i`, at `X_i`. -/
noncomputable def ehatAt (C : CrossFit X d K) {n : ℕ} (D : Fin n → Draw X d) (i : Fin n)
    (j : Fin d) : ℝ :=
  C.ehat n (C.fold n i) (C.trainData D (C.fold n i)) (D i).1 j

/-- (5), p. 13: the `j`-th coordinate of the cross-fitted AIPW score
`Γ̂_i = (Y_i − μ̂^{-k(i)}_{A_i}(X_i)) / ê^{-k(i)}_{A_i}(X_i) · A_i + (μ̂^{-k(i)}_{a¹}(X_i), …, μ̂^{-k(i)}_{a^d}(X_i))`. -/
noncomputable def GammaHat (C : CrossFit X d K) {n : ℕ} (D : Fin n → Draw X d) (i : Fin n)
    (j : Fin d) : ℝ :=
  C.μhatAt D i j +
    if (obs (D i)).2.1 = j then
      ((obs (D i)).2.2 - C.μhatAt D i (obs (D i)).2.1) / C.ehatAt D i (obs (D i)).2.1
    else 0

/-- §3, p. 13: `Q̂_CAIPWL(π) = (1/n) ∑_i ⟨π(X_i), Γ̂_i⟩`. -/
noncomputable def Qhat (C : CrossFit X d K) {n : ℕ} (D : Fin n → Draw X d) (π : X → Fin d) : ℝ :=
  (1 / n : ℝ) * ∑ i, C.GammaHat D i (π (D i).1)

/-- Definition 8: `Δ̂(π₁, π₂) = Q̂_CAIPWL(π₁) − Q̂_CAIPWL(π₂)`. -/
noncomputable def Δhat (C : CrossFit X d K) {n : ℕ} (D : Fin n → Draw X d)
    (π₁ π₂ : X → Fin d) : ℝ :=
  C.Qhat D π₁ - C.Qhat D π₂

/-- Mean-squared error of `μ̂^{-k}_a` at sample size `n`: training data drawn from the sample
law, evaluated at an independent fresh feature `X ∼ P_X` (Assumption 2, p. 12). -/
noncomputable def mseMu (M : Model X d) (C : CrossFit X d K) (n : ℕ) (k : Fin K) (a : Fin d) : ℝ :=
  ∫ D, ∫ x, (C.μhat n k (C.trainData D k) x a - M.μ x a) ^ 2 ∂M.PX ∂M.sample n

/-- Mean-squared error of `ê^{-k}_a` at sample size `n` (Assumption 2, p. 12). -/
noncomputable def mseE (M : Model X d) (C : CrossFit X d K) (n : ℕ) (k : Fin K) (a : Fin d) : ℝ :=
  ∫ D, ∫ x, (C.ehat n k (C.trainData D k) x a - M.e x a) ^ 2 ∂M.PX ∂M.sample n

end CrossFit

end OfflinePolicyLearning.Regret


