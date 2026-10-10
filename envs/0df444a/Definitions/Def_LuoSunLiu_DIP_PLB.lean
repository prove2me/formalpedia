-- Prove2me | Definitions.Def_LuoSunLiu_DIP_PLB
-- name    : LuoSunLiu_DIP_PLB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:08.524629+00:00
-- url     : https://prove2.me/theorems/8f225e2f-4bec-43f9-a250-cd5cd53f2c6a
-- title:
--   p. 14, pp. 16–17, p. 20 — perturbed linear bandit, Conditions 1–4, M-LinUCB (Algorithm 5), β̃_t, shadow parameter ξ̇_t
-- statement:
--   This file defines the **perturbed linear bandit** (PLB) of Luo, Sun and Liu and the algorithm M-LinUCB.
--
--   Fix a dimension $d$ and a filtration $(\mathcal F_t)$. At each period $t \ge 1$ there is a finite action set $\mathcal A_t \subset \mathbb R^d$, a linear parameter $\xi_t \in \mathbb R^d$, a selected action $A_t \in \mathcal A_t$ and a reward
--   $$Z_t = \langle \xi_t, A_t\rangle + \eta_t .$$
--
--   1. **PLB model with variance proxy $\sigma^2$**: $A_t \in \mathcal A_t$, the reward identity holds, $A_t$ is $\mathcal F_{t-1}$-measurable, $\eta_t$ is $\mathcal F_t$-measurable, and $\eta_t$ is conditionally $\sigma^2$-sub-Gaussian: $\mathbb E[e^{\alpha\eta_t}\mid\mathcal F_{t-1}] \le e^{\sigma^2\alpha^2/2}$ for all $\alpha$.
--   2. **Perturbation constant $C_p$**: $\|\xi_s - \xi_t\|_\infty \le C_p$ for all $s, t \ge 1$.
--   3. **Conditions 1–3** (p. 20): $|\langle\xi_t, a\rangle| \le 1$ for $a \in \mathcal A_t$; $\|\xi_t\|_\infty \le C_1$; every $a \in \mathcal A_t$ has exactly one nonzero entry, with index $\delta(a)$, and $\|a\|_2 \le a_{\max}$. Condition 4 is the PLB model with $\sigma^2 = 1$.
--   4. The **PLB regret** $R^{PLB}_{T_0} = \sum_{t=1}^{T_0} \langle \xi_t, A^*_t - A_t\rangle$, where $A^*_t \in \arg\max_{a\in\mathcal A_t}\langle\xi_t, a\rangle$.
--   5. The confidence parameter of Lemma 3:
--   $$\tilde\beta_t = 1 \vee \Bigl(C_1\sqrt{\lambda d} + \sqrt{2\log(1/\delta) + d\log\tfrac{d\lambda + (t-1)a_{\max}^2}{d\lambda}}\Bigr)^2 .$$
--   6. **LinUCB** (Algorithm 5, line 8). With $V_{t-1}(\lambda) = \lambda I + \sum_{s=1}^{t-1} A_sA_s^\top$ and the ridge estimate $\hat\xi_{t-1} = V_{t-1}(\lambda)^{-1}\sum_{s=1}^{t-1} A_sZ_s$,
--   $$\mathrm{LinUCB}_t(a) = \langle\hat\xi_{t-1}, a\rangle + \sqrt{\beta_t}\,\|a\|_{V_{t-1}(\lambda)^{-1}},$$
--   which is $\max_{\xi\in\mathcal C_t(\beta_t)}\langle\xi, a\rangle$ over the ellipsoid $\mathcal C_t(\beta_t) = \{\xi : \|\xi - \hat\xi_{t-1}\|^2_{V_{t-1}(\lambda)} \le \beta_t\}$.
--   7. A **run of M-LinUCB** up to $T_0$ on a sample path: for each $t \le T_0$, with $\tilde{\mathcal B}_t = \{\delta(a) : a \in \mathcal A_t\}$ and $\tilde{\mathcal B}'_t = \{\delta(A_s) : s \le t-1\}$, if $\tilde{\mathcal B}_t \not\subseteq \tilde{\mathcal B}'_t$ then $\delta(A_t) \notin \tilde{\mathcal B}'_t$; otherwise $A_t$ maximizes $\mathrm{LinUCB}_t$ over $\mathcal A_t$. Every tie-breaking rule is allowed.
--   8. The **shadow parameter** $\dot\xi_t = V_{t-1}^+\sum_{s=1}^{t-1}A_sA_s^\top\xi_s$ of Lemma S3, in coordinates $(\dot\xi_t)_i = \sum_{s<t} A_{s,i}^2\xi_{s,i} / \sum_{s<t}A_{s,i}^2$.
--
--   The PLB framework is the paper's device for analysing the UCB step of its pricing policy; Lemma 3 bounds the regret of M-LinUCB on any PLB.
--
--   **Formalization Note** $V_t(\lambda)$ and $\hat\xi_t$ are the published `BanditAlgorithm.regularizedDesignMatrix` and `BanditAlgorithm.regularizedLeastSquares` (definition `SelfNormalizedProcess`), used at index $t-1$. LinUCB is given in closed form, which avoids a real supremum; Lemma 2 (a) of this mission states that it equals the maximum over the ellipsoid. Conditional sub-Gaussianity is Mathlib's `HasCondSubgaussianMGF`, which requires a standard Borel sample space. The index $\delta(a)$ is encoded through the set of nonzero entries of $a$. The shadow parameter's coordinate formula equals the Moore–Penrose expression when every $A_s$ has one nonzero entry; Lean's $0/0 = 0$ gives the Moore–Penrose value $0$ on coordinates never pulled. The maximum $\max_{a \in \mathcal A_t}$ is taken as $0$ on an empty set, which never occurs because $A_t \in \mathcal A_t$. Indices $j \in [d]$ are Lean's `Fin d`, 0-based.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 14 (PLB), pp. 16–17 (δ(a), ℬ̃_t, ℬ̃′_t, Algorithm 5), p. 20 (Conditions 1–4, β̃_t), p. 39 (Lemma S3, ξ̇_t), p. 42 (R^{PLB})

import Mathlib
import Definitions.Def_SelfNormalizedProcess

open MeasureTheory ProbabilityTheory Matrix NNReal

namespace LuoSunLiu.DIP

/-- The set of indices of the nonzero entries of `a`. For a vector with exactly one nonzero entry
it is the singleton `{δ(a)}` of Luo, Sun and Liu (arXiv:2109.07340v2, p. 16). -/
noncomputable def supp {d : ℕ} (a : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter (fun i => a i ≠ 0)

/-- `‖a‖₀ = 1`: the vector `a` has exactly one nonzero entry. -/
def IsOneSparse {d : ℕ} (a : Fin d → ℝ) : Prop :=
  ∃ (i : Fin d) (c : ℝ), c ≠ 0 ∧ a = Pi.single i c

/-- The norm `‖v‖_M = √(vᵀ M v)` induced by a (positive semidefinite) matrix `M`. -/
noncomputable def mNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ M *ᵥ v)

/-- The perturbed linear bandit model (p. 14) at periods `t = 1, 2, …` with filtration `ℱ`
and conditional sub-Gaussian variance proxy `σ²`: the selected action `A_t` lies in the finite
action set `𝒜_t`, the reward is `Z_t = ⟨ξ_t, A_t⟩ + η_t`, `A_t` is `ℱ_{t-1}`-measurable, `η_t`
is `ℱ_t`-measurable, and `η_t` is `σ²`-sub-Gaussian conditionally on `ℱ_{t-1}`
(`E[exp(α η_t) | ℱ_{t-1}] ≤ exp(σ² α² / 2)` for all `α`). -/
def IsPLBModel {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℕ mΩ)
    (ξ : ℕ → Ω → Fin d → ℝ) (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) (A : ℕ → Ω → Fin d → ℝ)
    (Z η : ℕ → Ω → ℝ) (σ2 : ℝ≥0) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    (∀ ω, A t ω ∈ 𝒜 t ω ∧ Z t ω = ξ t ω ⬝ᵥ A t ω + η t ω) ∧
    Measurable[ℱ (t - 1)] (A t) ∧ Measurable[ℱ t] (η t) ∧
    HasCondSubgaussianMGF (ℱ (t - 1)) (ℱ.le (t - 1)) (η t) σ2 P

/-- The perturbation condition of a perturbed linear bandit with perturbation constant `C_p`
(p. 14): `‖ξ_s - ξ_t‖_∞ ≤ C_p` for all periods `s, t ≥ 1`, on every sample path. -/
def HasPerturbation {d : ℕ} {Ω : Type*} (ξ : ℕ → Ω → Fin d → ℝ) (Cp : ℝ) : Prop :=
  ∀ s t : ℕ, 1 ≤ s → 1 ≤ t → ∀ ω i, |ξ s ω i - ξ t ω i| ≤ Cp

/-- Condition 1 (p. 20): `|⟨ξ_t, a⟩| ≤ 1` for every `t ≥ 1` and `a ∈ 𝒜_t`. -/
def Condition1 {d : ℕ} {Ω : Type*} (ξ : ℕ → Ω → Fin d → ℝ)
    (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ ω, ∀ a ∈ 𝒜 t ω, |ξ t ω ⬝ᵥ a| ≤ 1

/-- Condition 2 (p. 20): `‖ξ_t‖_∞ ≤ C₁` for every `t ≥ 1`. -/
def Condition2 {d : ℕ} {Ω : Type*} (ξ : ℕ → Ω → Fin d → ℝ) (C1 : ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ ω i, |ξ t ω i| ≤ C1

/-- Condition 3 (p. 20): every `a ∈ 𝒜_t` has `‖a‖₀ = 1` and `‖a‖₂ ≤ a_max`. -/
def Condition3 {d : ℕ} {Ω : Type*} (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) (amax : ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ ω, ∀ a ∈ 𝒜 t ω, IsOneSparse a ∧ Real.sqrt (∑ i, a i ^ 2) ≤ amax

/-- `max_{a ∈ 𝒜} ⟨ξ, a⟩` over a finite nonempty action set (value `0` on the empty set, which
never occurs for an action set containing the selected action). -/
noncomputable def bestValue {d : ℕ} (𝒜 : Finset (Fin d → ℝ)) (ξ : Fin d → ℝ) : ℝ :=
  if h : 𝒜.Nonempty then 𝒜.sup' h (fun a => ξ ⬝ᵥ a) else 0

/-- The PLB regret `R^{PLB}_{T₀} = ∑_{t=1}^{T₀} ⟨ξ_t, A*_t - A_t⟩` with
`A*_t ∈ argmax_{a ∈ 𝒜_t} ⟨ξ_t, a⟩` (proof of Lemma 3, p. 42; p. 48). -/
noncomputable def plbRegret {d : ℕ} {Ω : Type*} (ξ : ℕ → Ω → Fin d → ℝ)
    (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) (A : ℕ → Ω → Fin d → ℝ) (T0 : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T0, (bestValue (𝒜 t ω) (ξ t ω) - ξ t ω ⬝ᵥ A t ω)

/-- The confidence parameter of Lemma 3 (p. 20):
`β̃_t = 1 ∨ (C₁√(λd) + √(2 log(1/δ) + d log((dλ + (t-1) a²_max)/(dλ))))²`. -/
noncomputable def betaTilde (C1 amax lam : ℝ) (d : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  max 1 ((C1 * Real.sqrt (lam * d) +
    Real.sqrt (2 * Real.log (1 / δ) +
      d * Real.log ((d * lam + ((t : ℝ) - 1) * amax ^ 2) / (d * lam)))) ^ 2)

/-- `LinUCB_t(a) = max_{ξ ∈ 𝒞_t(β)} ⟨ξ, a⟩` of Algorithm 5 (p. 17) in closed form
`⟨ξ̂_{t-1}, a⟩ + √β ‖a‖_{V_{t-1}(λ)⁻¹}`, where `V_{t-1}(λ) = λI + ∑_{s=1}^{t-1} A_s A_sᵀ` and
`ξ̂_{t-1} = V_{t-1}(λ)⁻¹ ∑_{s=1}^{t-1} A_s Z_s` (the published
`BanditAlgorithm.regularizedDesignMatrix` and `BanditAlgorithm.regularizedLeastSquares`, index
`t - 1`). For `λ > 0` and `β ≥ 0` this is the maximum of `⟨ξ, a⟩` over the ellipsoid
`𝒞_t(β) = {ξ : ‖ξ - ξ̂_{t-1}‖²_{V_{t-1}(λ)} ≤ β}` (Lemma 2 (a) of this mission). -/
noncomputable def linUCB {d : ℕ} {Ω : Type*} (lam β : ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (Z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (a : Fin d → ℝ) : ℝ :=
  BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω ⬝ᵥ a +
    Real.sqrt β * mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ a

/-- `ℬ̃_t = {δ(a) : a ∈ 𝒜_t}`, the nonzero indices of the available actions (p. 16). -/
noncomputable def availIdx {d : ℕ} (𝒜 : Finset (Fin d → ℝ)) : Finset (Fin d) :=
  𝒜.biUnion supp

/-- `ℬ̃′_t = {δ(A_s) : s ∈ [t-1]}`, the nonzero indices of the past actions (p. 16). -/
noncomputable def pastIdx {d : ℕ} {Ω : Type*} (A : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    Finset (Fin d) :=
  (Finset.Icc 1 (t - 1)).biUnion (fun s => supp (A s ω))

/-- On the sample path `ω`, the actions `A_1, …, A_{T₀}` are a run of M-LinUCB (Algorithm 5,
p. 17) with regularization `λ` and confidence parameters `β_t`, for **every** tie-breaking rule:
at each `t ∈ [T₀]`, `A_t ∈ 𝒜_t`; if `ℬ̃_t ⊄ ℬ̃′_t`, then `δ(A_t) ∉ ℬ̃′_t`; if `ℬ̃_t ⊆ ℬ̃′_t`,
then `A_t` maximizes `LinUCB_t` over `𝒜_t`. -/
def IsMLinUCBRunAt {d : ℕ} {Ω : Type*} (lam : ℝ) (β : ℕ → ℝ)
    (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) (A : ℕ → Ω → Fin d → ℝ) (Z : ℕ → Ω → ℝ)
    (T0 : ℕ) (ω : Ω) : Prop :=
  ∀ t ∈ Finset.Icc 1 T0,
    A t ω ∈ 𝒜 t ω ∧
    (¬ availIdx (𝒜 t ω) ⊆ pastIdx A t ω → Disjoint (supp (A t ω)) (pastIdx A t ω)) ∧
    (availIdx (𝒜 t ω) ⊆ pastIdx A t ω →
      ∀ a ∈ 𝒜 t ω, linUCB lam (β t) A Z t ω a ≤ linUCB lam (β t) A Z t ω (A t ω))

/-- The shadow parameter `ξ̇_t = V⁺_{t-1} ∑_{s=1}^{t-1} A_s A_sᵀ ξ_s` of Lemma S3 (p. 39), in
coordinates: `(ξ̇_t)_i = (∑_{s=1}^{t-1} A_{s,i}² ξ_{s,i}) / (∑_{s=1}^{t-1} A_{s,i}²)`, which is the
Moore–Penrose formula when every `A_s` has a single nonzero entry (then `V_{t-1}` is diagonal);
Lean's `0 / 0 = 0` gives the Moore–Penrose value `0` on coordinates never pulled. -/
noncomputable def shadowParam {d : ℕ} {Ω : Type*} (A ξ : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    Fin d → ℝ :=
  fun i => (∑ s ∈ Finset.Icc 1 (t - 1), A s ω i ^ 2 * ξ s ω i) /
    (∑ s ∈ Finset.Icc 1 (t - 1), A s ω i ^ 2)

end LuoSunLiu.DIP


