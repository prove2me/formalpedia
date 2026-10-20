-- Prove2me | Definitions.Def_DynkinAsymInfo_Linear_Model
-- name    : DynkinAsymInfo_Linear_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:15:58.344373+00:00
-- url     : https://prove2.me/theorems/e6e04f5a-37b9-44e0-8fe4-138de0bd42b7
-- title:
--   §2 and §6 — the hidden drift GBM and the two information filtrations
-- statement:
--   Fix drifts $\mu_0,\mu_1\in\mathbb R$ and volatility $\sigma>0$. A complete probability space carries a standard Brownian motion $W$ with continuous paths and two independent uniforms $U,\Theta$ on $[0,1]$; the whole Brownian path, $U$, and $\Theta$ are mutually independent. For a prior $\pi\in(0,1)$ set $\theta^\pi=\mathbf1_{\{\Theta<\pi\}}$. The observed state started at $x>0$ is the geometric Brownian motion
--   $$X_t=x\exp\bigl(((1-\theta^\pi)\mu_0+\theta^\pi\mu_1-\sigma^2/2)t+\sigma W_t\bigr).$$
--   The signal-to-noise ratio is $\omega=(\mu_1-\mu_0)/\sigma$. Player 1 observes the completed filtration $\mathcal F^X_t=\sigma(X_s:s\le t)$; player 2 observes its enlargement by $\theta^\pi$. Neither filtration contains $U$.
--
--   This common model fixes the information available to both players in all subsequent statements.
--
--   **Formalization Note.** The explicit GBM replaces the §2 SDE in the §6 instance. The continuous path field selects a modification of Brownian motion. The type is generated from a uniform device to realise every prior on one space.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 4–5, 18, §2 and §6

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, arXiv:1810.07674v5, pp. 4, 18, §2 and §6.
The two possible GBM drifts and the positive volatility. -/
structure Params where
  mu0 : ℝ
  mu1 : ℝ
  sigma : ℝ
  sigma_pos : 0 < sigma

/-- The signal-to-noise ratio, §6, p. 18. -/
noncomputable def signalNoise (p : Params) : ℝ := (p.mu1 - p.mu0) / p.sigma

/-- The original probability space of §2, p. 4. The uniform device `Theta` generates the
unknown Bernoulli type for each prior. Paths are taken in a continuous modification. -/
structure Setting (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  complete_P : P.IsComplete
  W : ℝ≥0 → Ω → ℝ
  brownian : IsBrownianReal W P
  measurable_W : ∀ t, Measurable (W t)
  continuous_W : ∀ ω, Continuous (fun t => W t ω)
  U : Ω → ℝ
  Theta : Ω → ℝ
  measurable_U : Measurable U
  measurable_Theta : Measurable Theta
  uniform_U : HasLaw U (volume.restrict (Set.Icc (0 : ℝ) 1)) P
  uniform_Theta : HasLaw Theta (volume.restrict (Set.Icc (0 : ℝ) 1)) P
  indep_W_Theta : IndepFun (fun ω => fun t => W t ω) Theta P
  indep_WTheta_U : IndepFun (fun ω => ((fun t => W t ω), Theta ω)) U P

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The hidden type `θ^π = 1{Theta < π}` (§2, p. 4). -/
noncomputable def hiddenType (st : Setting Ω) (pi : ℝ) (ω : Ω) : ℝ :=
  if st.Theta ω < pi then 1 else 0

/-- The strong GBM solution of (1) in §6 (p. 18). -/
noncomputable def X (p : Params) (st : Setting Ω) (x pi : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x * Real.exp (((p.mu0 * (1 - hiddenType st pi ω) + p.mu1 * hiddenType st pi ω) -
    p.sigma ^ 2 / 2) * (t : ℝ) + p.sigma * st.W t ω)

private lemma measurable_hiddenType (st : Setting Ω) (pi : ℝ) :
    Measurable (hiddenType st pi) :=
  Measurable.ite (measurableSet_lt st.measurable_Theta measurable_const) measurable_const measurable_const

private lemma measurable_X (p : Params) (st : Setting Ω) (x pi : ℝ) (t : ℝ≥0) :
    Measurable (X p st x pi t) := by
  unfold X
  have ht := measurable_hiddenType st pi
  have hw := st.measurable_W t
  fun_prop

/-- The augmented observation filtration `F^X` (§2, p. 4). No type or randomisation device
is included in the generated information. -/
noncomputable def FX (p : Params) (st : Setting Ω) (x pi : ℝ) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t := MeasurableSpace.generateFrom
    ({A | MeasurableSet[⨆ (s : ℝ≥0) (_ : s ≤ t),
      MeasurableSpace.comap (X p st x pi s) (inferInstance : MeasurableSpace ℝ)] A} ∪
      {N | st.P N = 0})
  mono' := by
    intro s t hst
    apply MeasurableSpace.generateFrom_mono
    apply Set.union_subset_union_left
    intro A hA
    have hle : (⨆ (u : ℝ≥0) (_ : u ≤ s),
      MeasurableSpace.comap (X p st x pi u) (inferInstance : MeasurableSpace ℝ)) ≤
      ⨆ (u : ℝ≥0) (_ : u ≤ t),
      MeasurableSpace.comap (X p st x pi u) (inferInstance : MeasurableSpace ℝ) :=
        biSup_mono (fun u hu => hu.trans hst)
    exact hle A hA
  le' := by
    intro t
    apply MeasurableSpace.generateFrom_le
    rintro A (hA | hA)
    · have hle : (⨆ (u : ℝ≥0) (_ : u ≤ t),
        MeasurableSpace.comap (X p st x pi u) (inferInstance : MeasurableSpace ℝ)) ≤
        ‹MeasurableSpace Ω› :=
          iSup₂_le fun u _ => (measurable_X p st x pi u).comap_le
      exact hle A hA
    · exact st.complete_P.out A hA

/-- Player 2's augmented filtration `F^{X,θ}` (§2, p. 4). It contains the observation
filtration and the hidden type, but never the independent randomisation device `U`. -/
noncomputable def FXTheta (p : Params) (st : Setting Ω) (x pi : ℝ) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t := (FX p st x pi t) ⊔
    MeasurableSpace.comap (hiddenType st pi) (inferInstance : MeasurableSpace ℝ)
  mono' := by
    intro s t hst
    exact sup_le_sup_right ((FX p st x pi).mono hst) _
  le' := by
    intro t
    exact sup_le ((FX p st x pi).le t) (measurable_hiddenType st pi).comap_le

end DynkinAsymInfo.Linear


