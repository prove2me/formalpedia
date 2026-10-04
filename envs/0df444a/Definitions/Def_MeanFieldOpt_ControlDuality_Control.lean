-- Prove2me | Definitions.Def_MeanFieldOpt_ControlDuality_Control
-- name    : MeanFieldOpt_ControlDuality_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:28:34.274882+00:00
-- url     : https://prove2.me/theorems/c87516f5-8d94-4870-ba21-bbc9518aeb59
-- title:
--   Admissible controls $D[t,1]$, the constraint $z+\int_t^1\sqrt{\xi''}u\,dB\in(-1,1)$ and the objective of $\mathcal J_\gamma(t,z)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space carrying a standard Brownian motion $(B_r)_{r\ge0}$, and fix a mixture $\xi$, $\gamma\in\mathsf{SF}_+$ and a starting point $(t,z)$.
--
--   1. **Filtration.** $\mathcal F^t_s=\sigma(B_r:\ t\le r\le s)$ is the filtration of the Brownian motion $(B_r)_{r\in[t,1]}$.
--   2. **Admissible controls** (Eq. (4.5) with $D[t,1]$ of p. 10). A process $(u_s)_{s\in[t,1]}$ is admissible if it is progressively measurable for $(\mathcal F^t_s)$, satisfies
--   $$\mathbb E\int_t^1\xi''(s)u_s^2\,ds<\infty,$$
--   and its Itô integral satisfies the terminal constraint
--   $$z+\int_t^1\sqrt{\xi''(s)}\,u_s\,dB_s\in(-1,1)\quad\text{almost surely.}$$
--   3. **Objective.**
--   $$\mathbb E\Big[\int_t^1\xi''(s)u_s\,ds+\frac12\int_t^1\nu(s)\big(\xi''(s)u_s^2-1\big)ds\Big],\qquad \nu(s)=\int_s^1\xi''(r)\gamma(r)\,dr .$$
--   4. The value $\mathcal J_\gamma(t,z)$ is the supremum of the objective over admissible controls; the set of objective values of admissible controls is defined here, and statements assert that a given number is its least upper bound.
--
--   This is the Lagrangian relaxation, with multiplier $\tfrac12\xi''\gamma$, of the control problem that bounds the value of message-passing algorithms.
--
--   **Formalization Note** Brownian time is $\mathbb R_{\ge0}$ and $B$ is a Mathlib `IsBrownianReal` process whose coordinates $B_r$ are measurable. Controls are processes indexed by $\mathbb R_{\ge0}$, and only their values on $[t,1]$ matter (progressive measurability is imposed on the restriction to $[t,1]$, extended by $0$). The stochastic integral is the $L^2$ Itô integral of the published definition `Peng1990.SMP.IsItoIntegral` (horizon $1$, integrand $\mathbb I_{[t,1]}\sqrt{\xi''}\,u$, driving process $B$, filtration $\mathcal F^t$), whose square-integrability condition is exactly $\mathbb E\int_t^1\xi''u^2<\infty$; that condition is also stated separately. Under it the objective's integrand is integrable (Cauchy–Schwarz, since $\xi''$ and $\nu$ are bounded on $[0,1]$), so the expectation is not a default value. The supremum is never computed as a real `sSup`: statements use `IsLUB`.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 10 (admissible controls D[s,t]); p. 11, Eq. (4.5) (𝒥_γ and ν)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MeanFieldOpt_ControlDuality_Parisi

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldOpt.ControlDuality

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The filtration of the Brownian motion `(B_r)_{r ∈ [t₀, 1]}` (p. 10): at time `s` it is
`σ(B_r : t₀ ≤ r ≤ s)` (trivial for `s < t₀`). Each `B_r` is assumed measurable. -/
def bmFiltration (B : ℝ≥0 → Ω → ℝ) (hB : ∀ r, Measurable (B r)) (t₀ : ℝ) :
    Filtration ℝ≥0 mΩ where
  seq s := ⨆ r : ℝ≥0, ⨆ (_ : t₀ ≤ (r : ℝ) ∧ r ≤ s),
    MeasurableSpace.comap (B r) (inferInstance : MeasurableSpace ℝ)
  mono' := fun _ _ hss' =>
    iSup_mono fun _ => iSup_mono' fun h => ⟨⟨h.1, h.2.trans hss'⟩, le_rfl⟩
  le' := fun _ => iSup₂_le fun r _ => (hB r).comap_le

/-- The control `u` restricted to the horizon `[t₀, 1]` (zero outside). Controls are indexed by
the Brownian time `ℝ≥0`. -/
noncomputable def restrictCtrl (t₀ : ℝ) (u : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if t₀ ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1 then u s ω else 0

/-- The integrand `𝕀_{[t₀, 1]}(s) √(ξ''(s)) u_s` of the stochastic integral in Eq. (4.5). -/
noncomputable def itoIntegrand (ξ : Mixture) (t₀ : ℝ) (u : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.sqrt (ξ.xi'' s) * restrictCtrl t₀ u s ω

/-- Admissible controls for `𝒥_γ(t₀, z)` (pp. 10–11, Eq. (4.5)). A process `u` is admissible when
1. `u` (on `[t₀, 1]`) is progressively measurable for the filtration of `(B_r)_{r ∈ [t₀, 1]}`;
2. `E ∫_{t₀}^1 ξ''(r) u_r² dr < ∞` (so `u ∈ D[t₀, 1]`);
3. the Itô integral `I = ∫_{t₀}^1 √(ξ''(s)) u_s dB_s` (the value at time `1` of an `L²` Itô
   integral process `J` of `𝕀_{[t₀,1]} √ξ'' u` against `B`) satisfies `z + I ∈ (−1, 1)` a.s. -/
def Admissible (ξ : Mixture) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : ∀ r, Measurable (B r))
    (t₀ z : ℝ) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsProgressive (bmFiltration B hB t₀) (restrictCtrl t₀ u) ∧
  ∫⁻ ω, ∫⁻ s in Set.Icc t₀ 1, ENNReal.ofReal (ξ.xi'' s * u s.toNNReal ω ^ 2) ∂volume ∂P < ⊤ ∧
  ∃ J : ℝ≥0 → Ω → ℝ,
    Peng1990.SMP.IsItoIntegral (bmFiltration B hB t₀) P 1 B (itoIntegrand ξ t₀ u) J ∧
    ∀ᵐ ω ∂P, z + J 1 ω ∈ Set.Ioo (-1 : ℝ) 1

/-- The objective of Eq. (4.5):
`E[∫_{t₀}^1 ξ''(s) u_s ds + ½ ∫_{t₀}^1 ν(s)(ξ''(s) u_s² − 1) ds]`. -/
noncomputable def obj (ξ : Mixture) (d : SFData) (P : Measure Ω) (t₀ : ℝ)
    (u : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, ((∫ s in t₀..1, ξ.xi'' s * u s.toNNReal ω)
      + (1 / 2) * ∫ s in t₀..1, nu ξ d s * (ξ.xi'' s * u s.toNNReal ω ^ 2 - 1)) ∂P

/-- The set of objective values of admissible controls; `𝒥_γ(t₀, z)` (Eq. (4.5)) is its supremum.
Statements say `IsLUB (controlValues …) v` for "`𝒥_γ(t₀, z) = v`". -/
def controlValues (ξ : Mixture) (d : SFData) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ r, Measurable (B r)) (t₀ z : ℝ) : Set ℝ :=
  {v | ∃ u : ℝ≥0 → Ω → ℝ, Admissible ξ P B hB t₀ z u ∧ v = obj ξ d P t₀ u}

end MeanFieldOpt.ControlDuality


