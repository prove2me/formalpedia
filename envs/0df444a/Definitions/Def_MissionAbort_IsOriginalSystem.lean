-- Prove2me | Definitions.Def_MissionAbort_IsOriginalSystem
-- name    : MissionAbort_IsOriginalSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:14.960302+00:00
-- url     : https://prove2.me/theorems/c66ad377-5d50-4098-b29c-30c4a8997b4c
-- title:
--   The original system
-- statement:
--   A probability space carrying $T=(T_{12},T_{13},T_{23})$ and signals $Y_1,\dots,Y_N$ is the original system with laws $F$ and $G$ if $T$ is measurable with independent coordinates of laws $G$, exponential of rate $\zeta$, and $F$, and if, for every measurable set $B$ and signal vector $y$,
--   $$
--   \mathbb P(T\in B,\ Y_{1:N}=y)=\int_B \prod_{n=1}^N e\big(\mathrm{state}(u;n\delta),y_n\big)\,\mathrm d\mathcal L_T(u).
--   $$
--
--   **Formalization Note** The last display encodes $\mathbb P(Y_n=k\mid X_n=i)=d_{ik}$, $Y_n=0$ upon failure, and conditional independence of the signals given the failure process. The last is not stated on p.10; the proof uses it on p.EC.2.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3, pp.8–10; Appendix A.2, p.EC.2

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_emit
import Definitions.Def_MissionAbort_state
import Definitions.Def_MissionAbort_timeLaw
import Definitions.Def_MissionAbort_signalLikelihood

namespace MissionAbort

open MeasureTheory

/-- The original system (Sun, Hu & Ye, arXiv:2505.03225v1, §3, pp.8–10): on a probability space,
`T = (T₁₂, T₁₃, T₂₃)` has independent coordinates with laws `G`, exponential of rate `ζ`, and `F`, and
given `T = u` the signals `Y₁, …, Y_N` are independent with `Yₙ` drawn from the state at `nδ` (the
page's `P(Yₙ = k | Xₙ = i) = d_ik`, and `Yₙ = 0` once failed, p.10).

**Formalization Note.** `Y n` for `1 ≤ n ≤ N` is the page's `Yₙ`; other indices are not consulted.
Conditional independence given the failure process is not stated on p.10 but is what the proof uses
(p.EC.2, "by the independence … conditional on the failure process"). -/
structure IsOriginalSystem {K : ℕ} (M : Model K) (F G : Measure ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → ℝ × ℝ × ℝ) (Y : ℕ → Ω → Fin (K + 1)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  measurable_T : Measurable T
  measurable_Y : ∀ n, 1 ≤ n → n ≤ M.N → Measurable (Y n)
  law_T : μ.map T = timeLaw G M.ζ F
  signals : ∀ (B : Set (ℝ × ℝ × ℝ)) (y : Fin M.N → Fin (K + 1)), MeasurableSet B →
    μ.real (T ⁻¹' B ∩ {ω | ∀ i : Fin M.N, Y (i.val + 1) ω = y i}) =
      ∫ u in B, signalLikelihood M u y ∂(timeLaw G M.ζ F)

end MissionAbort


