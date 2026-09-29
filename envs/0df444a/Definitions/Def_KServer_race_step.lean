-- Prove2me | Definitions.Def_KServer_race_step
-- name    : KServer_race_step
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T19:27:06.963202+00:00
-- url     : https://prove2.me/theorems/ab66b220-8f6f-420f-a834-c3e214f8ce09
-- title:
--   The BCR level step assembled
-- statement:
--   The complete BCR induction step. Given four level-$w$ chunk systems (a head system, two coin-side systems, and a closing system) on a taut level space $X$ with marked points $s,t$ at distance $D$, all with sizes clamped to $[0, c_B]$, expected totals at least $T$, variances at most $V$, trivial initial histories, nonempty chunks, and bail price $p_e \le D$, the race construction on the level step (the theta gluing of two three-copy chains of $X$) produces a level-$w{+}1$ chunk system between the new marked points at distance $3D$ with expected total at least
--   $$3T + \tfrac{G}{2} - 2c_B - \tfrac{\kappa\varepsilon}{2} - 2\sqrt{V},$$
--   where $G$ is any lower bound on the expected imbalance of the coin race, and variance at most $9V + 6c_B^2 + 3\,(2(m_L+m_R)c_B)^2$; the trivial-initial-history, variance, and nonempty-chunk conjuncts are carried. All geometric hypotheses of the abstract race (separation, dichotomy, junctions, diameter arithmetic) are discharged by the level-step geometry, tautness supplying the diameter bound. This is Lemma 6's inductive step: totals triple per level up to the gain and lower-order sacrifices, driving the $(\log k)^2$ growth.
-- source:
--   BCR randomized k-server lower bound

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt
import Definitions.Def_KServer_race_cost1
import Definitions.Def_KServer_race_cost2
import Definitions.Def_KServer_race_assemble
import Definitions.Def_KServer_race_fix
import Definitions.Def_KServer_race_total
import Definitions.Def_KServer_race_exp
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists
import Definitions.Def_KServer_fold
import Definitions.Def_KServer_race_geo

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

open ThetaChain

/-- **The BCR level step, assembled on the theta gluing.**  Four level-`w`
chunk systems (head, two coin sides, closing) race on the level step of
their space, producing a level-`w+1` chunk system between the new marked
points with total `3T + G/2 - 2c_B - κε/2 - 2√V` and variance
`9V + 6c_B² + 3(2(m_L+m_R)c_B)²`, carrying the trivial-initial-history,
variance, and nonempty-chunk conjuncts.  `G` is any lower bound on the
expected imbalance of the race (established separately via the
anti-concentration machinery), and tautness of the level space supplies
the diameter arithmetic. -/
theorem race_step {X : Type*} [MetricSpace X] {s t : X} (hst : s ≠ t)
    {cB T pe : ℝ} {mL : ℕ}
    (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) (hpe0 : 0 ≤ pe) {p' : ℝ} (hpe : pe ≤ p')
    (hpeD : dist s t + pe ≤ 2 * dist s t)
    (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    (h0A : ∀ a b : A.Ω, A.hist 0 a = A.hist 0 b)
    (h0L : ∀ a b : BL.Ω, BL.hist 0 a = BL.hist 0 b)
    (h0R : ∀ a b : BR.Ω, BR.hist 0 a = BR.hist 0 b)
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    {V G : ℝ} (hV0 : 0 ≤ V)
    (hVarA : ∑ a : A.Ω, A.P a * ((∑ i, A.size a i)
        - ∑ a' : A.Ω, A.P a' * ∑ i, A.size a' i) ^ 2 ≤ V)
    (hVarL : ∑ l : BL.Ω, BL.P l * ((∑ i, BL.size l i)
        - ∑ l' : BL.Ω, BL.P l' * ∑ i, BL.size l' i) ^ 2 ≤ V)
    (hVarR : ∑ r : BR.Ω, BR.P r * ((∑ i, BR.size r i)
        - ∑ r' : BR.Ω, BR.P r' * ∑ i, BR.size r' i) ^ 2 ≤ V)
    (hVarC : ∑ cc : CC.Ω, CC.P cc * ((∑ i, CC.size cc i)
        - ∑ cc' : CC.Ω, CC.P cc' * ∑ i, CC.size cc' i) ^ 2 ≤ V)
    (hG : G ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
    {mLo' : ℕ} (hmLo : mLo' ≤ mrace A BL BR CC κ) :
    letI := stepMetric s t hst
    ∃ C' : ChunkSystemB (Step s t hst) (stepS s t hst) (stepT s t hst)
        0 cB (3 * T + G / 2 - 2 * cB - (κ : ℝ) * ε / 2
          - 2 * Real.sqrt V) p' mLo',
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2
        ≤ 9 * V + 6 * cB ^ 2
          + 3 * (2 * ((BL.m : ℝ) + (BR.m : ℝ)) * cB) ^ 2) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by
  letI := chain3Metric X s t hst
  letI := stepMetric s t hst
  refine race_system2 A BL BR CC (GA' s t hst) (GL' s t hst)
    (GR' s t hst) (GTL' s t hst) (GTR' s t hst) (stepT s t hst) κ ε
    hε hκL hκR
    (stepRet0 s t hst) (stepRet1 s t hst) (stepRet1 s t hst)
    (stepRet2 s t hst) (stepRet2 s t hst)
    (gL0 s t hst) (gR0 s t hst) (gL1 s t hst) (gR1 s t hst)
    (gL2 s t hst) (gR2 s t hst)
    (stepRet0_lipschitz s t hst) (stepRet1_lipschitz s t hst)
    (stepRet1_lipschitz s t hst) (stepRet2_lipschitz s t hst)
    (stepRet2_lipschitz s t hst)
    (hGA_ret s t hst) (hGL_ret s t hst) (hGR_ret s t hst)
    (hGTL_ret s t hst) (hGTR_ret s t hst)
    (hGA_ne s t hst) (hGL_ne s t hst) (hGR_ne s t hst)
    (hGTL_ne s t hst) (hGTR_ne s t hst)
    (gL0_nonexp s t hst) (gR0_nonexp s t hst) (gL1_nonexp s t hst)
    (gR1_nonexp s t hst) (gL2_nonexp s t hst) (gR2_nonexp s t hst)
    (hGAL_sub s t hst) (hGAR_sub s t hst)
    (fun S => Set.Subset.rfl) (fun S => Set.Subset.rfl)
    (fun S => Set.Subset.rfl) (fun S => Set.Subset.rfl)
    (gJ0 s t hst) (gJ1L s t hst) (gJ1R s t hst) (gJ2L s t hst)
    (gJ2R s t hst) (gJ3L s t hst) (gJ3R s t hst)
    (GTL'_t s t hst) (GTR'_t s t hst)
    hchA hchL hchR hchC
    (sep := 2 * dist s t) (J := dist s t) (p' := p')
    hpe0 hpe (by
      have := dist_pos.mpr hst
      linarith)
    (fun x₁ x₂ => taut_diam s t htaut x₁ x₂) hpeD
    (hsepLR_geo s t hst) (hdicho_geo s t hst)
    h0A h0L h0R hcB
    (hd3_geo s t hst)
    hmLo
    (race_total A BL BR CC κ ε hε hκL hκR hcB hV0 hVarL hVarR hG)
    (race_var A BL BR CC κ ε hε hκL hκR hcB hVarA hVarC)

end Race

end KServer


