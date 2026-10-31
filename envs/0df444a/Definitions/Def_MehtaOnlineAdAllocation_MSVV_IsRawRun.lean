-- Prove2me | Definitions.Def_MehtaOnlineAdAllocation_MSVV_IsRawRun
-- name    : MehtaOnlineAdAllocation_MSVV_IsRawRun
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:38:31.0182+00:00
-- url     : https://prove2.me/theorems/fd8d8277-a7d0-4ae9-b342-7969fb1e13ba
-- title:
--   Section 5.2 — raw-bid proof run and gained score
-- statement:
--   This is the explicitly simplified proof rule: compare $b_{ut}\psi(S_u(t)/B_u)$ with the raw bid in place of the capped bid. Choose an available maximizer, and reject only when all raw scores are zero. A final raw charge may overshoot the budget, after which the advertiser is unavailable. Capped prefix spend is sufficient for its state: before exhaustion raw and capped spend agree; after exhaustion the advertiser has score zero and cannot be selected. Terminal spend used in the geometry is still capped.
--
--   The gained raw score on an arrival is the winning raw score, or zero for rejection. This quantity is not actual capped revenue. The definition is used only for the proof equations; it is not substituted for the capped MSVV rule in Theorem 5.3.
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), Ignored-capping simplification, printed p. 308 (PDF p. 46); §5.2 proof, pp. 312–315 (PDF pp. 50–53), equations (5.6)–(5.7).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_Spend
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_psi

namespace MehtaOnlineAdAllocation.MSVV

noncomputable def rawScore {N M : ℕ} (I : Instance N M)
    (σ : Allocation N M) (u : Fin N) (t : Fin M) : ℝ :=
  I.bid u t * psi (spend I σ u t.val / I.budget u)

def IsRawRun {N M : ℕ} (I : Instance N M) (σ : Allocation N M) : Prop :=
  ∀ t, match σ t with
  | none => ∀ u, rawScore I σ u t = 0
  | some u => spend I σ u t.val < I.budget u ∧
      ∀ v, rawScore I σ v t ≤ rawScore I σ u t

noncomputable def gainedRawScore {N M : ℕ} (I : Instance N M)
    (σ : Allocation N M) (t : Fin M) : ℝ :=
  match σ t with
  | none => 0
  | some u => rawScore I σ u t

end MehtaOnlineAdAllocation.MSVV


