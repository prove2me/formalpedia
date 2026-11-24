-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementW
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementW
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:47.335264+00:00
-- url     : https://prove2.me/theorems/8fb6cdd6-939f-4623-a6a4-a14faef5f925
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/StatementW.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace Formalism.L2.Th1.E
section Gen
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])
def Unif : Prop := Formalism.L2.Th1.A.g₂ W = ι L.g₂ ∧ Formalism.L2.Th1.A.g₃ W = ι L.g₃
open Classical in

def ptW (t : ℂ) : W.toAffine.Point :=
  if h : t ∉ L.lattice ∧ W.toAffine.Nonsingular (ι (L.weierstrassP t) - W.b₂ / 12)
      ((ι (L.derivWeierstrassP t) - W.a₁ * (ι (L.weierstrassP t) - W.b₂ / 12) - W.a₃) / 2)
  then .some _ _ h.2 else 0
def inW (f : ℂ → ℂ) : PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 f)).subst (Formalism.L2.Th1.A.logSer W)
def phW : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L))
    (Formalism.L2.Th1.A.logSer W)
def gW (t : ℂ) : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.fExp (phW l L ι W) * inW l ι W (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L))
end Gen
open Classical in

def PtWAdd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ s t : ℂ, ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t
def PtWZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ t : ℂ, ptW l L ι W t = 0 ↔ t ∈ L.lattice
open Classical in

def AnalyticSysW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ (π : ℂ →+ W.toAffine.Point), (∀ t, π t = ptW l L ι W t) → IsTransSys W π (gW l L ι W)
def AnalyticTransW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
      OneUnit (C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0))⁻¹ * gW l L ι W t)
def ShiftAnalyticW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W → ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ‖px W (ptW l L ι W (ω₀ / 2))‖ ≤ 1 → OneUnit (inW l ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      GaussOne (inW l ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))
end Formalism.L2.Th1.E


