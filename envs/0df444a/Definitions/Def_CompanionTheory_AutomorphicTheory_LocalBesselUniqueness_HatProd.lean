-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
-- name    : CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:57:26.602007+00:00
-- url     : https://prove2.me/theorems/850dac78-d7a4-4471-ab9f-cf5ec80735ba
-- title:
--   Hat Prod
-- statement:
--   Definitions and structural lemmas for Hat Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP
section defs
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def FFB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :=
  Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)
def IsGaugeQQB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ
def PInv (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (Θ : B.DiffOp P.k P.r Wp Wq) : Prop :=
  CutMP.PolyOp o κ Θ ∧ B.Commutes Bs (B.GPos Bs) Θ
def RealF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (o κ : ℕ)
    (Φ : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT) : Prop :=
  ∃ ts : List (MA.A P (MA.DQ P) × B.DiffOp P.k P.r Wp Wq),
    (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet P L) ∧ PInv P Bs o κ t.2) ∧
    ∀ J ∈ FFB P Bs, Φ J = (ts.map fun t => MA.actA P t.1 (Gauge.trJB P Bs e (B.opApply t.2 J))).sum
def IsTr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (X : MA.A P (MA.DQ P)) : Prop :=
  ∃ Θ : B.DiffOp P.k P.r Wp Wq, PInv P Bs (2 * P.r + P.k + 1) ((P.r + 1) * (2 * P.r + P.k + 1)) Θ ∧
    ∀ J ∈ FFB P Bs, Gauge.trJB P Bs e (B.opApply Θ J) = MA.actA P X (Gauge.trJB P Bs e J)
end defs
def CapAB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ y : ℂ, IsTr P Bs e (L.Ahat y) ∧ IsTr P Bs e (L.Ahatv y)
def CapRB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    IsGaugeQQB P Bs e → ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ y : ℝ, IsTr P Bs e (RhM P L y) ∧ IsTr P Bs e (RhvM P L y)
def HatProdB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    IsGaugeQQB P Bs e → ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ w : List (MA.A P (MA.DQ P)), (∀ a ∈ w, a ∈ MA.hatSet P L) →
      RealF P Bs e L (w.length * (2 * P.r + P.k + 1)) (w.length * ((P.r + 1) * (2 * P.r + P.k + 1)))
        (fun J => MA.actA P w.prod (Gauge.trJB P Bs e J))
section place
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
variable {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} {L : R.LevelData (MA.A P (MA.DQ P)) P.r} {o κ : ℕ}
variable (P Bs e L o κ) in

def RealX (X : MA.A P (MA.DQ P)) : Prop := RealF P Bs e L o κ (fun J => MA.actA P X (Gauge.trJB P Bs e J))
end place
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms


