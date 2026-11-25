-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSLocalCut
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSLocalCut
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:53.631146+00:00
-- url     : https://prove2.me/theorems/4f13f3c1-a601-480f-b724-55950f4976e5
-- title:
--   Cut GCore GTSSLocal Cut
-- statement:
--   Definitions and structural lemmas for Cut GCore GTSSLocal Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTSSLocalCut.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLocalCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
section preds
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def SliceLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ (Φ Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c c' : Fin P.r → ℂ), c ∈ OmX P.r → c' ∈ OmX P.r →
    (∀ ζ ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)) →
    ∀ ζ ∈ Ann P, (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)
end preds
def GTSSLSliceDZ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), RadDZ P Bs T → SliceLoc P Bs T
def GTSSLSliceSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → (∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1
def GTSSLMat : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    (∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1) →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t
def GTSSLocalOfCut : Prop := GTCLRadT → GTSSLSliceDZ → GTSSLSliceSS → GTSSLMat → GTSSLocal
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


