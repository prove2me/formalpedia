-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:34.310227+00:00
-- url     : https://prove2.me/theorems/79e07ccd-84f6-4a5b-a987-e17e575443e3
-- title:
--   cut GCore GTConn Cut
-- statement:
--   Definitions and structural lemmas for cut GCore GTConn Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/cut_GCore_GTConnCut.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGenTransferCut
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
def Ann (P : M.Par) : Set ℂ := {ζ : ℂ | P.TT < Complex.normSq ζ}
def fnZ (P : M.Par) (f : ℂ → ℂ) : MA.SmQ P.r P.TT := MA.toSm P (fun q => f q.1.2)
def dzQ (P : M.Par) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := ((MA.DQ P).dzP).1 f
def dzbQ (P : M.Par) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := ((MA.DQ P).dzbP).1 f
def modA (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : ℂ :=
  (M.aC P ρ : ℂ) * star ζ / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))
def modB (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : ℂ :=
  (M.aC P ρ : ℂ) * ζ / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))
def ConnF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (A B : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P),
    trR P Bs e (d.L.nab.1 Φ) ρ = dzQ P (trR P Bs e Φ ρ) + fnZ P (A ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e (d.L.nabs.1 Φ) ρ = -dzbQ P (trR P Bs e Φ ρ) + fnZ P (B ρ) * trR P Bs e Φ ρ
def SmAB (P : M.Par) (A B : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A ρ) (Ann P) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B ρ) (Ann P)
def PhaseEq (P : M.Par) (A B u : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 ∧
    A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ = modA P ρ ζ ∧ B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ = modB P ρ ζ
end preds
def GTCLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ A B : M.Ty P → ℂ → ℂ, SmAB P A B ∧ ConnF P Bs d e A B
def GTCReal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∀ ρ, ∀ ζ ∈ Ann P, B ρ ζ = star (A ρ ζ)
def GTCCurv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B →
        ∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A ρ w) ζ).re = 0
def GTCHol : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B →
        ∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A ρ w) 0 R).im = Real.pi * n
def GTCAnnulus : Prop :=
  ∀ (TT : ℝ) (α : ℂ → ℂ), 0 ≤ TT → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → (NF.dZb α ζ).re = 0) →
    (∀ R : ℝ, 0 < R → TT < R ^ 2 → ∃ n : ℤ, (circleIntegral α 0 R).im = Real.pi * n) →
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} ∧
      ∀ ζ : ℂ, TT < Complex.normSq ζ →
        ‖u ζ‖ = 1 ∧ star (u ζ) * NF.dZ u ζ = α ζ ∧ star (u ζ) * NF.dZb u ζ = -star (α ζ)
def GTCGauge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B u : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → PhaseEq P A B u →
        IsFrameB P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) ∧ KapF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) ∧
          NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ)
def GTCTT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → 0 ≤ P.TT
def GTCPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∃ u, PhaseEq P A B u
def GTCPhaseOfCut : Prop := GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTCTT → GTCPhase
def GTConnOfCut : Prop := GTCLocal → GTCPhase → GTCGauge → GTConn
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


