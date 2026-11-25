-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:49.953204+00:00
-- url     : https://prove2.me/theorems/2105ea20-9464-4ea7-a81d-15f94d4eb6b0
-- title:
--   Cut GCore GTSSCut
-- statement:
--   Definitions and structural lemmas for Cut GCore GTSSCut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTSSCut.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
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
def SSLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
    trR P Bs e ((d.SS l).1 Φ) ρ' = ∑ ρ, fnZ P (s l ρ' ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e ((star (d.SS l)).1 Φ) ρ' = ∑ ρ, fnZ P (t l ρ' ρ) * trR P Bs e Φ ρ
def SmST (P : M.Par) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s l ρ' ρ) (Ann P) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t l ρ' ρ) (Ann P)
end preds
def GTSSLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t
def GTRadAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (Y : ℂ) (a b : Fin 2) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∃ K : Set ℂ, IsCompact K ∧ K ⊆ Ann P ∧ ∀ ζ ∈ Ann P, ζ ∉ K →
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0 ∧
          (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0) →
      ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((X.t Y a b Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) =
        ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((X.t (star Y) b a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
def GTSSAdjPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, ∀ ζ ∈ Ann P, t l ρ ρ' ζ = star (s l ρ' ρ ζ)
def GTSSConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ' ρ : M.Ty P, ∃ C D : ℂ, ∀ ζ ∈ Ann P, s l ρ' ρ ζ = C ∧ t l ρ' ρ ζ = D
def GTSSPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ, SSLoc P Bs d e (fun l ρ' ρ _ => s l ρ' ρ) (fun l ρ' ρ _ => t l ρ' ρ) →
        (∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, t l ρ ρ' = star (s l ρ' ρ)) →
        ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e' ∧ SSF P Bs d e'
def GTSSOfCut : Prop := GTSSLocal → GTSSAdjPt → GTSSConst → GTSSPhase → GTSS
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


