-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T04:31:36.849694+00:00
-- url     : https://prove2.me/theorems/b79c6507-4879-4536-aa20-5f1c74fe12da
-- title:
--   Cut JAFFStable2
-- statement:
--   Definitions and structural lemmas for Cut JAFFStable2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStable2.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
def GermOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq),
    (∀ (U : Set (B.Mat k r)) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U →
      (∀ x ∈ U, x ∈ B.GV k r → f x = f' x) → ∀ g ∈ U, g ∈ B.GV k r →
        B.opApply Θ f g = B.opApply Θ f' g ∧ B.opAdj Θ f g = B.opAdj Θ f' g) ∧
    (∀ (c : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r),
      B.opApply Θ (c • f) g = c • B.opApply Θ f g ∧ B.opAdj Θ (c • f) g = c • B.opAdj Θ f g)
def ExtLoc : Prop :=
  ∀ (k r : ℕ) (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] (O : Set (B.Mat k r)) (J : B.Mat k r → E'),
    IsOpen O → Q.SmoothLev k r 0 O J → ∀ g₀ ∈ B.GV k r, g₀ ∈ O →
      ∃ (f : B.Mat k r → E') (U : Set (B.Mat k r)), B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧
        IsOpen U ∧ g₀ ∈ U ∧ ∀ x ∈ U, x ∈ B.GV k r → f x = J x
def SmoothOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (O : Set (B.Mat k r)), IsOpen O → (∀ g ∈ O, g ∈ B.GV k r → g ∈ B.GPos D) →
    B.SmoothCoef (B.GPos D) Θ → ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → tsupport f ⊆ O →
      Q.SmoothLev k r 0 O (B.opApply Θ f) ∧ Q.SmoothLev k r 0 O (B.opAdj Θ f)
def AdjComm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → B.SuppIn (B.GPos D) f →
      ∀ p, D.inSS p → ∀ g ∈ B.GPos D, B.opAdj Θ (B.rho D p f) g = B.rho D p (B.opAdj Θ f) g
def EquivOps : Prop :=
  ExtLoc →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (O : Set (B.Mat k r)) (P : (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsDom k r D.z D.z' 0 O →
    (∀ (U : Set (B.Mat k r)) (f f' : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U →
      (∀ x ∈ U, x ∈ B.GV k r → f x = f' x) → ∀ g ∈ U, g ∈ B.GV k r → P f g = P f' g) →
    (∀ (c : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → P (c • f) g = c • P f g) →
    (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → tsupport f ⊆ O → Q.SmoothLev k r 0 O (P f)) →
    (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) f → HasCompactSupport f → tsupport f ⊆ O →
      ∀ p, D.inSS p → ∀ g ∈ O, g ∈ B.GV k r → P (B.rho D p f) g = B.rho D p (P f) g) →
    ∀ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O, P J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O
def OmPDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f),
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) ∧
      ∀ g ∈ OmP S T v, g ∈ B.GV S.G.k S.G.r → g ∈ B.GPos (T v).base
end
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS


