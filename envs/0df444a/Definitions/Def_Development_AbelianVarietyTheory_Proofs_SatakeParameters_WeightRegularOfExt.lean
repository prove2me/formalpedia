-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T19:04:35.300693+00:00
-- url     : https://prove2.me/theorems/542b777a-b3e1-4616-aadb-8f63e94a7c46
-- title:
--   Weight Regular Of Ext
-- statement:
--   Definitions and structural lemmas for Weight Regular Of Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
abbrev Eig : Type := ∀ w : PlE H, A.LP w → G H.E N.Om → Multiset ℂ
def FrobLift (w : PlE H) (σ : G H.E N.Om) : Prop := IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ
def charRep (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) : G H.E N.Om →* GL (Fin 1) (N.O i) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp χ
def Cont (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)))
def matK (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (g : G H.E N.Om) :
    Matrix (Fin a) (Fin a) (Kf N i) :=
  ((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).map (algebraMap (N.O i) (Kf N i))
def wd (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (w : PlE H) : A.LP w :=
  A.wdOf i (mapRep (iotaOQ N A i) ρ) w
def DeRham (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (w : PlE H) : Prop :=
  A.IsdRW i (mapRep (iotaOQ N A i) ρ) w
def SubOrQuot (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (χ : G H.E N.Om →* (N.O i)ˣ)
    (w : PlE H) : Prop :=
  ∃ v : Fin a → Kf N i, v ≠ 0 ∧
    ((∀ g ∈ Dec (F := H.E) (N.plOm.1 w), (matK N i ρ g).mulVec v =
        algebraMap (N.O i) (Kf N i) ((χ g : (N.O i)ˣ) : N.O i) • v) ∨
      (∀ g ∈ Dec (F := H.E) (N.plOm.1 w), Matrix.vecMul v (matK N i ρ g) =
        algebraMap (N.O i) (Kf N i) ((χ g : (N.O i)ˣ) : N.O i) • v))
def EigLaws (eig : Eig N A) : Prop := ∀ w σ, FrobLift N w σ →
  (∀ a : A.LP w, Multiset.card (eig w a σ) = A.lpDim a) ∧
  (∀ (a : A.LP w) (s : ℝ), eig w (A.lpTw a s) σ =
    (eig w a σ).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ))) ∧
  (∀ (a χ : A.LP w) (c : ℂ), A.lpDim χ = 1 → eig w χ σ = {c} →
    eig w (A.lpChar a χ) σ = (eig w a σ).map (· * c))
def EigAway (eig : Eig N A) : Prop := ∀ (i : N.Loc) (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (N.O i)),
  Cont N i ρ → ∀ w, w ∉ placesOver H.E (N.l i) → ∀ σ, FrobLift N w σ →
    ((ρ σ : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).charpoly.map (iotaO N A i) =
      ((eig w (wd N A i ρ w) σ).map fun α => X - C α).prod
def EigAbove (eig : Eig N A) : Prop := ∀ (i : N.Loc) (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (N.O i))
  (χ : G H.E N.Om →* (N.O i)ˣ), Cont N i ρ → Cont N i (charRep N i χ) →
  ∀ w, w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w → DeRham N A i (charRep N i χ) w →
    SubOrQuot N i ρ χ w → ∀ σ, FrobLift N w σ →
      eig w (wd N A i (charRep N i χ) w) σ ≤ eig w (wd N A i ρ w) σ
def TemperedSizes (eig : Eig N A) : Prop := ∀ w σ, FrobLift N w σ → ∀ a : A.LP w, A.tempered a →
  ∀ α ∈ eig w a σ, ((normV w : ℕ) : ℝ) ^ (-(((A.lpDim a : ℝ) - 1) / 2)) ≤ ‖α‖ ∧
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((A.lpDim a : ℝ) - 1) / 2)
def Matches (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (π : A.CG a) (u : ℝ) : Prop :=
  ∀ᶠ w in Filter.cofinite, IsSplitPl H w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).charpoly.map (iotaO N A i) =
      galPol A (A.lpTw (A.locG π w) u)
def LocalGlobal : Prop := ∀ (i : N.Loc) (a : ℕ), 1 ≤ a → ∀ (π : A.CG a) (η : A.CG 1) (s : ℝ),
  A.csd (A.tw π η) → A.ralg (A.tw π η) → (∀ τ, ∀ z ∈ A.infG η τ, ∃ k : ℤ, (s : ℂ) - z = k) →
  ∀ ρ : G H.E N.Om →* GL (Fin a) (N.O i), Cont N i ρ →
    IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) → Matches N A i ρ π (s + (1 - (a : ℝ)) / 2) →
    ∀ w, wd N A i ρ w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2) ∧
      (w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w)
def EtaType : Prop := A.csd A.etaT ∧ ∀ τ, ∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2
def WeightRegular : Prop := ∀ (i : N.Loc) (_ : A.AV i) (τ : H.E →+* ℂ), (A.infWt i τ).Nodup ∧
  ∀ z ∈ A.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((R.nV : ℂ) - 1) / 2
def GoodCuspidal : Prop := ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
  HasParamX N A i x Sig → goodSig N A Sig → IsCuspIso N A Sig
end GlobalTheory.LocalInv


