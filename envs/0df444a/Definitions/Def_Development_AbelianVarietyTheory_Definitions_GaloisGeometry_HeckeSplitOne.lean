-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
-- name    : Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:35:20.353798+00:00
-- url     : https://prove2.me/theorems/42b712c0-9f95-4ab9-a67e-83a130a8204e
-- title:
--   Hecke Split One
-- statement:
--   Definitions and structural lemmas for Hecke Split One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/HeckeSplitOne.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaExh
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
def RowSize : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∀ w, IsSplitPl H w →
  A.unr (A.locW i σ w) → ∀ α ∈ A.frobEig (A.locW i σ w),
    ‖α‖ < ((normV w : ℕ) : ℝ) ^ (((R.t : ℝ) - 1) / 2)
def RowSizeLe : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∀ w, IsSplitPl H w →
  A.unr (A.locW i σ w) → ∀ α ∈ A.frobEig (A.locW i σ w),
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)
def HeckeSplitOne : Prop := ∀ χ χ' : A.CG 1,
  (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w) → χ = χ'
def Tempered : Prop := ∀ (a : ℕ) (π : A.CG a), A.csd π → A.ralg π → ∀ w, A.tempered (A.locG π w)
def LamPos (i : N.Loc) : Prop := ∀ σ : what₂.FT,
  (∀ f ∈ what₂.isot (N.j i) σ, what₂.thetaP (N.mu i) (N.j i) (what₂.thetaT (N.mu i) (N.j i) f) =
    ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) • f) ∧
  (what₂.isot (N.j i) σ ≠ ⊥ → 0 < what₂.lamP (N.mu i) (N.j i) σ)
def UpInj (i : N.Loc) : Prop := ∀ σ : what₂.FT, ∀ f ∈ what₂.isot (N.j i) σ,
  what₂.thetaT (N.mu i) (N.j i) f = 0 → f = 0
def ThetaOne : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P, thetaOf N A i σ P
def Pairs (i : N.Loc) (σ : what₂.FT) (P : A.AV i) : Prop :=
  ∃ f ∈ what₂.isot (N.j i) σ, ∃ F ∈ A.typeV i P, inner ℂ F (what₂.thetaT (N.mu i) (N.j i) f) ≠ 0
def HoweUp (i : N.Loc) : Prop := ∀ σ P P', Pairs N A i σ P → Pairs N A i σ P' → P = P'
def HoweDown (i : N.Loc) : Prop := ∀ σ σ' P, Pairs N A i σ P → Pairs N A i σ' P → σ = σ'
def TypeOrth (i : N.Loc) : Prop := ∀ P P', P ≠ P' → A.typeV i P ⟂ A.typeV i P'
def PartOrth (i : N.Loc) : Prop := ∀ σ σ', σ ≠ σ' → what₂.isot (N.j i) σ ⟂ what₂.isot (N.j i) σ'
def liftPar (i : N.Loc) (w : PlE H) (a : A.LP w) : A.LP w :=
  A.lpChar (A.lpSum a (spehLoc N A (muPart N A i) w)) (A.locG A.etaTinv w)
def SplitLift (i : N.Loc) : Prop := ∀ σ P, thetaOf N A i σ P → ∀ w, IsSplitPl H w →
  A.locV i P w = liftPar N A i w (A.locW i σ w)
def ParamLaws : Prop := ∀ w : PlE H,
  (∀ a b χ : A.LP w, A.lpDim χ = 1 → A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ)) ∧
  (∀ χ : A.LP w, A.lpDim χ = 1 → A.lpChar (A.lpZero w) χ = A.lpZero w) ∧
  (∀ (a χ : A.LP w) (s : ℝ), A.lpDim χ = 1 → A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s) ∧
  (∀ a b χ : A.LP w, A.lpDim χ = 1 → A.lpChar a χ = A.lpChar b χ → a = b) ∧
  (∀ a b c : A.LP w, A.lpSum a c = A.lpSum b c → a = b)
def PtLocal (i : N.Loc) : Prop := ∀ (P : A.AV i) (x : N.X i),
  (∀ w, SplitOut N i w → ∃ p : Polynomial (N.O i),
    p.map (iotaO N A i) = galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) ∧
    p.map (IsLocalRing.residue (N.O i)) = (heckePol N i x w).map (IsLocalRing.residue (N.O i))) →
  ∃ y, A.ptV i P = some y
def PtOfLoc (i : N.Loc) : Prop := ∀ (P P' : A.AV i) (x : N.X i), A.ptV i P' = some x →
  (∀ w, SplitOut N i w → A.locV i P w = A.locV i P' w) → A.ptV i P = some x
def LocOfPt (i : N.Loc) : Prop := ∀ (P P' : A.AV i) (x : N.X i), A.ptV i P = some x →
  A.ptV i P' = some x → ∀ w, IsSplitPl H w → A.locV i P w = A.locV i P' w
def RepOfPt (i : N.Loc) : Prop := ∀ (P P' : A.AV i) (x : N.X i), A.ptV i P = some x →
  A.ptV i P' = some x → P = P'
def LiftParam (i : N.Loc) : Prop := ∀ σ P, thetaOf N A i σ P → ∃ Sig, HasParamW N A i σ Sig ∧
  IsBCV N A i P (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv)
def TypePlSplit : Prop := ∀ k v, IsSplitPl H (A.plGw k v)
def ParUp (i : N.Loc) : Prop := ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
  (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x
def DownMem (i : N.Loc) : Prop := ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
  (eigC N A i x).map (what₂.thetaP (N.mu i) (N.j i)) ≤ MjSig N A i Sig
def TypeNZ (i : N.Loc) : Prop := ∀ x ∈ ZgoodN N A i, ∀ F ∈ eigC N A i x,
  what₂.thetaP (N.mu i) (N.j i) F = 0 → F = 0
def GoodPart (i : N.Loc) : Prop :=
  goodPartM N A i = ⨆ x ∈ ZgoodN N A i, ⨆ Sig ∈ {Sig | HasParamX N A i x Sig}, MjSig N A i Sig
def Count (i : N.Loc) : Prop := ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
  Module.finrank ℂ ↥(eigC N A i x) ≤ Module.finrank ℂ ↥(MjSig N A i Sig)
def IsRho (i : N.Loc) (x : N.X i) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (s : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) s →
    ((ρ s : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
      ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c s : (N.O i)ˣ) : N.O i)) = heckePol N i x w
def epsO (i : N.Loc) (g : G H.E N.Om) : N.O i :=
  algebraMap ℤ_[N.l i] (N.O i) ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i])
def NoLocalInv (i : N.Loc) : Prop := ∀ (x : N.X i) (π : A.CG R.r),
  HasParamX N A i x [⟨R.r, π, 1⟩] → ∀ ρ, IsRho N i x ρ → ∀ w : PlE H,
    (∀ v : Fin R.r → N.O i, (∀ g ∈ Dec (F := H.E) (N.plOm.1 w),
      ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).mulVec v = chi1 N i g • v) → v = 0) ∧
    (∀ v : Fin R.r → N.O i, (∀ g ∈ Dec (F := H.E) (N.plOm.1 w),
      Matrix.vecMul v ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)) =
        (chi1 N i g * epsO N i g) • v) → v = 0)
end GlobalTheory.ThetaExh


