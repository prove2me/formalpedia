-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_LocalInvariantsOfColumns
-- name    : Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_LocalInvariantsOfColumns
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:50.822384+00:00
-- url     : https://prove2.me/theorems/563eb1d9-f54e-4f63-a81e-670d51dafd3c
-- title:
--   Local Invariants Of Columns
-- statement:
--   Definitions and structural lemmas for Local Invariants Of Columns, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/LocalInvariantsOfColumns.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalInvariantsOfColumns
def charTwist {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (χ : Γ →* kˣ) : Representation k Γ V where
  toFun g := ((χ g : kˣ) : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]
def colRep {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    Representation k Γ (Fin a → k) where
  toFun g := Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl
def NoInv {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (D : Subgroup Γ) : Prop :=
  Representation.invariants (ρ.comp D.subtype) = ⊥
theorem noInv_iff {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]
    (ρ : Representation k Γ V) (D : Subgroup Γ) :
    NoInv ρ D ↔ ∀ v : V, (∀ g ∈ D, ρ g v = v) → v = 0 := by
  unfold NoInv
  rw [Submodule.eq_bot_iff]
  refine forall_congr' fun v => imp_congr ?_ Iff.rfl
  rw [Representation.mem_invariants]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
example {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [Nontrivial V]
    (D : Subgroup Γ) : ¬ NoInv (Representation.trivial k Γ V) D := by
  rw [noInv_iff]
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (h v fun _ _ => rfl)
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
def chiOneK (i : N.Loc) : G H.E N.Om →* (Kf N i)ˣ :=
  (Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom).comp (N.chi i 1)
def cycK (i : N.Loc) : G H.E N.Om →* (Kf N i)ˣ :=
  (Units.map ((algebraMap (N.O i) (Kf N i)).comp (algebraMap ℤ_[N.l i] (N.O i))).toMonoidHom).comp
    (cycZ (F := H.E) (Ω := N.Om) (N.l i))
def Wtw (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    Representation (Kf N i) (G H.E N.Om) (Fin R.r → Kf N i) :=
  charTwist (colRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ)) (chiOneK N i)⁻¹
def TateDual (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    Representation (Kf N i) (G H.E N.Om) (Module.Dual (Kf N i) (Fin R.r → Kf N i)) :=
  charTwist (Representation.dual (Wtw N i ρ)) (cycK N i)
def IsRankPart (i : N.Loc) (Sig : List (Part A.CG))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) ∧
  ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly.map (iotaO N A i) =
      galPol A (A.lpTw (isoLoc N A (twistIso N A Sig A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2))
def NoLocalInvariants : Prop :=
  ∀ (i : N.Loc) (x : N.X i), x ∈ ZN N A i →
    ∀ Sig : List (Part A.CG), HasParamX N A i x Sig → IsCuspIso N A Sig →
    ∀ ρ : G H.E N.Om →* GL (Fin R.r) (N.O i), IsRankPart N A i Sig ρ →
    ∀ w : PlE H,
      NoInv (Wtw N i ρ) (Dec (F := H.E) (N.plOm.1 w)) ∧
      NoInv (TateDual N i ρ) (Dec (F := H.E) (N.plOm.1 w))
end GlobalTheory.IndefiniteRowSideFullHecke.LocalInvariantsOfColumns
end


