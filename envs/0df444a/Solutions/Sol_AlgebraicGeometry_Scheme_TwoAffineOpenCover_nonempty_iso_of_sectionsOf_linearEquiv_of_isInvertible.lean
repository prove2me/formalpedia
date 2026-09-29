-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/65b36807-1dac-535c-9d78-55b1ef1c0c3d

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible

set_option autoImplicit false

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_top_eq_opensRange moduleSpecΓFunctor Scheme.Modules.restrictFunctorCongr Spec Spec.map Scheme Scheme.Modules.restrictFunctor IsAffineOpen.fromSpec_app_self Scheme.Modules.Hom.id_app Scheme.Modules.restrictFunctorIsoPullback IsOpenImmersion Scheme.Modules.fromTildeΓ modulesSpecToSheaf tilde.functor Scheme.Modules.toOpen_fromTildeΓ_app Scheme.Modules.restrictFunctorComp StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.hom_ext_of_isIso_fromTildeGamma Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.image_top_eq_opensRange Modules.restrictFunctorCongr Modules.restrictFunctor Modules.Hom.id_app Modules.restrictFunctorIsoPullback Modules.fromTildeΓ restrictFunctor Hom.comp_app Modules.toOpen_fromTildeΓ_app Modules.restrictFunctorComp Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.hom_ext_of_isIso_fromTildeGamma Modules.exists_hom_restrict_eq_of_isOpenImmersion Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1 sectionsOf exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace GlueIso
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

section Generic

variable {Y : Scheme.{u}}

theorem op_hom_eq {U V : Y.Opens} (i j : op U ⟶ op V) : i = j :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem map_endo (M : Y.Modules) {U : Y.Opens} (i : op U ⟶ op U) (x : Γ(M, U)) :
    M.presheaf.map i x = x := by
  rw [op_hom_eq i (𝟙 _), CategoryTheory.Functor.map_id]; rfl

theorem map_map (M : Y.Modules) {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (x : Γ(M, U)) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp]; rfl

theorem map_irrel (M : Y.Modules) {U V : Y.Opens} (i j : op U ⟶ op V) (x : Γ(M, U)) :
    M.presheaf.map i x = M.presheaf.map j x := by rw [op_hom_eq i j]

theorem ring_map_endo {U : Y.Opens} (i : op U ⟶ op U) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map i x = x := by
  rw [op_hom_eq i (𝟙 _), CategoryTheory.Functor.map_id]; rfl

theorem ring_map_map {U V W : Y.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map j (Y.presheaf.map i x) = Y.presheaf.map (i ≫ j) x := by
  rw [Functor.map_comp]; rfl

theorem ring_map_irrel {U V : Y.Opens} (i j : op U ⟶ op V) (x : Y.presheaf.obj (op U)) :
    Y.presheaf.map i x = Y.presheaf.map j x := by rw [op_hom_eq i j]

theorem app_naturality {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens} (i : op U ⟶ op V) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i x) = N.presheaf.map i (φ.app U x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i) x

theorem comp_app_apply {M N K : Y.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : Y.Opens) (x : Γ(M, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

def rsec {X A : Scheme.{u}} (p : A ⟶ X) [IsOpenImmersion p] (M : X.Modules) (V : A.Opens)
    (x : Γ(M.restrict p, V)) : Γ(M, p ''ᵁ V) := x
def usec {X A : Scheme.{u}} (p : A ⟶ X) [IsOpenImmersion p] (M : X.Modules) (V : A.Opens)
    (x : Γ(M, p ''ᵁ V)) : Γ(M.restrict p, V) := x

section RSec

variable {X A : Scheme.{u}} (p : A ⟶ X) [IsOpenImmersion p] (M : X.Modules) (V : A.Opens)

theorem rsec_usec (x : Γ(M, p ''ᵁ V)) : rsec p M V (usec p M V x) = x := rfl
theorem usec_rsec (x : Γ(M.restrict p, V)) : usec p M V (rsec p M V x) = x := rfl
theorem rsec_injective : Function.Injective (rsec p M V) := fun _ _ h => h
theorem rsec_add (x y : Γ(M.restrict p, V)) : rsec p M V (x + y) = rsec p M V x + rsec p M V y := rfl
theorem usec_add (x y : Γ(M, p ''ᵁ V)) : usec p M V (x + y) = usec p M V x + usec p M V y := rfl

theorem rsec_smul (ρ : A.presheaf.obj (op V)) (z : Γ(M.restrict p, V)) :
    rsec p M V (ρ • z) = ((p.appIso V).inv ρ) • rsec p M V z := rfl
theorem usec_smul (a : X.presheaf.obj (op (p ''ᵁ V))) (y : Γ(M, p ''ᵁ V)) :
    usec p M V (a • y) = ((p.appIso V).hom a) • usec p M V y := by
  apply rsec_injective p M V
  rw [rsec_smul, rsec_usec, rsec_usec, ← CommRingCat.comp_apply, Iso.hom_inv_id]
  rfl
theorem rsec_map {V' : A.Opens} (i : op V ⟶ op V') (z : Γ(M.restrict p, V)) :
    rsec p M V' ((M.restrict p).presheaf.map i z) = M.presheaf.map (p.opensFunctor.map i.unop).op (rsec p M V z) := rfl
theorem usec_map {V' : A.Opens} (i : op V ⟶ op V') (y : Γ(M, p ''ᵁ V)) :
    (M.restrict p).presheaf.map i (usec p M V y) = usec p M V' (M.presheaf.map (p.opensFunctor.map i.unop).op y) := rfl

end RSec

theorem locallyTrivial_of_iso {M N : Y.Modules} (e : M ≅ N) (hM : Scheme.Modules.IsInvertible M) :
    ∀ y : Y, ∃ (V : Y.Opens), y ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj N ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  intro y
  obtain ⟨V, hy, ⟨eV⟩⟩ := hM.1 y
  exact ⟨V, hy, ⟨((Scheme.Modules.pullback V.ι).mapIso e).symm ≪≫ eV⟩⟩

end Generic

section SpecGeneric

variable {R : CommRingCat.{u}}

theorem tilde_map_app_toOpen {M N : ModuleCat.{u} R} (f : M ⟶ N) (U : (Spec R).Opens) (m : M) :
    (tilde.map f).app U (tilde.toOpen M U m : Γ(tilde M, U)) = tilde.toOpen N U (f m) := by
  have h := tilde.toOpen_map_app f U
  exact ConcreteCategory.congr_hom h m

theorem fromTildeΓ_app_top_toOpen (M : (Spec (.of R)).Modules)
    (m : (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) :
    (Scheme.Modules.fromTildeΓ M).app ⊤
      (show Γ(tilde ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)), ⊤) from tilde.toOpen _ ⊤ m) =
      (show Γ(M, ⊤) from m) := by
  have h := Scheme.Modules.toOpen_fromTildeΓ_app M ⊤
  have h' := ConcreteCategory.congr_hom h m
  refine h'.trans ?_
  exact map_endo M _ _

end SpecGeneric

section Chart

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

theorem image_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

abbrev ιd : op U ⟶ op (hU.fromSpec ''ᵁ ⊤) := (eqToHom (image_top U hU)).op

abbrev ιu : op (hU.fromSpec ''ᵁ ⊤) ⟶ op U := (eqToHom (image_top U hU).symm).op

theorem appIso_inv_ΓSpecIso_inv (r : X.presheaf.obj (op U)) :
    (hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso (X.presheaf.obj (op U))).inv r) =
      X.presheaf.map (ιd U hU) r := by
  have h1 : (Scheme.ΓSpecIso (X.presheaf.obj (op U))).inv r =
      (Spec (X.presheaf.obj (op U))).presheaf.map
        (homOfLE (show (⊤ : (Spec (X.presheaf.obj (op U))).Opens) ≤ hU.fromSpec ⁻¹ᵁ U from
          hU.fromSpec_preimage_self.ge)).op (hU.fromSpec.app U r) := by
    rw [IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply, ring_map_map, ring_map_endo]
  rw [h1]
  have h2 := congrArg (fun t => (CommRingCat.Hom.hom t) (hU.fromSpec.app U r))
    (hU.fromSpec.appIso_inv_naturality
      (homOfLE (show (⊤ : (Spec (X.presheaf.obj (op U))).Opens) ≤ hU.fromSpec ⁻¹ᵁ U from
        hU.fromSpec_preimage_self.ge)).op)
  have h2' : (hU.fromSpec.appIso ⊤).inv ((Spec (X.presheaf.obj (op U))).presheaf.map
      (homOfLE (show (⊤ : (Spec (X.presheaf.obj (op U))).Opens) ≤ hU.fromSpec ⁻¹ᵁ U from
        hU.fromSpec_preimage_self.ge)).op (hU.fromSpec.app U r)) =
      X.presheaf.map (hU.fromSpec.opensFunctor.op.map
        (homOfLE (show (⊤ : (Spec (X.presheaf.obj (op U))).Opens) ≤ hU.fromSpec ⁻¹ᵁ U from
          hU.fromSpec_preimage_self.ge)).op)
        ((hU.fromSpec.appIso (hU.fromSpec ⁻¹ᵁ U)).inv (hU.fromSpec.app U r)) := h2
  rw [h2']
  have h3 : (hU.fromSpec.appIso (hU.fromSpec ⁻¹ᵁ U)).inv (hU.fromSpec.app U r) =
      X.presheaf.map (homOfLE (Set.image_preimage_subset hU.fromSpec U.1)).op r :=
    congrArg (fun t => (CommRingCat.Hom.hom t) r) (hU.fromSpec.app_appIso_inv U)
  rw [h3]
  exact (ring_map_map _ _ r).trans (ring_map_irrel _ _ r)

variable (L : X.Modules)

abbrev RL : (Spec (X.presheaf.obj (op U))).Modules := L.restrict hU.fromSpec

abbrev ΓR : ModuleCat (X.presheaf.obj (op U)) :=
  (moduleSpecΓFunctor (R := X.presheaf.obj (op U))).obj (RL U hU L)

def toΓ : ΓR U hU L → Γ(L, hU.fromSpec ''ᵁ ⊤) := fun s => s
def ofΓ : Γ(L, hU.fromSpec ''ᵁ ⊤) → ΓR U hU L := fun s => s

theorem toΓ_ofΓ (x : Γ(L, hU.fromSpec ''ᵁ ⊤)) : toΓ U hU L (ofΓ U hU L x) = x := rfl
theorem ofΓ_toΓ (s : ΓR U hU L) : ofΓ U hU L (toΓ U hU L s) = s := rfl
theorem toΓ_add (s t : ΓR U hU L) : toΓ U hU L (s + t) = toΓ U hU L s + toΓ U hU L t := rfl
theorem ofΓ_add (s t : Γ(L, hU.fromSpec ''ᵁ ⊤)) : ofΓ U hU L (s + t) = ofΓ U hU L s + ofΓ U hU L t := rfl
theorem toΓ_injective : Function.Injective (toΓ U hU L) := fun _ _ h => h

theorem toΓ_eq (s : ΓR U hU L) : (show Γ(RL U hU L, ⊤) from s) = toΓ U hU L s := rfl

theorem toΓ_smul (r : X.presheaf.obj (op U)) (s : ΓR U hU L) :
    toΓ U hU L (r • s) = (X.presheaf.map (ιd U hU) r) • toΓ U hU L s := by
  have h1 : toΓ U hU L (r • s) = ((hU.fromSpec.appIso ⊤).inv
      ((Spec (X.presheaf.obj (op U))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (X.presheaf.obj (op U))).Opens) ≤ ⊤)).op
          ((StructureSheaf.globalSectionsIso (X.presheaf.obj (op U))).hom r))) • toΓ U hU L s := rfl
  rw [h1, ring_map_endo]
  change ((hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso (X.presheaf.obj (op U))).inv r)) • toΓ U hU L s = _
  rw [appIso_inv_ΓSpecIso_inv]

def τ (s : ΓR U hU L) : Γ(L, U) := L.presheaf.map (ιu U hU) (toΓ U hU L s)

def τ' (m : Γ(L, U)) : ΓR U hU L := ofΓ U hU L (L.presheaf.map (ιd U hU) m)

theorem toΓ_τ' (m : Γ(L, U)) : toΓ U hU L (τ' U hU L m) = L.presheaf.map (ιd U hU) m := rfl

theorem τ_τ' (m : Γ(L, U)) : τ U hU L (τ' U hU L m) = m := by
  show L.presheaf.map (ιu U hU) (L.presheaf.map (ιd U hU) m) = m
  rw [map_map, map_endo]

theorem τ'_τ (s : ΓR U hU L) : τ' U hU L (τ U hU L s) = s := by
  show ofΓ U hU L (L.presheaf.map (ιd U hU) (L.presheaf.map (ιu U hU) (toΓ U hU L s))) = s
  rw [map_map, map_endo]; rfl

theorem τ_add (s t : ΓR U hU L) : τ U hU L (s + t) = τ U hU L s + τ U hU L t := by
  show L.presheaf.map (ιu U hU) (toΓ U hU L (s + t)) = _
  rw [toΓ_add, map_add]; rfl

theorem τ'_add (m n : Γ(L, U)) : τ' U hU L (m + n) = τ' U hU L m + τ' U hU L n := by
  show ofΓ U hU L (L.presheaf.map (ιd U hU) (m + n)) = _
  rw [map_add]; rfl

theorem τ_smul (r : X.presheaf.obj (op U)) (s : ΓR U hU L) : τ U hU L (r • s) = r • τ U hU L s := by
  show L.presheaf.map (ιu U hU) (toΓ U hU L (r • s)) = r • L.presheaf.map (ιu U hU) (toΓ U hU L s)
  rw [toΓ_smul, Scheme.Modules.map_smul, ring_map_map, ring_map_endo]

theorem τ'_smul (r : X.presheaf.obj (op U)) (m : Γ(L, U)) : τ' U hU L (r • m) = r • τ' U hU L m := by
  apply toΓ_injective U hU L
  rw [toΓ_smul, toΓ_τ', toΓ_τ', Scheme.Modules.map_smul]

end Chart

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_top_eq_opensRange moduleSpecΓFunctor Scheme.Modules.restrictFunctorCongr Spec Spec.map Scheme Scheme.Modules.restrictFunctor IsAffineOpen.fromSpec_app_self Scheme.Modules.Hom.id_app Scheme.Modules.restrictFunctorIsoPullback IsOpenImmersion Scheme.Modules.fromTildeΓ modulesSpecToSheaf tilde.functor Scheme.Modules.toOpen_fromTildeΓ_app Scheme.Modules.restrictFunctorComp StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.hom_ext_of_isIso_fromTildeGamma Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.image_top_eq_opensRange Modules.restrictFunctorCongr Modules.restrictFunctor Modules.Hom.id_app Modules.restrictFunctorIsoPullback Modules.fromTildeΓ restrictFunctor Hom.comp_app Modules.toOpen_fromTildeΓ_app Modules.restrictFunctorComp Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.hom_ext_of_isIso_fromTildeGamma Modules.exists_hom_restrict_eq_of_isOpenImmersion Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1 sectionsOf exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace GlueIso
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

section ChartHom

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (L L' : X.Modules)
  (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
  (e : Γ(L, U) ≃ₗ[X.presheaf.obj (op U)] Γ(L', U))

def eL : ΓR U hU L ≃ₗ[X.presheaf.obj (op U)] ΓR U hU L' where
  toFun s := τ' U hU L' (e (τ U hU L s))
  invFun s' := τ' U hU L (e.symm (τ U hU L' s'))
  map_add' s t := by rw [τ_add, map_add, τ'_add]
  map_smul' r s := by rw [τ_smul, LinearEquiv.map_smul, τ'_smul]; rfl
  left_inv s := by simp only [τ_τ', LinearEquiv.symm_apply_apply, τ'_τ]
  right_inv s' := by simp only [τ_τ', LinearEquiv.apply_symm_apply, τ'_τ]

def eR : ΓR U hU L ≅ ΓR U hU L' := (eL U hU L L' e).toModuleIso

theorem eR_hom_apply (s : ΓR U hU L) : (eR U hU L L' e).hom s = τ' U hU L' (e (τ U hU L s)) := rfl

include hL in

theorem isIso_fromTildeΓ :
    IsIso (Scheme.Modules.fromTildeΓ (R := X.presheaf.obj (op U)) (RL U hU L)) := by
  refine Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial _ ?_
  have h := locallyTrivial_of_iso ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app L).symm (hL.pullback hU.fromSpec)
  exact h

def ψiso : RL U hU L ≅ RL U hU L' :=
  haveI := isIso_fromTildeΓ U hU L hL
  haveI := isIso_fromTildeΓ U hU L' hL'
  (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := X.presheaf.obj (op U)) (RL U hU L))
      (isIso_fromTildeΓ U hU L hL)).symm ≪≫
    (tilde.functor (X.presheaf.obj (op U))).mapIso (eR U hU L L' e) ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := X.presheaf.obj (op U)) (RL U hU L'))
      (isIso_fromTildeΓ U hU L' hL')

def ψ : RL U hU L ⟶ RL U hU L' := (ψiso U hU L L' hL hL' e).hom

scoped instance isIso_ψ : IsIso (ψ U hU L L' hL hL' e) := by unfold ψ; infer_instance

theorem ψ_eq : ψ U hU L L' hL hL' e =
    (haveI := isIso_fromTildeΓ U hU L hL
     inv (Scheme.Modules.fromTildeΓ (R := X.presheaf.obj (op U)) (RL U hU L)) ≫
      (tilde.functor (X.presheaf.obj (op U))).map (eR U hU L L' e).hom ≫
      Scheme.Modules.fromTildeΓ (R := X.presheaf.obj (op U)) (RL U hU L')) := rfl

theorem ψ_app_top_τ' (m : Γ(L, U)) :
    (ψ U hU L L' hL hL' e).app ⊤ (usec hU.fromSpec L ⊤ (L.presheaf.map (ιd U hU) m)) =
      usec hU.fromSpec L' ⊤ (L'.presheaf.map (ιd U hU) (e m)) := by
  haveI := isIso_fromTildeΓ U hU L hL

  have h1 : (inv (Scheme.Modules.fromTildeΓ (R := X.presheaf.obj (op U)) (RL U hU L))).app ⊤
      (usec hU.fromSpec L ⊤ (L.presheaf.map (ιd U hU) m)) =
      tilde.toOpen (ΓR U hU L) ⊤ (τ' U hU L m) := by
    have h := fromTildeΓ_app_top_toOpen (R := X.presheaf.obj (op U)) (RL U hU L) (τ' U hU L m)
    have h2 := congrArg ((inv (Scheme.Modules.fromTildeΓ (R := X.presheaf.obj (op U)) (RL U hU L))).app ⊤) h
    rw [← comp_app_apply, IsIso.hom_inv_id, Scheme.Modules.Hom.id_app] at h2
    exact h2.symm
  have h2 : ((tilde.functor (X.presheaf.obj (op U))).map (eR U hU L L' e).hom).app ⊤
      (tilde.toOpen (ΓR U hU L) ⊤ (τ' U hU L m)) = tilde.toOpen (ΓR U hU L') ⊤ (τ' U hU L' (e m)) := by
    have h := tilde_map_app_toOpen (eR U hU L L' e).hom ⊤ (τ' U hU L m)
    rw [eR_hom_apply, τ_τ'] at h
    exact h
  rw [ψ_eq, comp_app_apply, comp_app_apply, h1]
  refine (congrArg ((Scheme.Modules.fromTildeΓ (R := X.presheaf.obj (op U)) (RL U hU L')).app ⊤) h2).trans ?_
  exact fromTildeΓ_app_top_toOpen (R := X.presheaf.obj (op U)) (RL U hU L') _

end ChartHom

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_top_eq_opensRange moduleSpecΓFunctor Scheme.Modules.restrictFunctorCongr Spec Spec.map Scheme Scheme.Modules.restrictFunctor IsAffineOpen.fromSpec_app_self Scheme.Modules.Hom.id_app Scheme.Modules.restrictFunctorIsoPullback IsOpenImmersion Scheme.Modules.fromTildeΓ modulesSpecToSheaf tilde.functor Scheme.Modules.toOpen_fromTildeΓ_app Scheme.Modules.restrictFunctorComp StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.hom_ext_of_isIso_fromTildeGamma Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.image_top_eq_opensRange Modules.restrictFunctorCongr Modules.restrictFunctor Modules.Hom.id_app Modules.restrictFunctorIsoPullback Modules.fromTildeΓ restrictFunctor Hom.comp_app Modules.toOpen_fromTildeΓ_app Modules.restrictFunctorComp Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.hom_ext_of_isIso_fromTildeGamma Modules.exists_hom_restrict_eq_of_isOpenImmersion Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1 sectionsOf exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace GlueIso
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

section MoreGeneric

variable {X : Scheme.{u}}

theorem image_comp_eq {C A : Scheme.{u}} (g : C ⟶ A) (f : A ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f]
    (U : C.Opens) : (g ≫ f) ''ᵁ U = f ''ᵁ (g ''ᵁ U) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨g.base x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp⟩

theorem map_congr_hom {Y : Scheme.{u}} (M : Y.Modules) {U V : Y.Opens} (i j : op U ⟶ op V) (x y : Γ(M, U))
    (h : x = y) : M.presheaf.map i x = M.presheaf.map j y := by rw [h, op_hom_eq i j]

theorem image_eq_of_eq {A : Scheme.{u}} {p q : A ⟶ X} [IsOpenImmersion p] [IsOpenImmersion q] (h : p = q)
    (V : A.Opens) : p ''ᵁ V = q ''ᵁ V := by subst h; rfl

theorem opensRange_eq_of_eq {A : Scheme.{u}} {p q : A ⟶ X} [IsOpenImmersion p] [IsOpenImmersion q] (h : p = q) :
    p.opensRange = q.opensRange := by subst h; rfl

theorem restrict_app_apply {A : Scheme.{u}} (p : A ⟶ X) [IsOpenImmersion p] {M N : X.Modules} (φ : M ⟶ N)
    (V : A.Opens) (x : Γ(M.restrict p, V)) :
    ((Scheme.Modules.restrictFunctor p).map φ).app V x = φ.app (p ''ᵁ V) x := rfl

theorem bijective_app_of_iso {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) (U : Y.Opens) :
    Function.Bijective (e.hom.app U) := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  exact ⟨⟨e.inv.app U, by rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app],
    by rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]⟩⟩

theorem isIso_fromTildeΓ_restrict {A : CommRingCat.{u}} (f : Spec A ⟶ X) [IsOpenImmersion f] (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    IsIso (Scheme.Modules.fromTildeΓ (R := A) (show (Spec (.of A)).Modules from L.restrict f)) := by
  refine Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial _ ?_
  have h := locallyTrivial_of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app L).symm (hL.pullback f)
  exact h

end MoreGeneric
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"

section Charts

variable {X : Scheme.{u}} (U0 U1 : X.Opens)

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso.ρ0 : X.presheaf.obj (op U0) ⟶ X.presheaf.obj (op (U0 ⊓ U1)) := X.presheaf.map (homOfLE inf_le_left).op
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso" "ρ0"
private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso.ρ1 : X.presheaf.obj (op U1) ⟶ X.presheaf.obj (op (U0 ⊓ U1)) := X.presheaf.map (homOfLE inf_le_right).op
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso" "ρ1"
abbrev g0 : Spec (X.presheaf.obj (op (U0 ⊓ U1))) ⟶ Spec (X.presheaf.obj (op U0)) := Spec.map (ρ0 U0 U1)
abbrev g1 : Spec (X.presheaf.obj (op (U0 ⊓ U1))) ⟶ Spec (X.presheaf.obj (op U1)) := Spec.map (ρ1 U0 U1)

variable (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))

theorem g0_f0 : g0 U0 U1 ≫ hU0.fromSpec = hU01.fromSpec := hU0.map_fromSpec hU01 (homOfLE inf_le_left).op
theorem g1_f1 : g1 U0 U1 ≫ hU1.fromSpec = hU01.fromSpec := hU1.map_fromSpec hU01 (homOfLE inf_le_right).op

include hU01 in
theorem hg : g0 U0 U1 ≫ hU0.fromSpec = g1 U0 U1 ≫ hU1.fromSpec :=
  (g0_f0 U0 U1 hU0 hU01).trans (g1_f1 U0 U1 hU1 hU01).symm

include hU0 hU01 in
theorem isOpenImmersion_g0 : IsOpenImmersion (g0 U0 U1) := by
  have : IsOpenImmersion (g0 U0 U1 ≫ hU0.fromSpec) := by rw [g0_f0 U0 U1 hU0 hU01]; infer_instance
  exact IsOpenImmersion.of_comp _ hU0.fromSpec

include hU1 hU01 in
theorem isOpenImmersion_g1 : IsOpenImmersion (g1 U0 U1) := by
  have : IsOpenImmersion (g1 U0 U1 ≫ hU1.fromSpec) := by rw [g1_f1 U0 U1 hU1 hU01]; infer_instance
  exact IsOpenImmersion.of_comp _ hU1.fromSpec

end Charts
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"

section OneChart

variable {X : Scheme.{u}} (U W : X.Opens) (hU : IsAffineOpen U) (hWU : W ≤ U)
  {B : Scheme.{u}} (g : B ⟶ Spec (X.presheaf.obj (op U))) [IsOpenImmersion g]
  (hgW : hU.fromSpec ''ᵁ (g ''ᵁ ⊤) = W)
  (L L' : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
  (e : Γ(L, U) ≃ₗ[X.presheaf.obj (op U)] Γ(L', U))

abbrev cW : op W ⟶ op (hU.fromSpec ''ᵁ (g ''ᵁ ⊤)) := (eqToHom hgW).op
abbrev cW' : op (hU.fromSpec ''ᵁ (g ''ᵁ ⊤)) ⟶ op W := (eqToHom hgW.symm).op

def Θ (x : Γ(L, W)) : Γ(L', W) :=
  L'.presheaf.map (cW' U W hU g hgW) (rsec hU.fromSpec L' (g ''ᵁ ⊤)
    ((ψ U hU L L' hL hL' e).app (g ''ᵁ ⊤) (usec hU.fromSpec L (g ''ᵁ ⊤) (L.presheaf.map (cW U W hU g hgW) x))))

theorem Θ_add (x y : Γ(L, W)) :
    Θ U W hU g hgW L L' hL hL' e (x + y) = Θ U W hU g hgW L L' hL hL' e x + Θ U W hU g hgW L L' hL hL' e y := by
  unfold Θ; rw [map_add, usec_add, map_add, rsec_add, map_add]

theorem Θ_smul (a : X.presheaf.obj (op W)) (x : Γ(L, W)) :
    Θ U W hU g hgW L L' hL hL' e (a • x) = a • Θ U W hU g hgW L L' hL hL' e x := by
  unfold Θ
  rw [Scheme.Modules.map_smul, usec_smul, Scheme.Modules.Hom.app_smul, rsec_smul, ← CommRingCat.comp_apply,
    Iso.hom_inv_id, CommRingCat.id_apply, Scheme.Modules.map_smul, ring_map_map, ring_map_endo]

def Θₗ : Γ(L, W) →ₗ[X.presheaf.obj (op W)] Γ(L', W) where
  toFun := Θ U W hU g hgW L L' hL hL' e
  map_add' := Θ_add U W hU g hgW L L' hL hL' e
  map_smul' := Θ_smul U W hU g hgW L L' hL hL' e

theorem Θₗ_apply (x : Γ(L, W)) : Θₗ U W hU g hgW L L' hL hL' e x = Θ U W hU g hgW L L' hL hL' e x := rfl

theorem Θ_res (m : Γ(L, U)) :
    Θ U W hU g hgW L L' hL hL' e (L.presheaf.map (homOfLE hWU).op m) = L'.presheaf.map (homOfLE hWU).op (e m) := by
  unfold Θ
  have h1 : usec hU.fromSpec L (g ''ᵁ ⊤) (L.presheaf.map (cW U W hU g hgW) (L.presheaf.map (homOfLE hWU).op m)) =
      (RL U hU L).presheaf.map (homOfLE (le_top : g ''ᵁ ⊤ ≤ ⊤)).op
        (usec hU.fromSpec L ⊤ (L.presheaf.map (ιd U hU) m)) := by
    rw [usec_map, map_map, map_map]; rfl
  rw [h1, app_naturality, ψ_app_top_τ', rsec_map, rsec_usec, map_map, map_map]
  rfl

theorem ψ_app_normal (t : Γ(L, hU.fromSpec ''ᵁ (g ''ᵁ ⊤)))
    (k : op (hU.fromSpec ''ᵁ (g ''ᵁ ⊤)) ⟶ op W) (k' : op W ⟶ op (hU.fromSpec ''ᵁ (g ''ᵁ ⊤))) :
    rsec hU.fromSpec L' (g ''ᵁ ⊤) ((ψ U hU L L' hL hL' e).app (g ''ᵁ ⊤) (usec hU.fromSpec L (g ''ᵁ ⊤) t)) =
      L'.presheaf.map k' (Θ U W hU g hgW L L' hL hL' e (L.presheaf.map k t)) := by
  unfold Θ
  rw [map_map, map_map, map_endo, map_endo]

end OneChart
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"

section Agreement

variable {X : Scheme.{u}} (U0 U1 : X.Opens)
  (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))
  [IsOpenImmersion (g0 U0 U1)] [IsOpenImmersion (g1 U0 U1)]
  (L L' : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
  (e0 : Γ(L, U0) ≃ₗ[X.presheaf.obj (op U0)] Γ(L', U0))
  (e1 : Γ(L, U1) ≃ₗ[X.presheaf.obj (op U1)] Γ(L', U1))
  (e01 : Γ(L, U0 ⊓ U1) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))] Γ(L', U0 ⊓ U1))
  (he0 : ∀ m, e01 (L.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op m) =
    L'.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op (e0 m))
  (he1 : ∀ m, e01 (L.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op m) =
    L'.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op (e1 m))
  (span0 : Submodule.span (X.presheaf.obj (op (U0 ⊓ U1)))
    (Set.range fun m : Γ(L, U0) => L.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op m) = ⊤)
  (span1 : Submodule.span (X.presheaf.obj (op (U0 ⊓ U1)))
    (Set.range fun m : Γ(L, U1) => L.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op m) = ⊤)

omit [IsOpenImmersion (g1 U0 U1)] in
include hU01 in
theorem f0_g0_top : hU0.fromSpec ''ᵁ ((g0 U0 U1) ''ᵁ ⊤) = U0 ⊓ U1 := by
  rw [← image_comp_eq, Scheme.Hom.image_top_eq_opensRange, opensRange_eq_of_eq (g0_f0 U0 U1 hU0 hU01),
    hU01.opensRange_fromSpec]

omit [IsOpenImmersion (g0 U0 U1)] in
include hU01 in
theorem f1_g1_top : hU1.fromSpec ''ᵁ ((g1 U0 U1) ''ᵁ ⊤) = U0 ⊓ U1 := by
  rw [← image_comp_eq, Scheme.Hom.image_top_eq_opensRange, opensRange_eq_of_eq (g1_f1 U0 U1 hU1 hU01),
    hU01.opensRange_fromSpec]

abbrev Θ0 := Θₗ U0 (U0 ⊓ U1) hU0 (g0 U0 U1) (f0_g0_top U0 U1 hU0 hU01) L L' hL hL' e0
abbrev Θ1 := Θₗ U1 (U0 ⊓ U1) hU1 (g1 U0 U1) (f1_g1_top U0 U1 hU1 hU01) L L' hL hL' e1

include he0 span0 in
theorem Θ0_eq : Θ0 U0 U1 hU0 hU01 L L' hL hL' e0 = e01.toLinearMap := by
  refine LinearMap.ext_on span0 ?_
  rintro _ ⟨m, rfl⟩
  rw [Θₗ_apply, LinearEquiv.coe_coe, Θ_res U0 (U0 ⊓ U1) hU0 inf_le_left, he0]

include he1 span1 in
theorem Θ1_eq : Θ1 U0 U1 hU1 hU01 L L' hL hL' e1 = e01.toLinearMap := by
  refine LinearMap.ext_on span1 ?_
  rintro _ ⟨m, rfl⟩
  rw [Θₗ_apply, LinearEquiv.coe_coe, Θ_res U1 (U0 ⊓ U1) hU1 inf_le_right, he1]

def T0 : L.restrict (g0 U0 U1 ≫ hU0.fromSpec) ⟶ L'.restrict (g0 U0 U1 ≫ hU0.fromSpec) :=
  (Scheme.Modules.restrictFunctorComp (g0 U0 U1) hU0.fromSpec).hom.app L ≫
    (Scheme.Modules.restrictFunctor (g0 U0 U1)).map (ψ U0 hU0 L L' hL hL' e0) ≫
    (Scheme.Modules.restrictFunctorComp (g0 U0 U1) hU0.fromSpec).inv.app L'

def T1 : L.restrict (g0 U0 U1 ≫ hU0.fromSpec) ⟶ L'.restrict (g0 U0 U1 ≫ hU0.fromSpec) :=
  (Scheme.Modules.restrictFunctorCongr (hg U0 U1 hU0 hU1 hU01)).hom.app L ≫
    (Scheme.Modules.restrictFunctorComp (g1 U0 U1) hU1.fromSpec).hom.app L ≫
    (Scheme.Modules.restrictFunctor (g1 U0 U1)).map (ψ U1 hU1 L L' hL hL' e1) ≫
    (Scheme.Modules.restrictFunctorComp (g1 U0 U1) hU1.fromSpec).inv.app L' ≫
    (Scheme.Modules.restrictFunctorCongr (hg U0 U1 hU0 hU1 hU01)).inv.app L'

include hU01 in
theorem P_top : (g0 U0 U1 ≫ hU0.fromSpec) ''ᵁ ⊤ = U0 ⊓ U1 := by
  rw [Scheme.Hom.image_top_eq_opensRange, opensRange_eq_of_eq (g0_f0 U0 U1 hU0 hU01), hU01.opensRange_fromSpec]

abbrev dd : op ((g0 U0 U1 ≫ hU0.fromSpec) ''ᵁ ⊤) ⟶ op (U0 ⊓ U1) := (eqToHom (P_top U0 U1 hU0 hU01).symm).op
abbrev dd' : op (U0 ⊓ U1) ⟶ op ((g0 U0 U1 ≫ hU0.fromSpec) ''ᵁ ⊤) := (eqToHom (P_top U0 U1 hU0 hU01)).op

theorem T0_app_top (t : Γ(L.restrict (g0 U0 U1 ≫ hU0.fromSpec), ⊤)) :
    rsec (g0 U0 U1 ≫ hU0.fromSpec) L' ⊤ ((T0 U0 U1 hU0 L L' hL hL' e0).app ⊤ t) =
      L'.presheaf.map (dd' U0 U1 hU0 hU01)
        (Θ0 U0 U1 hU0 hU01 L L' hL hL' e0 (L.presheaf.map (dd U0 U1 hU0 hU01)
          (rsec (g0 U0 U1 ≫ hU0.fromSpec) L ⊤ t))) := by
  have key : rsec (g0 U0 U1 ≫ hU0.fromSpec) L' ⊤ ((T0 U0 U1 hU0 L L' hL hL' e0).app ⊤ t) =
      L'.presheaf.map (eqToHom (image_comp_eq (g0 U0 U1) hU0.fromSpec ⊤)).op
        (rsec hU0.fromSpec L' ((g0 U0 U1) ''ᵁ ⊤) ((ψ U0 hU0 L L' hL hL' e0).app ((g0 U0 U1) ''ᵁ ⊤)
          (usec hU0.fromSpec L ((g0 U0 U1) ''ᵁ ⊤)
            (L.presheaf.map (eqToHom (image_comp_eq (g0 U0 U1) hU0.fromSpec ⊤).symm).op
              (rsec (g0 U0 U1 ≫ hU0.fromSpec) L ⊤ t))))) := rfl
  rw [key, Θₗ_apply, ψ_app_normal U0 (U0 ⊓ U1) hU0 (g0 U0 U1) (f0_g0_top U0 U1 hU0 hU01) L L' hL hL' e0 _
    ((eqToHom (image_comp_eq (g0 U0 U1) hU0.fromSpec ⊤)).op ≫ dd U0 U1 hU0 hU01)
    (dd' U0 U1 hU0 hU01 ≫ (eqToHom (image_comp_eq (g0 U0 U1) hU0.fromSpec ⊤).symm).op), map_map, map_map]
  exact map_congr_hom L' _ _ _ _ (congrArg (Θ U0 (U0 ⊓ U1) hU0 (g0 U0 U1) (f0_g0_top U0 U1 hU0 hU01) L L' hL hL' e0)
    (map_irrel L _ _ _))

theorem T1_app_top (t : Γ(L.restrict (g0 U0 U1 ≫ hU0.fromSpec), ⊤)) :
    rsec (g0 U0 U1 ≫ hU0.fromSpec) L' ⊤ ((T1 U0 U1 hU0 hU1 hU01 L L' hL hL' e1).app ⊤ t) =
      L'.presheaf.map (dd' U0 U1 hU0 hU01)
        (Θ1 U0 U1 hU1 hU01 L L' hL hL' e1 (L.presheaf.map (dd U0 U1 hU0 hU01)
          (rsec (g0 U0 U1 ≫ hU0.fromSpec) L ⊤ t))) := by
  have key : rsec (g0 U0 U1 ≫ hU0.fromSpec) L' ⊤ ((T1 U0 U1 hU0 hU1 hU01 L L' hL hL' e1).app ⊤ t) =
      L'.presheaf.map (eqToHom (image_eq_of_eq (hg U0 U1 hU0 hU1 hU01) ⊤)).op
        (L'.presheaf.map (eqToHom (image_comp_eq (g1 U0 U1) hU1.fromSpec ⊤)).op
          (rsec hU1.fromSpec L' ((g1 U0 U1) ''ᵁ ⊤) ((ψ U1 hU1 L L' hL hL' e1).app ((g1 U0 U1) ''ᵁ ⊤)
            (usec hU1.fromSpec L ((g1 U0 U1) ''ᵁ ⊤)
              (L.presheaf.map (eqToHom (image_comp_eq (g1 U0 U1) hU1.fromSpec ⊤).symm).op
                (L.presheaf.map (eqToHom (image_eq_of_eq (hg U0 U1 hU0 hU1 hU01) ⊤).symm).op
                  (rsec (g0 U0 U1 ≫ hU0.fromSpec) L ⊤ t))))))) := rfl
  rw [key, Θₗ_apply, ψ_app_normal U1 (U0 ⊓ U1) hU1 (g1 U0 U1) (f1_g1_top U0 U1 hU1 hU01) L L' hL hL' e1 _
    ((eqToHom (image_comp_eq (g1 U0 U1) hU1.fromSpec ⊤)).op ≫
      (eqToHom (image_eq_of_eq (hg U0 U1 hU0 hU1 hU01) ⊤)).op ≫ dd U0 U1 hU0 hU01)
    (dd' U0 U1 hU0 hU01 ≫ (eqToHom (image_eq_of_eq (hg U0 U1 hU0 hU1 hU01) ⊤).symm).op ≫
      (eqToHom (image_comp_eq (g1 U0 U1) hU1.fromSpec ⊤).symm).op),
    map_map, map_map, map_map, map_map]
  exact map_congr_hom L' _ _ _ _ (congrArg (Θ U1 (U0 ⊓ U1) hU1 (g1 U0 U1) (f1_g1_top U0 U1 hU1 hU01) L L' hL hL' e1)
    (map_irrel L _ _ _))

include he0 he1 span0 span1 in

theorem T0_eq_T1 : T0 U0 U1 hU0 L L' hL hL' e0 = T1 U0 U1 hU0 hU1 hU01 L L' hL hL' e1 := by
  haveI := isIso_fromTildeΓ_restrict (g0 U0 U1 ≫ hU0.fromSpec) L hL
  refine Scheme.Modules.hom_ext_of_isIso_fromTildeGamma (R := X.presheaf.obj (op (U0 ⊓ U1)))
    (M := show (Spec (.of (X.presheaf.obj (op (U0 ⊓ U1))))).Modules from L.restrict (g0 U0 U1 ≫ hU0.fromSpec))
    (N := show (Spec (.of (X.presheaf.obj (op (U0 ⊓ U1))))).Modules from L'.restrict (g0 U0 U1 ≫ hU0.fromSpec))
    _ _ (fun t => ?_)
  apply rsec_injective (g0 U0 U1 ≫ hU0.fromSpec) L' ⊤
  have h0 := T0_app_top U0 U1 hU0 hU01 L L' hL hL' e0 t
  have h1 := T1_app_top U0 U1 hU0 hU1 hU01 L L' hL hL' e1 t
  have hΘ : ∀ x, Θ0 U0 U1 hU0 hU01 L L' hL hL' e0 x = Θ1 U0 U1 hU1 hU01 L L' hL hL' e1 x := fun x => by
    rw [Θ0_eq U0 U1 hU0 hU01 L L' hL hL' e0 e01 he0 span0, Θ1_eq U0 U1 hU1 hU01 L L' hL hL' e1 e01 he1 span1]
  rw [hΘ] at h0
  exact h0.trans h1.symm

end Agreement
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_top_eq_opensRange moduleSpecΓFunctor Scheme.Modules.restrictFunctorCongr Spec Spec.map Scheme Scheme.Modules.restrictFunctor IsAffineOpen.fromSpec_app_self Scheme.Modules.Hom.id_app Scheme.Modules.restrictFunctorIsoPullback IsOpenImmersion Scheme.Modules.fromTildeΓ modulesSpecToSheaf tilde.functor Scheme.Modules.toOpen_fromTildeΓ_app Scheme.Modules.restrictFunctorComp StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.hom_ext_of_isIso_fromTildeGamma Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.image_top_eq_opensRange Modules.restrictFunctorCongr Modules.restrictFunctor Modules.Hom.id_app Modules.restrictFunctorIsoPullback Modules.fromTildeΓ restrictFunctor Hom.comp_app Modules.toOpen_fromTildeΓ_app Modules.restrictFunctorComp Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.hom_ext_of_isIso_fromTildeGamma Modules.exists_hom_restrict_eq_of_isOpenImmersion Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1 sectionsOf exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace GlueIso
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry Opposite TopologicalSpace TensorProduct AlgebraicGeometry.Scheme.Modules"

section Main

variable {X : Scheme.{u}} (U0 U1 : X.Opens)
  (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))
  [IsOpenImmersion (g0 U0 U1)] [IsOpenImmersion (g1 U0 U1)]
  (L L' : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
  (e0 : Γ(L, U0) ≃ₗ[X.presheaf.obj (op U0)] Γ(L', U0))
  (e1 : Γ(L, U1) ≃ₗ[X.presheaf.obj (op U1)] Γ(L', U1))
  (e01 : Γ(L, U0 ⊓ U1) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))] Γ(L', U0 ⊓ U1))
  (he0 : ∀ m, e01 (L.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op m) =
    L'.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op (e0 m))
  (he1 : ∀ m, e01 (L.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op m) =
    L'.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op (e1 m))
  (span0 : Submodule.span (X.presheaf.obj (op (U0 ⊓ U1)))
    (Set.range fun m : Γ(L, U0) => L.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op m) = ⊤)
  (span1 : Submodule.span (X.presheaf.obj (op (U0 ⊓ U1)))
    (Set.range fun m : Γ(L, U1) => L.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op m) = ⊤)
  (hsup : U0 ⊔ U1 = ⊤)

omit [IsOpenImmersion (g0 U0 U1)] [IsOpenImmersion (g1 U0 U1)] in
include hsup in
theorem hcov : hU0.fromSpec.opensRange ⊔ hU1.fromSpec.opensRange = ⊤ := by
  rw [hU0.opensRange_fromSpec, hU1.opensRange_fromSpec, hsup]

omit [IsOpenImmersion (g1 U0 U1)] in
include hU01 in
theorem hov : hU0.fromSpec.opensRange ⊓ hU1.fromSpec.opensRange ≤ (g0 U0 U1 ≫ hU0.fromSpec).opensRange := by
  rw [opensRange_eq_of_eq (g0_f0 U0 U1 hU0 hU01), hU0.opensRange_fromSpec, hU1.opensRange_fromSpec,
    hU01.opensRange_fromSpec]

include hU01 he0 he1 span0 span1 hsup in
theorem exists_φ : ∃ φ : L ⟶ L', (Scheme.Modules.restrictFunctor hU0.fromSpec).map φ = ψ U0 hU0 L L' hL hL' e0 ∧
    (Scheme.Modules.restrictFunctor hU1.fromSpec).map φ = ψ U1 hU1 L L' hL hL' e1 := by
  have h := T0_eq_T1 U0 U1 hU0 hU1 hU01 L L' hL hL' e0 e1 e01 he0 he1 span0 span1
  unfold T0 T1 at h
  exact Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion hU0.fromSpec hU1.fromSpec (g0 U0 U1) (g1 U0 U1)
    (hg U0 U1 hU0 hU1 hU01) (hcov U0 U1 hU0 hU1 hsup) (hov U0 U1 hU0 hU1 hU01) _ _ h

omit [IsOpenImmersion (g0 U0 U1)] [IsOpenImmersion (g1 U0 U1)] in
include hsup in
theorem isIso_of_restrict (φ : L ⟶ L') (h0 : (Scheme.Modules.restrictFunctor hU0.fromSpec).map φ = ψ U0 hU0 L L' hL hL' e0)
    (h1 : (Scheme.Modules.restrictFunctor hU1.fromSpec).map φ = ψ U1 hU1 L L' hL hL' e1) : IsIso φ := by
  refine Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top φ (fun i : Bool => cond i U0 U1) ?_ ?_
  · rw [iSup_bool_eq]; exact hsup
  · intro i V hV
    cases i with
    | true =>
      have hVeq : V = hU0.fromSpec ''ᵁ (hU0.fromSpec ⁻¹ᵁ V) := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hU0.opensRange_fromSpec]
        exact (inf_eq_right.mpr hV).symm
      rw [hVeq]
      change IsIso (((Scheme.Modules.restrictFunctor hU0.fromSpec).map φ).app (hU0.fromSpec ⁻¹ᵁ V))
      rw [h0, ConcreteCategory.isIso_iff_bijective]
      exact bijective_app_of_iso (ψiso U0 hU0 L L' hL hL' e0) _
    | false =>
      have hVeq : V = hU1.fromSpec ''ᵁ (hU1.fromSpec ⁻¹ᵁ V) := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hU1.opensRange_fromSpec]
        exact (inf_eq_right.mpr hV).symm
      rw [hVeq]
      change IsIso (((Scheme.Modules.restrictFunctor hU1.fromSpec).map φ).app (hU1.fromSpec ⁻¹ᵁ V))
      rw [h1, ConcreteCategory.isIso_iff_bijective]
      exact bijective_app_of_iso (ψiso U1 hU1 L L' hL hL' e1) _

include hU0 hU1 hU01 hL hL' e0 e1 e01 he0 he1 span0 span1 hsup in

theorem nonempty_iso : Nonempty (L ≅ L') := by
  obtain ⟨φ, h0, h1⟩ := exists_φ U0 U1 hU0 hU1 hU01 L L' hL hL' e0 e1 e01 he0 he1 span0 span1 hsup
  haveI := isIso_of_restrict U0 U1 hU0 hU1 L L' hL hL' e0 e1 hsup φ h0 h1
  exact ⟨asIso φ⟩

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "tilde.map Scheme.Modules.Hom.app_smul IsOpenImmersion.of_comp Scheme.Modules.pullback tilde.toOpen_map_app Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_top_eq_opensRange moduleSpecΓFunctor Scheme.Modules.restrictFunctorCongr Spec Spec.map Scheme Scheme.Modules.restrictFunctor IsAffineOpen.fromSpec_app_self Scheme.Modules.Hom.id_app Scheme.Modules.restrictFunctorIsoPullback IsOpenImmersion Scheme.Modules.fromTildeΓ modulesSpecToSheaf tilde.functor Scheme.Modules.toOpen_fromTildeΓ_app Scheme.Modules.restrictFunctorComp StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules tilde Scheme.Modules.map_smul tilde.toOpen Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.Modules.IsInvertible Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.hom_ext_of_isIso_fromTildeGamma Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.image_top_eq_opensRange Modules.restrictFunctorCongr Modules.restrictFunctor Modules.Hom.id_app Modules.restrictFunctorIsoPullback Modules.fromTildeΓ restrictFunctor Hom.comp_app Modules.toOpen_fromTildeΓ_app Modules.restrictFunctorComp Modules Opens Modules.map_smul restrict ΓSpecIso TwoAffineOpenCover Modules.IsInvertible Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.hom_ext_of_isIso_fromTildeGamma Modules.exists_hom_restrict_eq_of_isOpenImmersion Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 sup_eq_top isAffineOpen_U1 sectionsOf exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible"
namespace GlueIso
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

open TensorProduct in

theorem span_eq_top_of_baseChange {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {M : Type*}
    [AddCommGroup M] [Module A M] {N : Type*} [AddCommGroup N] [Module B N]
    (r : M → N) (rbc : B ⊗[A] M ≃ₗ[B] N) (h : ∀ m, rbc (1 ⊗ₜ m) = r m) :
    Submodule.span B (Set.range r) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨t, rfl⟩ := rbc.surjective x
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul b m =>
    have hb : b ⊗ₜ[A] m = b • ((1 : B) ⊗ₜ[A] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hb, LinearEquiv.map_smul, h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso"

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible.AlgebraicGeometry TensorProduct Opposite AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlueIso in

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (L L' : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.sectionsOf c L').M0)
    (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.sectionsOf c L').M1)
    (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.sectionsOf c L').M01)
    (he0 : ∀ m, e01 ((𝒱.sectionsOf c L).r0 m) = (𝒱.sectionsOf c L').r0 (e0 m))
    (he1 : ∀ m, e01 ((𝒱.sectionsOf c L).r1 m) = (𝒱.sectionsOf c L').r1 (e1 m)) :
    Nonempty (L ≅ L') := by
  haveI := isOpenImmersion_g0 𝒱.U0 𝒱.U1 𝒱.isAffineOpen_U0 𝒱.isAffineOpen_inf
  haveI := isOpenImmersion_g1 𝒱.U0 𝒱.U1 𝒱.isAffineOpen_U1 𝒱.isAffineOpen_inf
  obtain ⟨rbc0, rbc1, h0, h1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
      𝒱 c L hL
  letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
  letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
  have span0 := span_eq_top_of_baseChange (fun m => (𝒱.sectionsOf c L).r0 m) rbc0 h0
  have span1 := span_eq_top_of_baseChange (fun m => (𝒱.sectionsOf c L).r1 m) rbc1 h1
  exact nonempty_iso 𝒱.U0 𝒱.U1 𝒱.isAffineOpen_U0 𝒱.isAffineOpen_U1 𝒱.isAffineOpen_inf L L' hL hL'
    e0 e1 e01 he0 he1 span0 span1 𝒱.sup_eq_top

end
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible (solution)
