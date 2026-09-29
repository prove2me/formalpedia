-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0d62dac8-c5b5-593b-9258-f2961bf30fcd

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_NeronModelInfra_TopFormOrder
import Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace OmegaPull

namespace T0

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)

noncomputable abbrev pre : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val

noncomputable def unitD (W : X.Opens) : (⋀[Γ(X, W)]^d Γ(f.kaehler, W)) → Γ(f.topDifferentials d, W) :=
  fun w => ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f d)).app
    (op W) (show (pre f d).obj (op W) from w)

lemma topToSections_eq (W : X.Opens) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    f.topToSections d W s = unitD f d W (exteriorPower.map d (f.kaehlerToSectionsₗ W) s) := rfl

lemma unitD_add (W : X.Opens) (w w' : ⋀[Γ(X, W)]^d Γ(f.kaehler, W)) :
    unitD f d W (w + w') = unitD f d W w + unitD f d W w' :=
  map_add (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f d)).app
    (op W)).hom _ _

lemma unitD_smul (W : X.Opens) (r : Γ(X, W)) (w : ⋀[Γ(X, W)]^d Γ(f.kaehler, W)) :
    unitD f d W (r • w) = r • unitD f d W w :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f d)).app
    (op W)).hom.map_smul r _

noncomputable abbrev resD {W' W : X.Opens} (h : W' ≤ W) (s : Γ(f.topDifferentials d, W)) :
    Γ(f.topDifferentials d, W') :=
  (f.topDifferentials d).presheaf.map (homOfLE h).op s

lemma resD_resD {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (s : Γ(f.topDifferentials d, W₁)) :
    resD f d h₃₂ (resD f d h₂₁ s) = resD f d (h₃₂.trans h₂₁) s := by
  change ((f.topDifferentials d).presheaf.map (homOfLE h₂₁).op ≫
    (f.topDifferentials d).presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma resD_smul {W' W : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (s : Γ(f.topDifferentials d, W)) :
    resD f d h (r • s) = X.presheaf.map (homOfLE h).op r • resD f d h s :=
  Scheme.Modules.map_smul _ (homOfLE h) r s

noncomputable abbrev preMap {W W' : X.Opens} (h : W' ≤ W) (w : ⋀[Γ(X, W)]^d Γ(f.kaehler, W)) :
    ⋀[Γ(X, W')]^d Γ(f.kaehler, W') :=
  show ⋀[Γ(X, W')]^d Γ(f.kaehler, W') from (pre f d).map (homOfLE h).op (show (pre f d).obj (op W) from w)

lemma preMap_ιMulti {W W' : X.Opens} (h : W' ≤ W) (m : Fin d → Γ(f.kaehler, W)) :
    preMap f d h (exteriorPower.ιMulti _ d m) =
      exteriorPower.ιMulti _ d (fun k => (f.kaehler.presheaf.map (homOfLE h).op : Γ(f.kaehler, W) ⟶ _) (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti d f.kaehler.val (homOfLE h).op m

lemma preMap_preMap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (w : ⋀[Γ(X, W₁)]^d Γ(f.kaehler, W₁)) :
    preMap f d h₃₂ (preMap f d h₂₁ w) = preMap f d (h₃₂.trans h₂₁) w := by
  change _ = (pre f d).map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op) (show (pre f d).obj (op W₁) from w)
  rw [PresheafOfModules.map_comp_apply]

lemma resD_unitD {W' W : X.Opens} (h : W' ≤ W) (w : ⋀[Γ(X, W)]^d Γ(f.kaehler, W)) :
    resD f d h (unitD f d W w) = unitD f d W' (preMap f d h w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (pre f d))).naturality (homOfLE h).op
  exact (congrArg (fun φ => φ.hom (show (pre f d).obj (op W) from w)) hnat).symm

noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    (f.kaehlerPresheaf.obj (op W') : Type u) :=
  (f.kaehlerPresheaf.map (homOfLE i).op).hom w

lemma pmap_pmap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (w : (f.kaehlerPresheaf.obj (op W₁) : Type u)) :
    pmap f h₃₂ (pmap f h₂₁ w) = pmap f (h₃₂.trans h₂₁) w := by
  change _ = (f.kaehlerPresheaf.map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op)).hom w
  rw [PresheafOfModules.map_comp_apply]

lemma res_kaehlerToSections {W' W : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    f.kaehler.val.presheaf.map (homOfLE i).op (f.kaehlerToSections W w) = f.kaehlerToSections W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf)).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

noncomputable abbrev preK : X.PresheafOfModules := PresheafOfModules.exteriorPower d f.kaehlerPresheaf

noncomputable abbrev emap {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    ⋀[Γ(X, W')]^d (f.kaehlerPresheaf.obj (op W')) :=
  show ⋀[Γ(X, W')]^d (f.kaehlerPresheaf.obj (op W')) from
    (preK f d).map (homOfLE h).op (show (preK f d).obj (op W) from s)

lemma emap_ιMulti {W W' : X.Opens} (h : W' ≤ W) (m : Fin d → (f.kaehlerPresheaf.obj (op W) : Type u)) :
    emap f d h (exteriorPower.ιMulti _ d m) = exteriorPower.ιMulti _ d (fun k => pmap f h (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti d f.kaehlerPresheaf (homOfLE h).op m

lemma emap_emap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (s : ⋀[Γ(X, W₁)]^d (f.kaehlerPresheaf.obj (op W₁))) :
    emap f d h₃₂ (emap f d h₂₁ s) = emap f d (h₃₂.trans h₂₁) s := by
  change _ = (preK f d).map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op) (show (preK f d).obj (op W₁) from s)
  rw [PresheafOfModules.map_comp_apply]

lemma emap_add {W W' : X.Opens} (h : W' ≤ W) (s s' : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    emap f d h (s + s') = emap f d h s + emap f d h s' :=
  map_add ((preK f d).map (homOfLE h).op).hom _ _

lemma emap_smul {W W' : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    emap f d h (r • s) = X.presheaf.map (homOfLE h).op r • emap f d h s :=
  (preK f d).map_smul (homOfLE h).op r (show (preK f d).obj (op W) from s)

noncomputable abbrev Λ (W : X.Opens) :
    ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W)) →ₗ[Γ(X, W)] ⋀[Γ(X, W)]^d Γ(f.kaehler, W) :=
  exteriorPower.map d (f.kaehlerToSectionsₗ W)

set_option maxHeartbeats 6400000 in

lemma preMap_Λ {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    preMap f d h (Λ f d W s) = Λ f d W' (emap f d h s) := by
  have key : ∀ s ∈ Submodule.span Γ(X, W) (Set.range (exteriorPower.ιMulti Γ(X, W) d
      (M := (f.kaehlerPresheaf.obj (op W) : Type u)))),
      preMap f d h (Λ f d W s) = Λ f d W' (emap f d h s) := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [emap_ιMulti]
      show preMap f d h (exteriorPower.map d (f.kaehlerToSectionsₗ W) (exteriorPower.ιMulti _ d m)) =
        exteriorPower.map d (f.kaehlerToSectionsₗ W') (exteriorPower.ιMulti _ d (fun k => pmap f h (m k)))
      rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, preMap_ιMulti]
      congr 1
      funext k
      exact res_kaehlerToSections f h (m k)
    | zero =>
      have e0 : emap f d h 0 = 0 := map_zero ((preK f d).map (homOfLE h).op).hom
      have p0 : preMap f d h 0 = 0 := map_zero ((pre f d).map (homOfLE h).op).hom
      rw [(Λ f d W).map_zero, e0, (Λ f d W').map_zero, p0]
    | add y z _ _ hy hz =>
      rw [(Λ f d W).map_add y z, emap_add, (Λ f d W').map_add, ← hy, ← hz]
      exact map_add ((pre f d).map (homOfLE h).op).hom _ _
    | smul r y _ hy =>
      rw [(Λ f d W).map_smul r y, emap_smul, (Λ f d W').map_smul, ← hy]
      exact (pre f d).map_smul (homOfLE h).op r (show (pre f d).obj (op W) from Λ f d W y)
  exact key s (by rw [exteriorPower.ιMulti_span]; trivial)

lemma resD_top {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d (f.kaehlerPresheaf.obj (op W))) :
    resD f d h (f.topToSections d W s) = f.topToSections d W' (emap f d h s) := by
  rw [topToSections_eq, topToSections_eq, resD_unitD, preMap_Λ]

end T0

section EA

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (d : ℕ)

lemma Λext {P : Type*} [AddCommGroup P] {g₁ g₂ : ⋀[R]^d M →+ P}
    (hsmul : ∀ (r : R) (x : ⋀[R]^d M), g₁ x = g₂ x → g₁ (r • x) = g₂ (r • x))
    (h : ∀ m : Fin d → M, g₁ (exteriorPower.ιMulti R d m) = g₂ (exteriorPower.ιMulti R d m)) :
    g₁ = g₂ := by
  ext x
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R d (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact h m
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => exact hsmul r x hx

lemma Λext_apply {P : Type*} [AddCommGroup P] {g₁ g₂ : ⋀[R]^d M →+ P}
    (hsmul : ∀ (r : R) (x : ⋀[R]^d M), g₁ x = g₂ x → g₁ (r • x) = g₂ (r • x))
    (h : ∀ m : Fin d → M, g₁ (exteriorPower.ιMulti R d m) = g₂ (exteriorPower.ιMulti R d m))
    (x : ⋀[R]^d M) : g₁ x = g₂ x :=
  congrArg (fun g : ⋀[R]^d M →+ P => g x) (Λext d hsmul h)

@[reducible] def modAlong (N : Type u) [AddCommGroup N] [Module S N] : Module R N := Module.compHom N f

variable {f} in

def linAlong (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) :
    letI := modAlong f N; M →ₗ[R] N :=
  letI := modAlong f N
  { toFun := ℓ, map_add' := ℓ.map_add, map_smul' := hℓ }

variable {f} in

set_option backward.isDefEq.respectTransparency false in
def ιAlong (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) :
    letI := modAlong f (⋀[S]^d N); M [⋀^Fin d]→ₗ[R] (⋀[S]^d N) :=
  letI := modAlong f N; letI := modAlong f (⋀[S]^d N)
  letI : Algebra R S := f.toAlgebra
  haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower R S (⋀[S]^d N) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  { ((exteriorPower.ιMulti S d (M := N)).toMultilinearMap.restrictScalars R).compLinearMap
      (fun _ => linAlong ℓ hℓ) with
    map_eq_zero_of_eq' := fun v i j h hij =>
      (exteriorPower.ιMulti S d (M := N)).map_eq_zero_of_eq _ (by simp [h]) hij }

variable {f} in

def EA (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) : ⋀[R]^d M →+ ⋀[S]^d N :=
  letI := modAlong f (⋀[S]^d N)
  (exteriorPower.alternatingMapLinearEquiv (ιAlong d ℓ hℓ)).toAddMonoidHom

variable {f d} in
lemma EA_ιMulti (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) (m : Fin d → M) :
    EA d ℓ hℓ (exteriorPower.ιMulti R d m) = exteriorPower.ιMulti S d (fun i => ℓ (m i)) := by
  letI := modAlong f (⋀[S]^d N)
  show (exteriorPower.alternatingMapLinearEquiv (ιAlong d ℓ hℓ)) (exteriorPower.ιMulti R d m) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

variable {f d} in
lemma EA_smul (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) (r : R) (x : ⋀[R]^d M) :
    EA d ℓ hℓ (r • x) = f r • EA d ℓ hℓ x := by
  letI := modAlong f (⋀[S]^d N)
  exact (exteriorPower.alternatingMapLinearEquiv (ιAlong d ℓ hℓ)).map_smul r x

end EA

section TFM

variable (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
  [CommRing O] [Algebra R' O] [CommRing F] [Algebra O F] [Algebra K' F] [Algebra R' F]
  [IsScalarTower R' O F] [IsScalarTower R' K' F] (d : ℕ)

lemma kd_smul (r : O) (m : Ω[O⁄R']) :
    (KaehlerDifferential.map R' K' O F).toAddMonoidHom (r • m) =
      algebraMap O F r • (KaehlerDifferential.map R' K' O F).toAddMonoidHom m := by
  simp only [LinearMap.toAddMonoidHom_coe, map_smul]
  exact (IsScalarTower.algebraMap_smul F r _).symm

lemma topFormMap_ιMulti (ω : Fin d → Ω[O⁄R']) :
    NeronModelInfra.TopFormOrder.topFormMap R' K' O F d (exteriorPower.ιMulti O d ω) =
      exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O F (ω i)) := by
  letI := NeronModelInfra.TopFormOrder.moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  show (exteriorPower.alternatingMapLinearEquiv (NeronModelInfra.TopFormOrder.ιMultiAlong R' K' O F d))
    (exteriorPower.ιMulti O d ω) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

lemma topFormMap_smul (r : O) (x : ⋀[O]^d (Ω[O⁄R'])) :
    NeronModelInfra.TopFormOrder.topFormMap R' K' O F d (r • x) =
      algebraMap O F r • NeronModelInfra.TopFormOrder.topFormMap R' K' O F d x := by
  letI := NeronModelInfra.TopFormOrder.moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  exact (NeronModelInfra.TopFormOrder.topFormMap R' K' O F d).map_smul r x

lemma topFormMap_eq_EA (x : ⋀[O]^d (Ω[O⁄R'])) :
    NeronModelInfra.TopFormOrder.topFormMap R' K' O F d x =
      EA (f := algebraMap O F) d (KaehlerDifferential.map R' K' O F).toAddMonoidHom (kd_smul R' K' O F) x := by
  letI := NeronModelInfra.TopFormOrder.moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  refine Λext_apply d (g₁ := (NeronModelInfra.TopFormOrder.topFormMap R' K' O F d).toAddMonoidHom)
    (g₂ := EA (f := algebraMap O F) d (KaehlerDifferential.map R' K' O F).toAddMonoidHom (kd_smul R' K' O F))
    (fun r y hy => ?_) (fun m => ?_) x
  · change NeronModelInfra.TopFormOrder.topFormMap R' K' O F d (r • y) = EA _ _ _ (r • y)
    rw [topFormMap_smul, EA_smul]
    exact congrArg (algebraMap O F r • ·) hy
  · change NeronModelInfra.TopFormOrder.topFormMap R' K' O F d _ = EA _ _ _ _
    rw [topFormMap_ιMulti, EA_ιMulti]
    rfl

end TFM

end OmegaPull

namespace OmegaPull

section Main

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ)

include hφ

lemma fac (U : Y.Opens) :
    CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) =
      gY.constToPresheaf.app (op U) ≫ φ.app U := by
  have h1 : gY.constToPresheaf.app (op U) ≫ φ.app U =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (φ ≫ gY).appLE ⊤ (φ ⁻¹ᵁ U) le_top := by
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gY.appLE ⊤ U le_top) ≫ φ.app U = _
    rw [Category.assoc, ← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
  have h2 : CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))).appLE ⊤ (φ ⁻¹ᵁ U) le_top := by
    change CommRingCat.ofHom (algebraMap A B) ≫
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top) = _
    rw [Scheme.Hom.comp_appLE, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  rw [h1, h2, hφ]

lemma fac_apply (U : Y.Opens) (a : A) :
    φ.app U (gY.constToPresheaf.app (op U) a) =
      gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) (algebraMap A B a) := by
  have := CategoryTheory.ConcreteCategory.congr_hom (fac gY gX φ hφ U) a
  exact this.symm

def kdMap (U : Y.Opens) :
    gY.kaehlerPresheaf.obj (op U) ⟶
      (ModuleCat.restrictScalars (φ.app U).hom).obj (gX.kaehlerPresheaf.obj (op (φ ⁻¹ᵁ U))) :=
  CommRingCat.KaehlerDifferential.map (fac gY gX φ hφ U)

abbrev unit1 (V : X.Opens) : gX.kaehlerPresheaf.obj (op V) ⟶ gX.kaehler.val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app gX.kaehlerPresheaf).app (op V)

lemma unit1_apply (V : X.Opens) (x : gX.kaehlerPresheaf.obj (op V)) :
    unit1 gX V x = gX.kaehlerToSections V x := rfl

omit hφ in

def dK {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C)) (V : Z.Opens) (b : Γ(Z, V)) :
    (g.kaehlerPresheaf.obj (op V) : Type u) :=
  CommRingCat.KaehlerDifferential.d (f := g.constToPresheaf.app (op V)) b

omit hφ in
lemma kp_map_dK {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C))
    {V V' : Z.Opens} (i : op V ⟶ op V') (b : Γ(Z, V)) :
    g.kaehlerPresheaf.map i (dK g V b) = dK g V' (Z.presheaf.map i b) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d g.constToPresheaf i b

omit hφ in

lemma kp_hom_ext {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C)) (V : Z.Opens)
    {M : ModuleCat Γ(Z, V)} {α β : g.kaehlerPresheaf.obj (op V) ⟶ M}
    (h : ∀ b : Γ(Z, V), α (dK g V b) = β (dK g V b)) : α = β :=
  CommRingCat.KaehlerDifferential.ext h

omit hφ in

lemma map_unit1 {V V' : X.Opens} (j : op V ⟶ op V') (x : gX.kaehlerPresheaf.obj (op V)) :
    gX.kaehler.val.map j (unit1 gX V x) = unit1 gX V' (gX.kaehlerPresheaf.map j x) :=
  (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app gX.kaehlerPresheaf) j x).symm

omit hφ in
lemma φ_naturality_apply {U U' : Y.Opens} (i : op U ⟶ op U') (b : Γ(Y, U)) :
    X.presheaf.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op (φ.app U b) =
      φ.app U' (Y.presheaf.map i b) :=
  (CategoryTheory.ConcreteCategory.congr_hom (φ.naturality i) b).symm

def k1app (U : Y.Opens) :
    gY.kaehlerPresheaf.obj (op U) ⟶ ((Scheme.Modules.pushforward φ).obj gX.kaehler).val.obj (op U) :=
  kdMap gY gX φ hφ U ≫ (ModuleCat.restrictScalars (φ.app U).hom).map (unit1 gX (φ ⁻¹ᵁ U))

lemma k1app_dK (U : Y.Opens) (b : Γ(Y, U)) :
    k1app gY gX φ hφ U (dK gY U b) = unit1 gX (φ ⁻¹ᵁ U) (dK gX (φ ⁻¹ᵁ U) (φ.app U b)) := by
  show unit1 gX (φ ⁻¹ᵁ U) (CommRingCat.KaehlerDifferential.map (fac gY gX φ hφ U)
    (CommRingCat.KaehlerDifferential.d b)) = _
  rw [CommRingCat.KaehlerDifferential.map_d]
  rfl

def k1pre : gY.kaehlerPresheaf ⟶ ((Scheme.Modules.pushforward φ).obj gX.kaehler).val where
  app U := k1app gY gX φ hφ U.unop
  naturality {U U'} i := by
    obtain ⟨U⟩ := U; obtain ⟨U'⟩ := U'
    apply kp_hom_ext gY U
    intro b
    change k1app gY gX φ hφ U' (gY.kaehlerPresheaf.map i (dK gY U b)) =
      gX.kaehler.val.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op
        (k1app gY gX φ hφ U (dK gY U b))
    rw [kp_map_dK, k1app_dK, k1app_dK, map_unit1, kp_map_dK, φ_naturality_apply]

abbrev adjY := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)

def k1 : gY.kaehler ⟶ (Scheme.Modules.pushforward φ).obj gX.kaehler :=
  ((adjY (Y := Y)).homEquiv gY.kaehlerPresheaf ((Scheme.Modules.pushforward φ).obj gX.kaehler)).symm
    (k1pre gY gX φ hφ)

lemma k1_kaehlerToSections (U : Y.Opens) (x : gY.kaehlerPresheaf.obj (op U)) :
    (k1 gY gX φ hφ).app U (gY.kaehlerToSections U x) = (k1app gY gX φ hφ U x : Γ(gX.kaehler, φ ⁻¹ᵁ U)) := by
  have h := (adjY (Y := Y)).homEquiv_unit gY.kaehlerPresheaf ((Scheme.Modules.pushforward φ).obj gX.kaehler)
    (k1 gY gX φ hφ)
  rw [k1, Equiv.apply_symm_apply] at h

  have h' := congrArg (fun (q : gY.kaehlerPresheaf ⟶ _) => (q.app (op U)).hom x) h
  exact h'.symm

abbrev k1h (U : Y.Opens) : Γ(gY.kaehler, U) →+ Γ(gX.kaehler, φ ⁻¹ᵁ U) :=
  ((k1 gY gX φ hφ).app U).hom

lemma k1h_smul (U : Y.Opens) (r : Γ(Y, U)) (m : Γ(gY.kaehler, U)) :
    k1h gY gX φ hφ U (r • m) = (φ.app U).hom r • k1h gY gX φ hφ U m :=
  Scheme.Modules.Hom.app_smul (k1 gY gX φ hφ) r m

lemma map_k1h {U U' : Y.Opens} (i : op U ⟶ op U') (m : Γ(gY.kaehler, U)) :
    gX.kaehler.presheaf.map ((Opens.map φ.base).map i.unop).op (k1h gY gX φ hφ U m) =
      k1h gY gX φ hφ U' (gY.kaehler.presheaf.map i m) :=
  (PresheafOfModules.naturality_apply (k1 gY gX φ hφ).val i m).symm

abbrev unitDh (V : X.Opens) : (⋀[Γ(X, V)]^d Γ(gX.kaehler, V)) →+ Γ(gX.topDifferentials d, V) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (T0.pre gX d)).app
      (op V)).hom.toAddMonoidHom

omit hφ in
lemma unitDh_apply (V : X.Opens) (w : ⋀[Γ(X, V)]^d Γ(gX.kaehler, V)) :
    unitDh gX d V w = T0.unitD gX d V w := rfl

def kdfun (U : Y.Opens) : (⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) →+ Γ(gX.topDifferentials d, φ ⁻¹ᵁ U) :=
  (unitDh gX d (φ ⁻¹ᵁ U)).comp (EA (f := (φ.app U).hom) d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U))

lemma kdfun_apply (U : Y.Opens) (w : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) :
    kdfun gY gX φ hφ d U w =
      T0.unitD gX d (φ ⁻¹ᵁ U) (EA (f := (φ.app U).hom) d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U) w) := rfl

lemma kdfun_smul (U : Y.Opens) (r : Γ(Y, U)) (w : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) :
    kdfun gY gX φ hφ d U (r • w) = (φ.app U).hom r • kdfun gY gX φ hφ d U w := by
  rw [kdfun_apply, kdfun_apply, EA_smul, T0.unitD_smul]

lemma kdfun_ιMulti (U : Y.Opens) (m : Fin d → Γ(gY.kaehler, U)) :
    kdfun gY gX φ hφ d U (exteriorPower.ιMulti _ d m) =
      T0.unitD gX d (φ ⁻¹ᵁ U) (exteriorPower.ιMulti _ d (fun k => k1h gY gX φ hφ U (m k))) := by
  rw [kdfun_apply, EA_ιMulti]

omit hφ in

lemma map_unitD {V V' : X.Opens} (j : op V ⟶ op V') (w : ⋀[Γ(X, V)]^d Γ(gX.kaehler, V)) :
    (gX.topDifferentials d).presheaf.map j (T0.unitD gX d V w) =
      T0.unitD gX d V' (show ⋀[Γ(X, V')]^d Γ(gX.kaehler, V') from
        (T0.pre gX d).map j (show (T0.pre gX d).obj (op V) from w)) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (T0.pre gX d))).naturality j
  exact (congrArg (fun ψ => ψ.hom (show (T0.pre gX d).obj (op V) from w)) hnat).symm

abbrev L₁ {U U' : Y.Opens} (i : op U ⟶ op U') :
    (⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) →+ Γ(gX.topDifferentials d, φ ⁻¹ᵁ U') :=
  (kdfun gY gX φ hφ d U').comp ((T0.pre gY d).map i).hom.toAddMonoidHom

abbrev L₂ {U U' : Y.Opens} (i : op U ⟶ op U') :
    (⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) →+ Γ(gX.topDifferentials d, φ ⁻¹ᵁ U') :=
  ((gX.topDifferentials d).presheaf.map ((Opens.map φ.base).map i.unop).op).hom.comp (kdfun gY gX φ hφ d U)

lemma L₁_smul {U U' : Y.Opens} (i : op U ⟶ op U') (r : Γ(Y, U)) (x : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) :
    L₁ gY gX φ hφ d i (r • x) = (φ.app U').hom (Y.presheaf.map i r) • L₁ gY gX φ hφ d i x := by
  have h1 := congrArg (kdfun gY gX φ hφ d U')
    ((T0.pre gY d).map_smul i r (show (T0.pre gY d).obj (op U) from x))
  exact h1.trans (kdfun_smul gY gX φ hφ d U' _ _)

lemma L₂_smul {U U' : Y.Opens} (i : op U ⟶ op U') (r : Γ(Y, U)) (x : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) :
    L₂ gY gX φ hφ d i (r • x) = (φ.app U').hom (Y.presheaf.map i r) • L₂ gY gX φ hφ d i x := by
  show (gX.topDifferentials d).presheaf.map ((Opens.map φ.base).map i.unop).op (kdfun gY gX φ hφ d U (r • x)) = _
  rw [kdfun_smul, ← φ_naturality_apply]
  exact Scheme.Modules.map_smul _ _ _ _

lemma L₁_ιMulti {U U' : Y.Opens} (i : op U ⟶ op U') (m : Fin d → Γ(gY.kaehler, U)) :
    L₁ gY gX φ hφ d i (exteriorPower.ιMulti _ d m) =
      T0.unitD gX d (φ ⁻¹ᵁ U')
        (exteriorPower.ιMulti _ d (fun k => k1h gY gX φ hφ U' (gY.kaehler.presheaf.map i (m k)))) := by
  have h1 := congrArg (kdfun gY gX φ hφ d U') (PresheafOfModules.exteriorPower_map_ιMulti d gY.kaehler.val i m)
  exact h1.trans (kdfun_ιMulti gY gX φ hφ d U' _)

lemma L₂_ιMulti {U U' : Y.Opens} (i : op U ⟶ op U') (m : Fin d → Γ(gY.kaehler, U)) :
    L₂ gY gX φ hφ d i (exteriorPower.ιMulti _ d m) =
      T0.unitD gX d (φ ⁻¹ᵁ U')
        (exteriorPower.ιMulti _ d (fun k => k1h gY gX φ hφ U' (gY.kaehler.presheaf.map i (m k)))) := by
  show (gX.topDifferentials d).presheaf.map ((Opens.map φ.base).map i.unop).op
    (kdfun gY gX φ hφ d U (exteriorPower.ιMulti _ d m)) = _
  rw [kdfun_ιMulti, map_unitD]
  have h2 := PresheafOfModules.exteriorPower_map_ιMulti d gX.kaehler.val ((Opens.map φ.base).map i.unop).op
    (fun k => k1h gY gX φ hφ U (m k))
  refine (congrArg (T0.unitD gX d (φ ⁻¹ᵁ U')) h2).trans ?_
  congr 1; congr 1
  funext k
  exact map_k1h gY gX φ hφ i (m k)

def kdAb : (T0.pre gY d).presheaf ⟶ ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d)).val.presheaf where
  app U := AddCommGrpCat.ofHom (kdfun gY gX φ hφ d U.unop)
  naturality {U U'} i := by
    obtain ⟨U⟩ := U; obtain ⟨U'⟩ := U'
    ext1
    change L₁ gY gX φ hφ d i = L₂ gY gX φ hφ d i
    refine Λext d (fun r x hx => ?_) (fun m => ?_)
    · rw [L₁_smul, L₂_smul]; exact congrArg (_ • ·) hx
    · rw [L₁_ιMulti, L₂_ιMulti]

def kdpre : T0.pre gY d ⟶ ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d)).val :=
  PresheafOfModules.homMk (kdAb gY gX φ hφ d) (fun U r w => by
    obtain ⟨U⟩ := U
    exact kdfun_smul gY gX φ hφ d U r w)

def kd : gY.topDifferentials d ⟶ (Scheme.Modules.pushforward φ).obj (gX.topDifferentials d) :=
  ((adjY (Y := Y)).homEquiv (T0.pre gY d) ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d))).symm
    (kdpre gY gX φ hφ d)

lemma kd_unitD (U : Y.Opens) (w : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) :
    (kd gY gX φ hφ d).app U (T0.unitD gY d U w) =
      (kdfun gY gX φ hφ d U w : Γ(gX.topDifferentials d, φ ⁻¹ᵁ U)) := by
  have h := (adjY (Y := Y)).homEquiv_unit (T0.pre gY d)
    ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d)) (kd gY gX φ hφ d)
  rw [kd, Equiv.apply_symm_apply] at h
  have h' := congrArg (fun (q : T0.pre gY d ⟶ _) => (q.app (op U)).hom (show (T0.pre gY d).obj (op U) from w)) h
  exact h'.symm

def θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d :=
  ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _).symm (kd gY gX φ hφ d)

lemma θ_pullbackLocalSection (U : Y.Opens) (s : Γ(gY.topDifferentials d, U)) :
    (θ gY gX φ hφ d).app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ s) =
      ((kd gY gX φ hφ d).app U s : Γ(gX.topDifferentials d, φ ⁻¹ᵁ U)) :=
  Scheme.Modules.homEquiv_symm_app_pullbackLocalSection φ (kd gY gX φ hφ d) s

set_option maxHeartbeats 3200000 in

lemma key (U : Y.Opens) (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))) :
    letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
    letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.app U).hom.toAlgebra
    letI : Algebra A Γ(X, φ ⁻¹ᵁ U) :=
      (CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U))).hom.toAlgebra
    ∀ [IsScalarTower A B Γ(X, φ ⁻¹ᵁ U)] [IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)],
    EA (f := (φ.app U).hom) d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U)
        (exteriorPower.map d (gY.kaehlerToSectionsₗ U) η) =
      exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
        (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η) := by
  intro _ _
  letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
  letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.app U).hom.toAlgebra
  letI : Algebra A Γ(X, φ ⁻¹ᵁ U) :=
    (CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U))).hom.toAlgebra
  refine Λext_apply d
    (g₁ := (EA (f := (φ.app U).hom) d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U)).comp
      (exteriorPower.map d (gY.kaehlerToSectionsₗ U)).toAddMonoidHom)
    (g₂ := (exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))).toAddMonoidHom.comp
      (letI := NeronModelInfra.TopFormOrder.moduleAlong Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)
        (⋀[Γ(X, φ ⁻¹ᵁ U)]^d (Ω[Γ(X, φ ⁻¹ᵁ U)⁄B]))
       (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d).toAddMonoidHom))
    (fun r x hx => ?_) (fun ω => ?_) η
  · change EA d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U) (exteriorPower.map d (gY.kaehlerToSectionsₗ U) (r • x)) =
      exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
        (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d (r • x))
    rw [map_smul, EA_smul]
    have hx' : EA d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U) (exteriorPower.map d (gY.kaehlerToSectionsₗ U) x) =
        exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
          (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d x) := hx
    rw [hx']
    have hts : NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d (r • x) =
        algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) r • NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d x :=
      topFormMap_smul ..
    have hms := (exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))).map_smul ((φ.app U).hom r)
      (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d x)
    exact hms.symm.trans (congrArg (exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))) hts.symm)
  · change EA d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U)
        (exteriorPower.map d (gY.kaehlerToSectionsₗ U) (exteriorPower.ιMulti _ d ω)) =
      exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
        (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d (exteriorPower.ιMulti _ d ω))
    rw [exteriorPower.map_apply_ιMulti, EA_ιMulti, topFormMap_ιMulti]
    refine Eq.trans ?_ (exteriorPower.map_apply_ιMulti (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
      (fun i => KaehlerDifferential.map A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) (ω i))).symm
    congr 1
    funext i
    change k1h gY gX φ hφ U (gY.kaehlerToSections U (ω i)) =
      gX.kaehlerToSections (φ ⁻¹ᵁ U) (KaehlerDifferential.map A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) (ω i))
    refine (k1_kaehlerToSections gY gX φ hφ U (ω i)).trans ?_
    rfl

omit hφ in

lemma emap_eq_topFormMap {V W : X.Opens} (h : W ≤ V) (z : ⋀[Γ(X, V)]^d (gX.kaehlerPresheaf.obj (op V))) :
    letI := gX.sectionsAlgebra V; letI := gX.sectionsAlgebra W
    letI : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    ∀ [IsScalarTower B Γ(X, V) Γ(X, W)],
    T0.emap gX d h z = NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d z := by
  intro _
  letI := gX.sectionsAlgebra V; letI := gX.sectionsAlgebra W
  letI : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  refine Λext_apply d
    (g₁ := ((T0.preK gX d).map (homOfLE h).op).hom.toAddMonoidHom)
    (g₂ := (letI := NeronModelInfra.TopFormOrder.moduleAlong Γ(X, V) Γ(X, W) (⋀[Γ(X, W)]^d (Ω[Γ(X, W)⁄B]))
       (NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d).toAddMonoidHom))
    (fun r x hx => ?_) (fun ω => ?_) z
  · have hx' : T0.emap gX d h x = NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d x := hx
    change T0.emap gX d h (r • x) = NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d (r • x)
    refine (T0.emap_smul gX d h r x).trans ?_
    rw [hx']
    have hts : NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d (r • x) =
        algebraMap Γ(X, V) Γ(X, W) r • NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d x :=
      topFormMap_smul ..
    exact hts.symm
  · change T0.emap gX d h (exteriorPower.ιMulti _ d ω) =
      NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d (exteriorPower.ιMulti _ d ω)
    rw [T0.emap_ιMulti, topFormMap_ιMulti]
    rfl

omit hφ in
lemma tower_sections {V W : X.Opens} (h : W ≤ V) :
    letI := gX.sectionsAlgebra V; letI := gX.sectionsAlgebra W
    letI : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsScalarTower B Γ(X, V) Γ(X, W) := by
  letI := gX.sectionsAlgebra V; letI := gX.sectionsAlgebra W
  letI : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun b => ?_
  have := gX.constToPresheaf.naturality (homOfLE h).op
  have h' := congrArg (fun ψ => ψ.hom b) this
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp,
    ] at h'
  exact h'

theorem main :
    ∃ θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d,
      ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η) := by
  refine ⟨θ gY gX φ hφ d, ?_⟩
  intro U _ W _ hWU instAW instABW instAYW η

  letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W; letI := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
  letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.app U).hom.toAlgebra
  letI : Algebra A Γ(X, φ ⁻¹ᵁ U) :=
    (CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U))).hom.toAlgebra
  haveI : IsScalarTower A B Γ(X, φ ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (fac gY gX φ hφ U))
  letI : Algebra Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  haveI : IsScalarTower Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower B Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := tower_sections gX hWU

  rw [θ_pullbackLocalSection, T0.topToSections_eq, kd_unitD, kdfun_apply, key gY gX φ hφ d U η,
    ← T0.topToSections_eq]
  change T0.resD gX d hWU (gX.topToSections d (φ ⁻¹ᵁ U)
    (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η)) = _
  rw [T0.resD_top, emap_eq_topFormMap gX d hWU]
  have hA : NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, φ ⁻¹ᵁ U) Γ(X, W) d
      (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η) =
      NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η :=
    NeronModelInfra.TopFormOrder.topFormMap_topFormMap ..
  exact congrArg (gX.topToSections d W) hA

end Main

end OmegaPull

end

theorem solution
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ) :
    ∃ θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d,
      ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η) :=
  OmegaPull.main gY gX φ hφ d

end S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq (solution)
