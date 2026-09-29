-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.map_topToSections_eq_topToSections_topFormMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/aaf618d0-5c87-59e4-a027-a31ad1796cc3

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace BenchOTN

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

lemma pmap_d {W W' : X.Opens} (h : W' ≤ W) (x : X.presheaf.obj (op W)) :
    pmap f h (CommRingCat.KaehlerDifferential.d x) =
      CommRingCat.KaehlerDifferential.d (X.presheaf.map (homOfLE h).op x) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d f.constToPresheaf (homOfLE h).op x

theorem topFormMap_ιMulti (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O] [Algebra R' O] [CommRing F] [Algebra O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F] (n : ℕ) (v : Fin n → Ω[O⁄R']) :
    NeronModelInfra.TopFormOrder.topFormMap R' K' O F n (exteriorPower.ιMulti O n v) =
      exteriorPower.ιMulti F n (fun i => KaehlerDifferential.map R' K' O F (v i)) := by
  letI := NeronModelInfra.TopFormOrder.moduleAlong O F (⋀[F]^n (Ω[F⁄K']))
  show exteriorPower.alternatingMapLinearEquiv (NeronModelInfra.TopFormOrder.ιMultiAlong R' K' O F n)
    (exteriorPower.ιMulti O n v) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

section restr

variable {W W' : X.Opens} (h : W' ≤ W)

lemma pmap_eq_map :
    letI := f.sectionsAlgebra W; letI := f.sectionsAlgebra W'
    letI : Algebra (X.presheaf.obj (op W)) (X.presheaf.obj (op W')) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    ∀ [IsScalarTower A (X.presheaf.obj (op W)) (X.presheaf.obj (op W'))]
      (w : Ω[(X.presheaf.obj (op W))⁄A]),
      pmap f h w = KaehlerDifferential.map A A (X.presheaf.obj (op W)) (X.presheaf.obj (op W')) w := by
  intro _ w
  letI := f.sectionsAlgebra W; letI := f.sectionsAlgebra W'
  letI : Algebra (X.presheaf.obj (op W)) (X.presheaf.obj (op W')) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  have hw : w ∈ Submodule.span (X.presheaf.obj (op W)) (Set.range (KaehlerDifferential.D A (X.presheaf.obj (op W)))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨x, rfl⟩ := hy
      rw [KaehlerDifferential.map_D]
      exact pmap_d f h x
  | zero =>
      rw [map_zero]; exact map_zero (f.kaehlerPresheaf.map (homOfLE h).op).hom
  | add y z _ _ hy hz =>
      rw [map_add, ← hy, ← hz]; exact map_add (f.kaehlerPresheaf.map (homOfLE h).op).hom _ _
  | smul r y _ hy =>
      rw [LinearMap.map_smul, ← hy,
        ← algebraMap_smul (A := X.presheaf.obj (op W')) (M := Ω[(X.presheaf.obj (op W'))⁄A]) r (pmap f h y)]
      exact (f.kaehlerPresheaf).map_smul (homOfLE h).op r y

set_option maxHeartbeats 3200000 in

lemma emap_eq_topFormMap :
    letI := f.sectionsAlgebra W; letI := f.sectionsAlgebra W'
    letI : Algebra (X.presheaf.obj (op W)) (X.presheaf.obj (op W')) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    ∀ [IsScalarTower A (X.presheaf.obj (op W)) (X.presheaf.obj (op W'))]
      (s : ⋀[X.presheaf.obj (op W)]^d (f.kaehlerPresheaf.obj (op W))),
      emap f d h s = NeronModelInfra.TopFormOrder.topFormMap A A (X.presheaf.obj (op W)) (X.presheaf.obj (op W')) d s := by
  intro _ s
  letI := f.sectionsAlgebra W; letI := f.sectionsAlgebra W'
  letI : Algebra (X.presheaf.obj (op W)) (X.presheaf.obj (op W')) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI := NeronModelInfra.TopFormOrder.moduleAlong (X.presheaf.obj (op W)) (X.presheaf.obj (op W'))
    (⋀[X.presheaf.obj (op W')]^d (Ω[(X.presheaf.obj (op W'))⁄A]))
  have hs : s ∈ Submodule.span (X.presheaf.obj (op W))
      (Set.range (exteriorPower.ιMulti (X.presheaf.obj (op W)) d (M := (f.kaehlerPresheaf.obj (op W) : Type u)))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hs using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [emap_ιMulti]
      erw [topFormMap_ιMulti]
      congr 1
      all_goals (funext k; exact pmap_eq_map f h (m k))
  | zero =>
      have e0 : emap f d h 0 = 0 := map_zero ((preK f d).map (homOfLE h).op).hom
      rw [e0]
      exact (map_zero (NeronModelInfra.TopFormOrder.topFormMap A A (X.presheaf.obj (op W))
        (X.presheaf.obj (op W')) d)).symm
  | add y z _ _ hy hz =>
      rw [emap_add, hy, hz]
      exact (map_add (NeronModelInfra.TopFormOrder.topFormMap A A (X.presheaf.obj (op W))
        (X.presheaf.obj (op W')) d) y z).symm
  | smul r y _ hy =>
      rw [emap_smul, hy]
      exact (LinearMap.map_smul (NeronModelInfra.TopFormOrder.topFormMap A A (X.presheaf.obj (op W))
        (X.presheaf.obj (op W')) d) r y).symm

end restr

end BenchOTN

theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U W : X.Opens} (hWU : W ≤ U) :
    letI := f.sectionsAlgebra U; letI := f.sectionsAlgebra W
    letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    ∀ [IsScalarTower A Γ(X, U) Γ(X, W)] (η : ⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U))),
      (f.topDifferentials d).presheaf.map (homOfLE hWU).op (f.topToSections d U η) =
        f.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A A Γ(X, U) Γ(X, W) d η) := by
  intro _ η
  exact (BenchOTN.resD_top f d hWU η).trans (congrArg (f.topToSections d W) (BenchOTN.emap_eq_topFormMap f d hWU η))

end S_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap (solution)
