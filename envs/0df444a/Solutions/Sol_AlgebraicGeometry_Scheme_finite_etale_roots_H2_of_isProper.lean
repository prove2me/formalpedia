-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_etale_roots_H2_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-18T22:24:44.221587+00:00
-- url     : https://prove2.me/submissions/e1e88112-fdbd-4698-b610-eedc70cd6e81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallEtaleUnits
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_constant_etale_cohomology_of_isProper

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PhilipponTorsorSectionExactness
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]

def evaluation (U : Cᵒᵖ) : Sheaf J AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U

/-- Taking sections of a short exact sequence preserves the kernel
condition even when the last section map need not be surjective. -/
theorem exact_on_sections (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (hS : S.ShortExact) (U : Cᵒᵖ) :
    Function.Exact (S.f.hom.app U) (S.g.hom.app U) := by
  let E := evaluation (J := J) U
  letI : PreservesLimits E := inferInstanceAs (PreservesLimits
    (sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U))
  letI : E.PreservesZeroMorphisms := inferInstanceAs
    ((sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U).PreservesZeroMorphisms)
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (hS.exact.map_of_mono_of_preservesKernel E hS.mono_f (by infer_instance))

theorem injective_on_sections (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))
    (hS : S.ShortExact) (U : Cᵒᵖ) : Function.Injective (S.f.hom.app U) := by
  letI := hS.mono_f
  letI : Mono S.f.hom := inferInstanceAs (Mono ((sheafToPresheaf J AddCommGrpCat).map S.f))
  exact (AddCommGrpCat.mono_iff_injective _).mp (inferInstance : Mono (S.f.hom.app U))

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- Choose an actual injective presentation and its cokernel in the
abelian category of sheaves. -/
def injectiveSequence (G : Sheaf J AddCommGrpCat.{w}) : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G)) (cokernel.condition _)

instance (G : Sheaf J AddCommGrpCat.{w}) : Injective (injectiveSequence G).X₂ :=
  inferInstanceAs (Injective (Injective.under G))

theorem injectiveSequence_shortExact (G : Sheaf J AddCommGrpCat.{w}) :
    (injectiveSequence G).ShortExact := by
  letI : Mono (injectiveSequence G).f := inferInstanceAs (Mono (Injective.ι G))
  letI : Epi (injectiveSequence G).g := inferInstanceAs (Epi (cokernel.π (Injective.ι G)))
  exact { exact := ShortComplex.exact_cokernel (Injective.ι G) }

end PhilipponTorsorSectionExactness
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponKummerSequence

namespace PhilipponEtaleRootsSections
universe u

theorem power_apply {X : Scheme.{u}} (n : ℕ) (U : X.Etale)
    (a : (units X).obj.obj (op U)) : (power X n).hom.app (op U) a = n • a := by
  change ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat).map (power X n)).app (op U) a = _
  rw [power, Functor.map_nsmul, NatTrans.app_nsmul,
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat).map_id]
  rfl

/-- The sections of the actual kernel sheaf on an étale object are the
roots of unity in that object's ring of global sections. -/
def sections (X : Scheme.{u}) (n : ℕ) (U : X.Etale) :
    (roots X n).obj.obj (op U) ≃+ Additive (rootsOfUnity n Γ(U.left, ⊤)) := by
  let E := PhilipponTorsorSectionExactness.evaluation (J := X.smallEtaleTopology) (op U)
  letI : PreservesLimits E := inferInstanceAs (PreservesLimits
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat).obj (op U)))
  letI : E.PreservesZeroMorphisms := inferInstanceAs
    ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat).obj (op U)).PreservesZeroMorphisms)
  let e := PreservesKernel.iso E (power X n) ≪≫ AddCommGrpCat.kernelIsoKer (E.map (power X n))
  refine e.addCommGroupIsoToAddEquiv.trans ?_
  refine
    { toFun := fun a => Additive.ofMul ⟨Additive.toMul a.val, ?_⟩
      invFun := fun a => ⟨Additive.ofMul a.toMul.val, ?_⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun a => Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  · have ha := a.property
    change (power X n).hom.app (op U) a.val = 0 at ha
    rw [power_apply] at ha
    exact ha
  · change (power X n).hom.app (op U) (Additive.ofMul a.toMul.val) = 0
    rw [power_apply]
    exact a.toMul.property

/-- Finiteness for a constant finite coefficient sheaf transfers across
an isomorphism to the roots of unity sheaf. -/
theorem finite_H2_of_constant_iso (X : Scheme.{u}) (n : ℕ) (A : AddCommGrpCat.{u})
    (i : roots X n ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat).obj A)
    [Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj A).H 2)] :
    Finite ((roots X n).H 2) := by
  let e : (roots X n).H 2 ≃+ ((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj A).H 2 :=
    ((Sheaf.functorH X.smallEtaleTopology 2).mapIso i).addCommGroupIsoToAddEquiv
  exact Finite.of_injective e e.injective

end PhilipponEtaleRootsSections
end
end

section
set_option autoImplicit false
noncomputable section

open Polynomial

namespace PhilipponRootsOverLocalAlgebra
universe u v

/-- In a local algebra over an algebraically closed field, every root of
unity of invertible order is the image of a root in the base field. -/
theorem exists_scalar_root {K : Type u} [Field K] [IsAlgClosed K]
    {R : Type v} [CommRing R] [IsLocalRing R] (f : K →+* R)
    {n : ℕ} (hn : IsUnit (n : R)) (x : R) (hx : x ^ n = 1) :
    ∃ a : K, a ^ n = 1 ∧ f a = x := by
  classical
  have hnK : (n : K) ≠ 0 := by
    intro e
    have e' := congrArg f e
    rw [map_natCast, map_zero] at e'
    exact not_isUnit_zero (e' ▸ hn)
  have hn0 : n ≠ 0 := by intro e; exact hnK (by simp [e])
  let p : K[X] := X ^ n - C 1
  have hmonic : p.Monic := monic_X_pow_sub_C 1 hn0
  have hsep : p.Separable := separable_X_pow_sub_C 1 hnK one_ne_zero
  let : Algebra K R := f.toAlgebra
  have hval : aeval x p = 0 := by simp [p, hx]
  have hfact := (IsAlgClosed.splits p).eq_prod_roots_of_monic hmonic
  have hnu : ¬ IsUnit (aeval x (p.roots.map (X - C ·)).prod) := by
    rw [← hfact, hval]
    exact not_isUnit_zero
  obtain ⟨a, ha, haroot⟩ := spectrum.exists_mem_of_not_isUnit_aeval_prod hnu
  have hna : ¬ IsUnit (x - f a) := by
    rw [spectrum.mem_iff, ← IsUnit.sub_iff] at ha
    exact ha
  have hamem : a ∈ p.roots := (mem_roots hmonic.ne_zero).mpr haroot
  have hother (b : K) (hb : b ∈ p.roots.erase a) : IsUnit (x - f b) := by
    have hab : b ≠ a := ((nodup_roots hsep).mem_erase_iff.mp hb).1
    have hd : IsUnit (x - f a + -(x - f b)) := by
      have he : x - f a + -(x - f b) = f (b - a) := by rw [map_sub]; ring
      rw [he]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab)).map f
    simpa only [neg_neg] using ((IsLocalRing.isUnit_or_isUnit_of_isUnit_add hd).resolve_left hna).neg
  have hfactors :
      IsUnit (((p.roots.erase a).map (fun b => x - f b)).prod) := by
    rw [← Multiset.prod_toList]
    apply List.prod_isUnit
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_toList.mp hz)
    exact hother b hb
  have hz : (p.roots.map (fun b => x - f b)).prod = 0 := by
    rw [hfact, map_multiset_prod, Multiset.map_map] at hval
    have ht (b : K) : algebraMap K R b = f b := rfl
    simpa only [Function.comp_def, map_sub, aeval_X, aeval_C, ht] using hval
  rw [← Multiset.prod_map_erase (f := fun b => x - f b) hamem] at hz
  have hxa : x - f a = 0 := hfactors.mul_left_inj.mp (hz.trans (zero_mul _).symm)
  exact ⟨a, by simpa [p, sub_eq_zero] using haroot, (sub_eq_zero.mp hxa).symm⟩

end PhilipponRootsOverLocalAlgebra
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PhilipponSchemeScalarRoots
universe u

/-- A root of unity in the global sections of a scheme over an
algebraically closed field is locally a scalar when its order is invertible. -/
theorem exists_open_of_pow_eq_one {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} (s : K →+* Γ(Y, ⊤)) {n : ℕ} (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(Y, ⊤))) (a : Γ(Y, ⊤)ˣ) (ha : a ^ n = 1) (y : Y) :
    ∃ (V : Y.Opens), y ∈ V ∧ ∃ r : rootsOfUnity n K,
      Units.map V.ι.appTop.hom.toMonoidHom a =
        Units.map ((V.ι.appTop.hom.comp s).toMonoidHom) r.val := by
  let g := (Y.presheaf.germ ⊤ y trivial).hom
  have hg : IsUnit (n : Y.presheaf.stalk y) := by
    simpa only [map_natCast] using hu.map g
  have hp : g (a : Γ(Y, ⊤)) ^ n = 1 := by
    have h := congrArg (fun b : Γ(Y, ⊤)ˣ => g (b : Γ(Y, ⊤))) ha
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] using h
  obtain ⟨c, hc, hc'⟩ := PhilipponRootsOverLocalAlgebra.exists_scalar_root
    (g.comp s) hg (g a.val) hp
  let : NeZero n := ⟨hn⟩
  let r : rootsOfUnity n K := rootsOfUnity.mkOfPowEq c hc
  obtain ⟨V, hyV, i, j, h⟩ := Y.presheaf.germ_eq y (show y ∈ (⊤ : Y.Opens) from trivial)
    (show y ∈ (⊤ : Y.Opens) from trivial) a.val (s c) hc'.symm
  change Y.Opens at V
  refine ⟨V, hyV, r, Units.ext ?_⟩
  change V.ι.appTop a.val = V.ι.appTop (s c)
  let k : V.ι ''ᵁ ⊤ ⟶ V := eqToHom V.ι_image_top
  have h' := congrArg (Y.presheaf.map k.op).hom h
  change Y.presheaf.map k.op (Y.presheaf.map i.op a.val) =
    Y.presheaf.map k.op (Y.presheaf.map j.op (s c)) at h'
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp] at h'
  rw [Scheme.Opens.ι_appTop]
  exact (Subsingleton.elim (k ≫ i) (homOfLE le_top)) ▸
    (Subsingleton.elim (k ≫ j) (homOfLE le_top)) ▸ h'

end PhilipponSchemeScalarRoots
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponKummerSequence PhilipponEtaleRootsSections

namespace PhilipponEtaleRootsScalarMap
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))

/-- The scalar homomorphism on the global sections of an object of the
small étale site. -/
def scalar (U : X.Etale) : CommRingCat.of K ⟶ Γ(U.left, ⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv ≫ (U.hom ≫ π).appTop

@[reassoc]
theorem scalar_naturality {U V : X.Etale} (f : V ⟶ U) :
    scalar π U ≫ f.left.appTop = scalar π V := by
  rw [scalar, scalar, Category.assoc, ← Scheme.Hom.comp_appTop,
    ← Category.assoc, MorphismProperty.Over.w f]

/-- The finite coefficient group before sheafification. -/
def coefficient (K : Type u) [Field K] (n : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Additive (rootsOfUnity n K))

def constantUnits (n : ℕ) :
    (Functor.const X.Etaleᵒᵖ).obj (coefficient K n) ⟶ (units X).obj where
  app U := AddCommGrpCat.ofHom
    (((Units.map (scalar π U.unop).hom.toMonoidHom).comp (Subgroup.subtype _)).toAdditive)
  naturality U V f := by
    apply AddCommGrpCat.ext
    intro a
    change Additive (rootsOfUnity n K) at a
    change Additive.ofMul (Units.map (scalar π V.unop).hom.toMonoidHom a.toMul.val) =
      Additive.ofMul (Units.map f.unop.left.appTop.hom.toMonoidHom
        (Units.map (scalar π U.unop).hom.toMonoidHom a.toMul.val))
    apply Additive.ofMul.injective.eq_iff.mpr
    apply Units.ext
    exact (ConcreteCategory.congr_hom (scalar_naturality π f.unop) (a.toMul.val : K)).symm

theorem constantUnits_power (n : ℕ) : constantUnits π n ≫ (power X n).hom = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  change Additive (rootsOfUnity n K) at a
  change (power X n).hom.app (op U.unop) ((constantUnits π n).app (op U.unop) a) = 0
  rw [power_apply]
  change (Units.map (scalar π U.unop).hom.toMonoidHom a.toMul.val) ^ n = 1
  rw [← map_pow, (mem_rootsOfUnity n _).mp a.toMul.property, map_one]

/-- The natural map from constant scalar roots into the exact kernel
used by the Kummer sequence. -/
def constantRoots (n : ℕ) :
    (Functor.const X.Etaleᵒᵖ).obj (coefficient K n) ⟶ (roots X n).obj :=
  kernel.lift (power X n).hom (constantUnits π n) (constantUnits_power π n) ≫
    (PreservesKernel.iso (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat) (power X n)).inv

@[reassoc]
theorem constantRoots_comp (n : ℕ) :
    constantRoots π n ≫ (kernel.ι (power X n)).hom = constantUnits π n := by
  let F := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat
  change (kernel.lift (power X n).hom (constantUnits π n) (constantUnits_power π n) ≫
    (PreservesKernel.iso F (power X n)).inv) ≫ F.map (kernel.ι (power X n)) = _
  rw [Category.assoc, PreservesKernel.iso_inv_ι]
  exact kernel.lift_ι _ _ _

theorem roots_incl_injective (n : ℕ) (U : X.Etale) :
    Function.Injective ((kernel.ι (power X n)).hom.app (op U)) := by
  let : Mono (kernel.ι (power X n)).hom := inferInstanceAs
    (Mono ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat).map (kernel.ι (power X n))))
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

theorem constantRoots_ι (n : ℕ) (U : X.Etale) (a : Additive (rootsOfUnity n K)) :
    (kernel.ι (power X n)).hom.app (op U) ((constantRoots π n).app (op U) a) =
      Additive.ofMul (Units.map (scalar π U).hom.toMonoidHom a.toMul.val) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (constantRoots_comp π n) (op U)) a

end PhilipponEtaleRootsScalarMap
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponKummerSequence PhilipponEtaleRootsScalarMap

namespace PhilipponEtaleRootsConstant
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))

theorem locally_injective (n : ℕ) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantRoots π n) := by
  constructor
  intro U a b hab
  let W : U.unop.left → X.Etale := fun _ => U.unop
  let f (x : U.unop.left) : W x ⟶ U.unop := 𝟙 _
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W f) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    have h := congrArg ((kernel.ι (power X n)).hom.app (op U.unop)) hab
    change (kernel.ι (power X n)).hom.app (op U.unop) ((constantRoots π n).app (op U.unop) a) =
      (kernel.ι (power X n)).hom.app (op U.unop) ((constantRoots π n).app (op U.unop) b) at h
    rw [constantRoots_ι, constantRoots_ι] at h
    change Additive (rootsOfUnity n K) at a b
    let g := (U.unop.left.presheaf.germ ⊤ x trivial).hom.comp (scalar π U.unop).hom
    have h' : g (a.toMul.val : K) = g (b.toMul.val : K) :=
      congrArg (fun z : Additive (Γ(U.unop.left, ⊤)ˣ) =>
        (U.unop.left.presheaf.germ ⊤ x trivial).hom (z.toMul : Γ(U.unop.left, ⊤))) h
    change a = b
    exact Additive.toMul.injective (rootsOfUnity.coe_injective (g.injective h'))
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, x, rfl⟩

variable [IsAlgClosed K]

theorem locally_surjective (n : ℕ) (hn : n ≠ 0) (hu : IsUnit (n : Γ(X, ⊤))) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantRoots π n) := by
  constructor
  intro U a
  let α : Γ(U.left, ⊤)ˣ := ((kernel.ι (power X n)).hom.app (op U) a :
    Additive (Γ(U.left, ⊤)ˣ)).toMul
  have hα : α ^ n = 1 := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f => f.hom) (kernel.condition (power X n))) (op U)) a
    change (power X n).hom.app (op U) ((kernel.ι (power X n)).hom.app (op U) a) = 0 at h
    rw [PhilipponEtaleRootsSections.power_apply] at h
    exact h
  have hu' : IsUnit (n : Γ(U.left, ⊤)) := by
    simpa only [map_natCast] using hu.map U.hom.appTop.hom
  choose V hx r hr using fun x : U.left =>
    PhilipponSchemeScalarRoots.exists_open_of_pow_eq_one (scalar π U).hom hn hu' α hα x
  let W (x : U.left) : X.Etale := Scheme.Etale.mk ((V x).ι ≫ U.hom)
  let f (x : U.left) : W x ⟶ U := MorphismProperty.Over.homMk (V x).ι rfl trivial
  refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows W f) ?_ ?_
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    refine ⟨Additive.ofMul (r x), roots_incl_injective n (W x) ?_⟩
    rw [constantRoots_ι, NatTrans.naturality_apply (kernel.ι (power X n)).hom (f x).op]
    have h := ConcreteCategory.congr_hom (scalar_naturality π (f x)) (r x).val.val
    change (V x).ι.appTop (scalar π U (r x).val.val) = scalar π (W x) (r x).val.val at h
    apply congrArg Additive.ofMul
    apply Units.ext
    change scalar π (W x) (r x).val.val = (V x).ι.appTop α.val
    exact h.symm.trans (congrArg Units.val (hr x)).symm
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, ⟨x, hx x⟩, rfl⟩

/-- The published small étale roots-of-unity sheaf over an algebraically
closed field is isomorphic to the constant sheaf of scalar roots. -/
def constant_iso (n : ℕ) (hn : n ≠ 0) (hu : IsUnit (n : Γ(X, ⊤))) :
    roots X n ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat).obj (coefficient K n) := by
  letI := locally_injective π n
  letI := locally_surjective π n hn hu
  have h := X.smallEtaleTopology.W_of_isLocallyBijective (constantRoots π n)
  letI := (X.smallEtaleTopology.W_iff (constantRoots π n)).mp h
  exact (asIso ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat).map (constantRoots π n)) ≪≫
    asIso ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat).counit.app (roots X n))).symm

end PhilipponEtaleRootsConstant
end
end

section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory PhilipponEtaleRootsScalarMap
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤))) : Finite ((PhilipponKummerSequence.roots X n).H 2) := by
  let : NeZero n := ⟨hn⟩
  let : Finite (coefficient K n) := inferInstanceAs (Finite (rootsOfUnity n K))
  let : Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj (coefficient K n)).H 2) :=
    AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_isProper K π (coefficient K n) 2
  exact PhilipponEtaleRootsSections.finite_H2_of_constant_iso X n (coefficient K n)
    (PhilipponEtaleRootsConstant.constant_iso π n hn hu)

end
