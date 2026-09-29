-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/88d72d13-62c3-5271-b70d-63e405cb3996

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Theorems.Thm_AlgebraicGeometry_exists_etale_of_formallyUnramified_stalkMap
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero

set_option maxHeartbeats 1600000

p2m_open "AlgebraicCurve AlgebraicGeometry P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing"

universe u

set_option synthInstance.maxHeartbeats 800000

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp ext_of_fromSpecResidueField_eq IsLocallyNoetherian LocallyOfFiniteType.stalkMap Surjective Scheme.Hom.germ_stalkMap_assoc IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom pointOfClosedPoint_apply pointOfClosedPoint Scheme.SpecMap_stalkSpecializes_fromSpecStalk UniversallyClosed LocallyOfFiniteType Spec Spec.map Scheme Smooth LocallyOfFiniteType.jacobsonSpace UniversallyOpen IsZariskiLocalAtSource Scheme.stalkClosedPointTo Spec.map_injective pointOfClosedPoint_comp IsReduced locallyOfFiniteType_of_comp IsSeparated Scheme.Spec_stalkClosedPointTo_fromSpecStalk morphismRestrict_ι_assoc Spec.map_id Etale SpecToEquivOfLocalRing_symm_apply IsProper.of_comp Scheme.SpecMap_stalkMap_fromSpecStalk Spec_closedPoint IsNoetherian FormallyUnramified SpecToEquivOfLocalRing_eq_iff Scheme.Hom.germ_stalkMap SpecToEquivOfLocalRing Spec.fromSpecStalk_eq range_eq_univ Scheme.ΓSpecIso IsZariskiLocalAtSource.of_iSup_eq_top isReduced_of_smooth_of_field exists_etale_of_formallyUnramified_stalkMap"
p2m_open "AlgebraicGeometry"

theorem surjective_of_universallyOpen_of_universallyClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyOpen f] [UniversallyClosed f]
    [Nonempty X] [PreconnectedSpace Y] : Surjective f := by
  refine ⟨?_⟩
  have hc : IsClopen (Set.range f.base) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  exact Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))

theorem exists_comp_eq_of_surjective_of_isAlgClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [LocallyOfFiniteType f]
    {L : Type u} [Field L] [IsAlgClosed L] (p : Spec (.of L) ⟶ Y) :
    ∃ q : Spec (.of L) ⟶ X, q ≫ f = p := by
  have : JacobsonSpace ↥(pullback f p) := LocallyOfFiniteType.jacobsonSpace (pullback.snd f p)
  have hne : (Set.univ : Set ↥(pullback f p)).Nonempty := by
    have : Surjective (pullback.snd f p) := inferInstance
    obtain ⟨x, -⟩ := this.surj (IsLocalRing.closedPoint L); exact ⟨x, trivial⟩
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  refine ⟨pointOfClosedPoint (pullback.snd f p) x hx ≫ pullback.fst f p, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

theorem ext_of_forall_comp_eq_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [IsReduced X]
    {f g : X ⟶ Y} (sY : Y ⟶ Z) [IsSeparated sY] (hfg : f ≫ sY = g ≫ sY)
    (h : ∀ σ : Spec (.of K) ⟶ X, σ ≫ sX = 𝟙 _ → σ ≫ f = σ ≫ g) : f = g := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  refine ext_of_fromSpecResidueField_eq f g sY (closedPoints X) ?_ ?_ hfg
  · rw [dense_iff_closure_eq, ← Set.univ_inter (closedPoints X)]
    exact JacobsonSpace.closure_inter_closedPoints isClosed_univ
  · intro x hx
    have hx' : IsClosed ({x} : Set X) := hx
    have := h (pointOfClosedPoint sX x hx') (pointOfClosedPoint_comp sX x hx')
    simpa only [pointOfClosedPoint, Category.assoc, cancel_epi] using this

@[reassoc]
theorem comp_pullbackLift {W X Y Z T : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (s : T ⟶ W) (a : W ⟶ X) (b : W ⟶ Y) (w : a ≫ f = b ≫ g) :
    s ≫ pullback.lift a b w =
      pullback.lift (s ≫ a) (s ≫ b) (by rw [Category.assoc, Category.assoc, w]) := by
  ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

theorem JPHead.formallyUnramified_of_surjective_cotangent
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing S] (f : R →+* S) [IsLocalHom f] (hf : f.EssFiniteType)
    (hres : ∀ s : S, ∃ r : R, s - f r ∈ maximalIdeal S)
    (hcot : ∀ x ∈ maximalIdeal S, ∃ y ∈ maximalIdeal R, x - f y ∈ (maximalIdeal S) ^ 2) :
    f.FormallyUnramified := by
  algebraize [f]
  have hloc : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have hsep : Algebra.IsSeparable (ResidueField R) (ResidueField S) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, hr⟩ := hres s
    have : residue S s = algebraMap (ResidueField R) (ResidueField S) (residue R r) := by
      rw [IsLocalRing.ResidueField.algebraMap_residue, ← sub_eq_zero, ← map_sub,
        IsLocalRing.residue_eq_zero_iff]
      exact hr
    rw [this]
    exact isSeparable_algebraMap _
  have hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
    apply le_antisymm
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
      rw [Ideal.mem_comap]
      simp only [mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun h ↦ ha (isUnit_of_map_unit (algebraMap R S) a h)
    · have hFG : (maximalIdeal S).FG := IsNoetherian.noetherian _
      refine Submodule.le_of_le_smul_of_le_jacobson_bot hFG (maximalIdeal_le_jacobson ⊥) ?_
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hcot x hx
      have : x = algebraMap R S y + (x - algebraMap R S y) := by ring
      rw [this]
      refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hy) ?_
      rw [Ideal.smul_eq_mul, ← pow_two]
      exact hxy
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmap

section TSZE
variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
  [IsCentralScalar K V]

scoped instance : IsLocalRing (TrivSqZeroExt K V) := by
  have : Nontrivial (TrivSqZeroExt K V) := (TrivSqZeroExt.fstHom K K V).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  by_cases h : a.fst = 0
  · right
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h,
      sub_zero]
    exact isUnit_one
  · left
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (Ne.isUnit h)

theorem TrivSqZeroExt.isUnit_iff_fst_ne_zero (a : TrivSqZeroExt K V) : IsUnit a ↔ a.fst ≠ 0 := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]

omit [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
theorem TrivSqZeroExt.snd_nsmul' (n : ℕ) (z : TrivSqZeroExt K V) : (n • z).snd = n • z.snd := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, TrivSqZeroExt.snd_add, ih]

abbrev Λ : CommRingCat.{u} := CommRingCat.of (TrivSqZeroExt K V)

variable {K V}
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

noncomputable abbrev Λmap (f : V →ₗ[K] W) : Λ K V ⟶ Λ K W :=
  CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom

noncomputable abbrev Λfst : Λ K V ⟶ CommRingCat.of K :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom

noncomputable abbrev Λinl : CommRingCat.of K ⟶ Λ K V :=
  CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K V))

scoped instance (f : V →ₗ[K] W) : IsLocalHom (Λmap f).hom := by
  constructor
  intro a ha
  simp only [TrivSqZeroExt.isUnit_iff_fst_ne_zero] at ha ⊢
  simpa using ha

scoped instance : IsLocalHom (Λfst (K := K) (V := V)).hom := by
  constructor
  intro a ha
  simp only [TrivSqZeroExt.isUnit_iff_fst_ne_zero]
  simpa [isUnit_iff_ne_zero] using ha

variable {P : Type u} [AddCommGroup P] [Module K P] [Module Kᵐᵒᵖ P] [IsCentralScalar K P]

theorem Λmap_id : Λmap (LinearMap.id : V →ₗ[K] V) = 𝟙 _ := by
  ext1; simp [TrivSqZeroExt.map_id]

theorem Λmap_comp (f : V →ₗ[K] W) (g : W →ₗ[K] P) : Λmap f ≫ Λmap g = Λmap (g ∘ₗ f) := by
  ext x <;> simp [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]

theorem Λmap_zero : Λmap (0 : V →ₗ[K] W) = Λfst ≫ Λinl := by
  ext x <;> simp [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, TrivSqZeroExt.algebraMap_eq_inl]

theorem Λmap_fst (f : V →ₗ[K] W) : Λmap f ≫ Λfst = Λfst := by
  ext x; simp [TrivSqZeroExt.fst_map]

theorem Λinl_map (f : V →ₗ[K] W) : Λinl ≫ Λmap f = Λinl := by
  ext x <;> simp [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, TrivSqZeroExt.algebraMap_eq_inl]

theorem Λinl_fst : (Λinl : _ ⟶ Λ K V) ≫ Λfst = 𝟙 _ := by
  ext x; simp [TrivSqZeroExt.algebraMap_eq_inl]

end TSZE

section Phi
variable {J : Scheme.{u}} (x₀ : J)

noncomputable def Φ {R : CommRingCat.{u}} (g : J.presheaf.stalk x₀ ⟶ R) : Spec R ⟶ J :=
  Spec.map g ≫ J.fromSpecStalk x₀

theorem Φ_comp {R R' : CommRingCat.{u}} (g : J.presheaf.stalk x₀ ⟶ R) (φ : R ⟶ R') :
    Φ x₀ (g ≫ φ) = Spec.map φ ≫ Φ x₀ g := by
  simp [Φ]

noncomputable def stalkEndo (φ : J ⟶ J) (hφ : φ.base x₀ = x₀) :
    J.presheaf.stalk x₀ ⟶ J.presheaf.stalk x₀ :=
  (J.presheaf.stalkCongr (.of_eq hφ.symm)).hom ≫ φ.stalkMap x₀

theorem Φ_comp_endo {R : CommRingCat.{u}} (g : J.presheaf.stalk x₀ ⟶ R) (φ : J ⟶ J)
    (hφ : φ.base x₀ = x₀) : Φ x₀ g ≫ φ = Φ x₀ (stalkEndo x₀ φ hφ ≫ g) := by
  simp only [Φ, stalkEndo, Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_hom]
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq hφ)]

theorem Φ_injective {R : CommRingCat.{u}} [IsLocalRing R] {g₁ g₂ : J.presheaf.stalk x₀ ⟶ R}
    [IsLocalHom g₁.hom] [IsLocalHom g₂.hom] (h : Φ x₀ g₁ = Φ x₀ g₂) : g₁ = g₂ := by
  have := (SpecToEquivOfLocalRing J R).symm.injective
    (a₁ := ⟨x₀, g₁, inferInstance⟩) (a₂ := ⟨x₀, g₂, inferInstance⟩)
    (by first | exact h | simpa [SpecToEquivOfLocalRing_symm_apply] using h | simpa +zetaDelta [SpecToEquivOfLocalRing_symm_apply] using h)
  obtain ⟨h1, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp this
  simpa using h2

theorem exists_eq_Φ {R : CommRingCat.{u}} [IsLocalRing R] (t : Spec R ⟶ J)
    (ht : t.base (closedPoint R) = x₀) :
    ∃ g : J.presheaf.stalk x₀ ⟶ R, IsLocalHom g.hom ∧ Φ x₀ g = t := by
  subst ht
  exact ⟨Scheme.stalkClosedPointTo t, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk t⟩

variable {K : Type u} [Field K] (c : J ⟶ Spec (.of K))

noncomputable def ιO : CommRingCat.of K ⟶ J.presheaf.stalk x₀ :=
  (Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop ≫ J.presheaf.germ ⊤ x₀ trivial

theorem Φ_comp_c {R : CommRingCat.{u}} (g : J.presheaf.stalk x₀ ⟶ R) :
    Φ x₀ g ≫ c = Spec.map (ιO x₀ c ≫ g) := by
  simp only [Φ, ιO, Category.assoc]
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq]
  simp only [← Spec.map_comp, Category.assoc]
  congr 1
  rw [Scheme.Hom.germ_stalkMap_assoc]
  rfl

end Phi

section Sep

theorem mem_sq_ker_of_forall_snd_eq_zero {O : Type u} [CommRing O] {K : Type u} [Field K]
    (ι : K →+* O) (ev : O →+* K) (hιev : ∀ a, ev (ι a) = a)
    (y : O) (hy : ev y = 0)
    (H : ∀ g : O →+* TrivSqZeroExt K K, (∀ x, (g x).fst = ev x) →
      (∀ a, g (ι a) = TrivSqZeroExt.inl a) → (g y).snd = 0) :
    y ∈ (RingHom.ker ev) ^ 2 := by
  letI : Algebra K O := ι.toAlgebra
  have hsmul : ∀ (a : K) (w : O), ι a * w = a • w := fun a w ↦ (Algebra.smul_def a w).symm
  set m : Ideal O := RingHom.ker ev with hm
  let N : Submodule K O := (m ^ 2).restrictScalars K ⊔ K ∙ (1 : O)
  by_contra hy2
  have hyN : y ∉ N := by
    intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hu' : u ∈ m ^ 2 := hu
    have h1 : ev u = 0 := Ideal.pow_le_self two_ne_zero hu'
    have ha : a = 0 := by
      have h2 := hy
      rw [map_add, h1, zero_add, ← hsmul, mul_one, hιev] at h2
      exact h2
    subst ha
    apply hy2
    rwa [zero_smul, add_zero]
  have hq : N.mkQ y ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using hyN
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K (O ⧸ N), φ (N.mkQ y) ≠ 0 := by
    by_contra h
    push Not at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  let ℓ : O →ₗ[K] K := φ ∘ₗ N.mkQ
  have hℓN : ∀ u ∈ N, ℓ u = 0 := fun u hu ↦ by
    show φ (N.mkQ u) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hu, map_zero]
  have hℓ1 : ℓ 1 = 0 := hℓN _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hℓ2 : ∀ u ∈ m ^ 2, ℓ u = 0 := fun u hu ↦
    hℓN _ (Submodule.mem_sup_left (show u ∈ (m ^ 2).restrictScalars K from hu))
  have hℓι : ∀ a, ℓ (ι a) = 0 := fun a ↦ by
    rw [← mul_one (ι a), hsmul, map_smul, hℓ1, smul_zero]
  have hdec : ∀ x, x - ι (ev x) ∈ m := fun x ↦ by simp [hm, RingHom.mem_ker, hιev]
  have key : ∀ x z, ℓ (x * z) = ev x • ℓ z + ev z • ℓ x := fun x z ↦ by
    have h1 : x * z = (ι (ev x) * z + ι (ev z) * x) +
        ((x - ι (ev x)) * (z - ι (ev z)) - ι (ev x * ev z)) := by
      rw [map_mul]; ring
    have h2 : ℓ ((x - ι (ev x)) * (z - ι (ev z))) = 0 :=
      hℓ2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hdec x) (hdec z))
    rw [h1, map_add, map_add, map_sub, h2, hℓι, sub_zero, add_zero, hsmul, hsmul, map_smul,
      map_smul]
  let g : O →+* TrivSqZeroExt K K :=
    { toFun := fun x ↦ TrivSqZeroExt.inl (ev x) + TrivSqZeroExt.inr (ℓ x)
      map_one' := by ext <;> simp [hℓ1]
      map_mul' := fun x z ↦ by
        ext
        · simp
        · simp [TrivSqZeroExt.snd_mul, key, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x z ↦ by ext <;> simp }
  have hg1 : ∀ x, (g x).fst = ev x := fun x ↦ by
    show (TrivSqZeroExt.inl (ev x) + TrivSqZeroExt.inr (ℓ x)).fst = ev x
    simp
  have hg2 : ∀ a, g (ι a) = TrivSqZeroExt.inl a := fun a ↦ by
    show TrivSqZeroExt.inl (ev (ι a)) + TrivSqZeroExt.inr (ℓ (ι a)) = TrivSqZeroExt.inl a
    rw [hιev, hℓι, TrivSqZeroExt.inr_zero, add_zero]
  have hgy : (TrivSqZeroExt.inl (ev y) + TrivSqZeroExt.inr (ℓ y)).snd = 0 := H g hg1 hg2
  apply hφ
  first | exact hgy | simpa using hgy | simpa +zetaDelta using hgy

end Sep

namespace JPHead

variable {K : Type u} [Field K] {J : Scheme.{u}}

section SchemeLevel

variable (c : J ⟶ Spec (.of K)) (mul : pullback c c ⟶ J)
  (hmulK : mul ≫ c = pullback.fst c c ≫ c)
  (e : Spec (.of K) ⟶ J) (he : e ≫ c = 𝟙 _)

noncomputable def nsmulHom : ℕ → {φ : J ⟶ J // φ ≫ c = c}
  | 0 => ⟨c ≫ e, by rw [Category.assoc, he, Category.comp_id]⟩
  | k + 1 => ⟨pullback.lift (nsmulHom k).1 (𝟙 J) (by rw [(nsmulHom k).2, Category.id_comp]) ≫ mul,
      by rw [Category.assoc, hmulK, pullback.lift_fst_assoc, (nsmulHom k).2]⟩

theorem nsmulHom_zero : (nsmulHom c mul hmulK e he 0).1 = c ≫ e := rfl

theorem nsmulHom_succ (k : ℕ) : (nsmulHom c mul hmulK e he (k + 1)).1 =
    pullback.lift (nsmulHom c mul hmulK e he k).1 (𝟙 J)
      (by rw [(nsmulHom c mul hmulK e he k).2, Category.id_comp]) ≫ mul := rfl

theorem e_comp_nsmulHom (hee : pullback.lift e e rfl ≫ mul = e) (k : ℕ) :
    e ≫ (nsmulHom c mul hmulK e he k).1 = e := by
  induction k with
  | zero => rw [nsmulHom_zero, ← Category.assoc, he, Category.id_comp]
  | succ k ih =>
    rw [nsmulHom_succ, comp_pullbackLift_assoc]
    convert hee using 2
    ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, ih]

noncomputable def transl (σ : {σ : Spec (.of K) ⟶ J // σ ≫ c = 𝟙 _}) : J ⟶ J :=
  pullback.lift (𝟙 J) (c ≫ σ.1) (by rw [Category.assoc, σ.2, Category.id_comp, Category.comp_id])
    ≫ mul

include hmulK in
theorem transl_comp_c (σ) : transl c mul σ ≫ c = c := by
  rw [transl, Category.assoc, hmulK, pullback.lift_fst_assoc, Category.id_comp]

end SchemeLevel

section Tangent

variable {K : Type u} [Field K] {J : Scheme.{u}}
  (c : J ⟶ Spec (.of K)) (mul : pullback c c ⟶ J)
  (hmulK : mul ≫ c = pullback.fst c c ≫ c)
  (e : Spec (.of K) ⟶ J) (he : e ≫ c = 𝟙 _)
  (hr : pullback.lift (𝟙 J) (c ≫ e) (by rw [Category.assoc, he, Category.id_comp,
      Category.comp_id]) ≫ mul = 𝟙 J)
  (hl : pullback.lift (c ≫ e) (𝟙 J) (by rw [Category.assoc, he, Category.id_comp,
      Category.comp_id]) ≫ mul = 𝟙 J)

noncomputable abbrev ev : J.presheaf.stalk (e.base (closedPoint K)) ⟶ CommRingCat.of K :=
  Scheme.stalkClosedPointTo e

theorem Φ_ev : Φ (e.base (closedPoint K)) (ev e) = e :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk e

include he in
theorem ιO_ev : ιO (e.base (closedPoint K)) c ≫ ev e = 𝟙 _ :=
  Spec.map_injective (by rw [← Φ_comp_c, Φ_ev, he, Spec.map_id])

include he in
theorem ev_ιO_apply (a : K) : (ev e).hom ((ιO (e.base (closedPoint K)) c).hom a) = a := by
  rw [← CommRingCat.comp_apply, ιO_ev c e he]; rfl

theorem mem_maximalIdeal_iff_ev (x : J.presheaf.stalk (e.base (closedPoint K))) :
    x ∈ maximalIdeal _ ↔ (ev e).hom x = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h
    by_contra h'
    exact h (isUnit_of_map_unit (ev e).hom x (isUnit_iff_ne_zero.mpr h'))
  · intro h h'
    exact (isUnit_iff_ne_zero.mp (h'.map (ev e).hom)) h

theorem maximalIdeal_eq_ker_ev :
    maximalIdeal (J.presheaf.stalk (e.base (closedPoint K))) = RingHom.ker (ev e).hom :=
  Ideal.ext fun x ↦ by rw [mem_maximalIdeal_iff_ev, RingHom.mem_ker]

include hr he in

theorem e_idem' : pullback.lift e e rfl ≫ mul = e := by
  have h := congrArg (e ≫ ·) hr
  simp only [comp_pullbackLift_assoc, Category.comp_id] at h
  convert h using 2
  ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, reassoc_of% he]

include hr he in
theorem nsmulHom_base (n : ℕ) :
    (nsmulHom c mul hmulK e he n).1.base (e.base (closedPoint K)) = e.base (closedPoint K) := by
  have := e_comp_nsmulHom c mul hmulK e he (e_idem' c mul e he hr) n
  simpa using congrArg (fun φ ↦ φ.base (closedPoint K)) this

theorem ιO_stalkEndo (φ : J ⟶ J) (hφc : φ ≫ c = c) (x₀ : J) (hφ : φ.base x₀ = x₀) :
    ιO x₀ c ≫ stalkEndo x₀ φ hφ = ιO x₀ c := by
  simp only [ιO, stalkEndo, Category.assoc, TopCat.Presheaf.stalkCongr_hom]
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap, ← Category.assoc,
    ← Category.assoc, Category.assoc (Scheme.ΓSpecIso _).inv]
  change ((Scheme.ΓSpecIso _).inv ≫ (φ ≫ c).appTop) ≫ _ = _
  rw [hφc]
  rfl

variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

def IsTestHom (g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V) : Prop :=
  g ≫ Λfst = ev e ∧ ιO (e.base (closedPoint K)) c ≫ g = Λinl

theorem IsTestHom.isLocalHom {g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V}
    (hg : IsTestHom c e g) : IsLocalHom g.hom := by
  constructor
  intro a ha
  have : IsUnit ((g ≫ Λfst).hom a) := by
    rw [CommRingCat.comp_apply]
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha
  rw [hg.1] at this
  exact isUnit_of_map_unit _ _ this

theorem isLocalHom_comp' {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsLocalHom f.hom]
    [IsLocalHom g.hom] : IsLocalHom (f ≫ g).hom :=
  ⟨fun a ha ↦ isUnit_of_map_unit f.hom a (isUnit_of_map_unit g.hom _ (by simpa using ha))⟩

theorem IsTestHom.Φcomp {g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V}
    (hg : IsTestHom c e g) : Φ _ g ≫ c = Spec.map Λinl := by
  rw [Φ_comp_c, hg.2]

theorem IsTestHom.comp_Λmap {g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V}
    (hg : IsTestHom c e g) (f : V →ₗ[K] W) : IsTestHom c e (g ≫ Λmap f) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Λmap_fst, hg.1]
  · rw [← Category.assoc, hg.2, Λinl_map]

include he in
theorem isTestHom_zero : IsTestHom c e (ev e ≫ (Λinl : _ ⟶ Λ K V)) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Λinl_fst, Category.comp_id]
  · rw [← Category.assoc, ιO_ev c e he, Category.id_comp]

theorem Φ_zero : Φ _ (ev e ≫ (Λinl : _ ⟶ Λ K V)) = Spec.map Λinl ≫ e := by
  rw [Φ_comp, Φ_ev]

noncomputable def mpt (g₁ g₂ : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V)
    (h : ιO (e.base (closedPoint K)) c ≫ g₁ = ιO (e.base (closedPoint K)) c ≫ g₂) :
    Spec (Λ K V) ⟶ J :=
  pullback.lift (Φ _ g₁) (Φ _ g₂) (by rw [Φ_comp_c, Φ_comp_c, h]) ≫ mul

theorem mpt_congr {g₁ g₂ g₁' g₂' : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V}
    (h₁ : g₁ = g₁') (h₂ : g₂ = g₂') (h) (h') :
    mpt c mul e g₁ g₂ h = mpt c mul e g₁' g₂' h' := by
  subst h₁ h₂; rfl

theorem SpecMap_comp_mpt_lift {R : CommRingCat.{u}}
    (g₁ g₂ : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V) (h) (φ : Λ K V ⟶ R) :
    Spec.map φ ≫ mpt c mul e g₁ g₂ h =
      pullback.lift (Φ _ (g₁ ≫ φ)) (Φ _ (g₂ ≫ φ))
        (by rw [Φ_comp_c, Φ_comp_c, reassoc_of% h]) ≫ mul := by
  rw [mpt, comp_pullbackLift_assoc]
  congr 1
  ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, Φ_comp]

theorem SpecMap_comp_mpt
    (g₁ g₂ : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V) (h) (φ : Λ K V ⟶ Λ K W) :
    Spec.map φ ≫ mpt c mul e g₁ g₂ h = mpt c mul e (g₁ ≫ φ) (g₂ ≫ φ) (by rw [reassoc_of% h]) := by
  rw [mpt, mpt, comp_pullbackLift_assoc]
  congr 1
  ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, Φ_comp]

include hr in
theorem mpt_zero_right {g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V}
    (hg : IsTestHom c e g) (h) : mpt c mul e g (ev e ≫ Λinl) h = Φ _ g := by
  have h2 := congrArg (Φ _ g ≫ ·) hr
  simp only [comp_pullbackLift_assoc, Category.comp_id] at h2
  rw [← h2, mpt]
  congr 1
  ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, Φ_zero, reassoc_of% (IsTestHom.Φcomp c e hg)]

include hl in
theorem mpt_zero_left {g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K V}
    (hg : IsTestHom c e g) (h) : mpt c mul e (ev e ≫ Λinl) g h = Φ _ g := by
  have h2 := congrArg (Φ _ g ≫ ·) hl
  simp only [comp_pullbackLift_assoc, Category.comp_id] at h2
  rw [← h2, mpt]
  congr 1
  ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, Φ_zero, reassoc_of% (IsTestHom.Φcomp c e hg)]

include hmulK hr hl he in

theorem exists_test_add {g₁ g₂ : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K K}
    (hg₁ : IsTestHom c e g₁) (hg₂ : IsTestHom c e g₂) :
    ∃ g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K K, IsTestHom c e g ∧
      Φ _ g = mpt c mul e g₁ g₂ (by rw [hg₁.2, hg₂.2]) ∧
      ∀ x, (g.hom x).snd = (g₁.hom x).snd + (g₂.hom x).snd := by

  set G₁ := g₁ ≫ Λmap (LinearMap.inl K K K) with hG₁def
  set G₂ := g₂ ≫ Λmap (LinearMap.inr K K K) with hG₂def
  have hG₁ : IsTestHom c e G₁ := IsTestHom.comp_Λmap c e hg₁ _
  have hG₂ : IsTestHom c e G₂ := IsTestHom.comp_Λmap c e hg₂ _
  have hG : ιO _ c ≫ G₁ = ιO _ c ≫ G₂ := by rw [hG₁.2, hG₂.2]
  set M := mpt c mul e G₁ G₂ hG with hMdef

  have hzero : ιO _ c ≫ g₁ = ιO _ c ≫ (ev e ≫ Λinl) := by
    rw [hg₁.2, ← Category.assoc, ιO_ev c e he, Category.id_comp]
  have hzero' : ιO _ c ≫ (ev e ≫ Λinl) = ιO _ c ≫ g₂ := by
    rw [hg₂.2, ← Category.assoc, ιO_ev c e he, Category.id_comp]
  have hM₁ : Spec.map (Λmap (LinearMap.fst K K K)) ≫ M = Φ _ g₁ := by
    have e1 : G₁ ≫ Λmap (LinearMap.fst K K K) = g₁ := by
      rw [hG₁def, Category.assoc, Λmap_comp, LinearMap.fst_comp_inl, Λmap_id, Category.comp_id]
    have e2 : G₂ ≫ Λmap (LinearMap.fst K K K) = ev e ≫ Λinl := by
      rw [hG₂def, Category.assoc, Λmap_comp, LinearMap.fst_comp_inr, Λmap_zero,
        reassoc_of% hg₂.1]
    rw [hMdef, SpecMap_comp_mpt, mpt_congr c mul e e1 e2 _ hzero, mpt_zero_right c mul e he hr hg₁]
  have hM₂ : Spec.map (Λmap (LinearMap.snd K K K)) ≫ M = Φ _ g₂ := by
    have e1 : G₁ ≫ Λmap (LinearMap.snd K K K) = ev e ≫ Λinl := by
      rw [hG₁def, Category.assoc, Λmap_comp, LinearMap.snd_comp_inl, Λmap_zero,
        reassoc_of% hg₁.1]
    have e2 : G₂ ≫ Λmap (LinearMap.snd K K K) = g₂ := by
      rw [hG₂def, Category.assoc, Λmap_comp, LinearMap.snd_comp_inr, Λmap_id, Category.comp_id]
    rw [hMdef, SpecMap_comp_mpt, mpt_congr c mul e e1 e2 _ hzero', mpt_zero_left c mul e he hl hg₂]
  have hMΔ : Spec.map (Λmap (LinearMap.fst K K K + LinearMap.snd K K K)) ≫ M =
      mpt c mul e g₁ g₂ (by rw [hg₁.2, hg₂.2]) := by
    have e1 : G₁ ≫ Λmap (LinearMap.fst K K K + LinearMap.snd K K K) = g₁ := by
      rw [hG₁def, Category.assoc, Λmap_comp, LinearMap.add_comp, LinearMap.fst_comp_inl,
        LinearMap.snd_comp_inl, add_zero, Λmap_id, Category.comp_id]
    have e2 : G₂ ≫ Λmap (LinearMap.fst K K K + LinearMap.snd K K K) = g₂ := by
      rw [hG₂def, Category.assoc, Λmap_comp, LinearMap.add_comp, LinearMap.fst_comp_inr,
        LinearMap.snd_comp_inr, zero_add, Λmap_id, Category.comp_id]
    rw [hMdef, SpecMap_comp_mpt, mpt_congr c mul e e1 e2]
  have hM₀ : Spec.map Λfst ≫ M = e := by
    rw [hMdef, SpecMap_comp_mpt_lift]
    have := e_idem' c mul e he hr
    convert this using 2
    ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, hG₁.1, hG₂.1, Φ_ev]
  have hMx : M.base (closedPoint (TrivSqZeroExt K (K × K))) = e.base (closedPoint K) := by
    have h1 : (Spec.map (Λfst : Λ K (K × K) ⟶ _)).base (closedPoint K) = closedPoint _ :=
      Spec_closedPoint
    rw [← h1]
    conv_rhs => rw [← hM₀]
    rfl
  obtain ⟨gM, hgMloc, hgM⟩ := exists_eq_Φ _ M hMx

  have hev : IsLocalHom (ev e).hom := inferInstance
  have hgM1 : gM ≫ Λfst = ev e := by
    have : IsLocalHom (gM ≫ Λfst).hom := isLocalHom_comp' _ _
    apply Φ_injective
    rw [Φ_comp, hgM, hM₀, Φ_ev]
  have hgM2 : ιO _ c ≫ gM = Λinl := by
    apply Spec.map_injective
    rw [← Φ_comp_c, hgM, hMdef, mpt, Category.assoc, hmulK, pullback.lift_fst_assoc, IsTestHom.Φcomp c e hG₁]
  have hgMt : IsTestHom c e gM := ⟨hgM1, hgM2⟩

  have hc1 : gM ≫ Λmap (LinearMap.fst K K K) = g₁ := by
    have := IsTestHom.isLocalHom c e (IsTestHom.comp_Λmap c e hgMt (LinearMap.fst K K K))
    have := IsTestHom.isLocalHom c e hg₁
    apply Φ_injective
    rw [Φ_comp, hgM, hM₁]
  have hc2 : gM ≫ Λmap (LinearMap.snd K K K) = g₂ := by
    have := IsTestHom.isLocalHom c e (IsTestHom.comp_Λmap c e hgMt (LinearMap.snd K K K))
    have := IsTestHom.isLocalHom c e hg₂
    apply Φ_injective
    rw [Φ_comp, hgM, hM₂]
  refine ⟨gM ≫ Λmap (LinearMap.fst K K K + LinearMap.snd K K K),
    IsTestHom.comp_Λmap c e hgMt _, ?_, ?_⟩
  · rw [Φ_comp, hgM, hMΔ]
  · intro x
    rw [← hc1, ← hc2]
    simp [TrivSqZeroExt.snd_map]

include hr hl he in

theorem exists_test_nsmul {g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K K}
    (hg : IsTestHom c e g) (k : ℕ) :
    ∃ g' : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K K, IsTestHom c e g' ∧
      Φ _ g' = Φ _ g ≫ (nsmulHom c mul hmulK e he k).1 ∧
      ∀ x, (g'.hom x).snd = k • (g.hom x).snd := by
  induction k with
  | zero =>
    refine ⟨ev e ≫ Λinl, isTestHom_zero c e he, ?_, fun x ↦ by
      simp [TrivSqZeroExt.algebraMap_eq_inl']⟩
    rw [Φ_zero, nsmulHom_zero, reassoc_of% (IsTestHom.Φcomp c e hg)]
  | succ k ih =>
    obtain ⟨gk, hgk, hΦk, hsndk⟩ := ih
    obtain ⟨g', hg', hΦ', hsnd'⟩ := exists_test_add c mul hmulK e he hr hl hgk hg
    refine ⟨g', hg', ?_, fun x ↦ by rw [hsnd', hsndk, succ_nsmul]⟩
    rw [hΦ', nsmulHom_succ, comp_pullbackLift_assoc, mpt]
    congr 1
    ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, hΦk]

include hr hl he in

theorem test_stalkEndo {g : J.presheaf.stalk (e.base (closedPoint K)) ⟶ Λ K K}
    (hg : IsTestHom c e g) (n : ℕ)
    (hfix : (nsmulHom c mul hmulK e he n).1.base (e.base (closedPoint K)) = e.base (closedPoint K))
    (x : J.presheaf.stalk (e.base (closedPoint K))) :
    (g.hom ((stalkEndo _ _ hfix).hom x)).snd = n • (g.hom x).snd ∧
      (g.hom ((stalkEndo _ _ hfix).hom x)).fst = (ev e).hom x := by
  obtain ⟨gn, hgn, hΦn, hsnd⟩ := exists_test_nsmul c mul hmulK e he hr hl hg n
  have heq : stalkEndo _ _ hfix ≫ g = gn := by
    have := IsTestHom.isLocalHom c e hg
    have := IsTestHom.isLocalHom c e hgn
    have : IsLocalHom (J.presheaf.stalkCongr (.of_eq hfix.symm)).hom.hom := isLocalHom_of_isIso _
    have : IsLocalHom (stalkEndo _ _ hfix).hom := isLocalHom_comp' _ _
    have : IsLocalHom (stalkEndo _ _ hfix ≫ g).hom := isLocalHom_comp' _ _
    apply Φ_injective
    rw [← Φ_comp_endo, hΦn]
  have h1 : g.hom ((stalkEndo _ _ hfix).hom x) = gn.hom x := by
    rw [← CommRingCat.comp_apply, heq]
  refine ⟨by rw [h1, hsnd], ?_⟩
  rw [h1, ← hgn.1, CommRingCat.comp_apply]
  rfl

include hr hl he in

theorem stalkEndo_nsmulHom_sub_mem_sq (n : ℕ)
    (hfix : (nsmulHom c mul hmulK e he n).1.base (e.base (closedPoint K)) =
      e.base (closedPoint K))
    (x : J.presheaf.stalk (e.base (closedPoint K)))
    (hx : x ∈ maximalIdeal (J.presheaf.stalk (e.base (closedPoint K)))) :
    (stalkEndo _ _ hfix).hom x - n • x ∈
      (maximalIdeal (J.presheaf.stalk (e.base (closedPoint K)))) ^ 2 := by
  rw [maximalIdeal_eq_ker_ev]
  have hx' : (ev e).hom x = 0 := (mem_maximalIdeal_iff_ev e x).mp hx
  refine mem_sq_ker_of_forall_snd_eq_zero (ιO _ c).hom (ev e).hom (ev_ιO_apply c e he) _ ?_ ?_
  · obtain ⟨-, hfst⟩ :=
      test_stalkEndo c mul hmulK e he hr hl (isTestHom_zero c e he (V := K)) n hfix x
    have hfst' : (ev e).hom ((stalkEndo _ _ hfix).hom x) = (ev e).hom x := by
      simpa [TrivSqZeroExt.algebraMap_eq_inl'] using hfst
    rw [map_sub, map_nsmul, hfst', hx', smul_zero, sub_zero]
  · intro g hg1 hg2
    have htest : IsTestHom c e (CommRingCat.ofHom g) := by
      refine ⟨?_, ?_⟩
      · refine CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_)
        first | exact hg1 y | simpa using hg1 y | simpa +zetaDelta using hg1 y
      · refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
        first | exact hg2 a | simpa [TrivSqZeroExt.algebraMap_eq_inl'] using hg2 a | simpa +zetaDelta [TrivSqZeroExt.algebraMap_eq_inl'] using hg2 a
    obtain ⟨hsnd, -⟩ := test_stalkEndo c mul hmulK e he hr hl htest n hfix x
    have hsnd' : (g ((stalkEndo _ _ hfix).hom x)).snd = n • (g x).snd := hsnd
    rw [map_sub, TrivSqZeroExt.snd_sub, hsnd', map_nsmul, TrivSqZeroExt.snd_nsmul', sub_self]

include hr hl he in

theorem formallyUnramified_stalkMap_nsmulHom [LocallyOfFiniteType c]
    (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) :
    ((nsmulHom c mul hmulK e he n).1.stalkMap (e.base (closedPoint K))).hom.FormallyUnramified := by
  have hfix := nsmulHom_base c mul hmulK e he hr n
  set φ := (nsmulHom c mul hmulK e he n) with hφdef
  have : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian c
  have : LocallyOfFiniteType (φ.1 ≫ c) := by rw [φ.2]; infer_instance
  have : LocallyOfFiniteType φ.1 := locallyOfFiniteType_of_comp φ.1 c
  let ι := (J.presheaf.stalkCongr (.of_eq hfix.symm)).hom
  have hιψ : ∀ y, (φ.1.stalkMap _).hom (ι.hom y) = (stalkEndo _ _ hfix).hom y := fun y ↦ by
    rw [← CommRingCat.comp_apply]; rfl
  have hK : ∀ a, (stalkEndo _ _ hfix).hom ((ιO _ c).hom a) = (ιO _ c).hom a := fun a ↦ by
    rw [← CommRingCat.comp_apply, ιO_stalkEndo c φ.1 φ.2]
  refine JPHead.formallyUnramified_of_surjective_cotangent (φ.1.stalkMap _).hom
    (LocallyOfFiniteType.stalkMap φ.1 _) ?_ ?_
  · intro s
    refine ⟨ι.hom ((ιO _ c).hom ((ev e).hom s)), ?_⟩
    rw [hιψ, hK, mem_maximalIdeal_iff_ev, map_sub, ev_ιO_apply c e he, sub_self]
  · intro x hx
    have hn' : (n : K) ≠ 0 := hchar
    set u := (ιO (e.base (closedPoint K)) c).hom (n : K)⁻¹ with hu
    have hux : u * (n • x) = x := by
      rw [nsmul_eq_mul, ← mul_assoc, hu, ← map_natCast (ιO (e.base (closedPoint K)) c).hom n,
        ← map_mul, inv_mul_cancel₀ hn', map_one, one_mul]
    refine ⟨ι.hom (u * x), ?_, ?_⟩
    ·
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      intro hunit
      apply hx
      have : IsUnit ((J.presheaf.stalkCongr (.of_eq hfix.symm)).inv.hom (ι.hom (u * x))) :=
        hunit.map _
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at this
      exact isUnit_of_mul_isUnit_right this
    · rw [hιψ, map_mul, hK]
      have hmem := stalkEndo_nsmulHom_sub_mem_sq c mul hmulK e he hr hl n hfix x hx
      have : x - u * (stalkEndo _ _ hfix).hom x = -(u * ((stalkEndo _ _ hfix).hom x - n • x)) := by
        rw [mul_sub, hux]; ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_left _ _ hmem)

end Tangent

section Points

theorem isReduced_J (c : J ⟶ Spec (.of K)) [Smooth c] : IsReduced J :=
  isReduced_of_smooth_of_field c

theorem isReduced_pullback (c : J ⟶ Spec (.of K)) [Smooth c] : IsReduced ↑(pullback c c) :=
  isReduced_of_smooth_of_field (pullback.fst c c ≫ c)

variable [IsAlgClosed K] (c : J ⟶ Spec (.of K)) [Smooth c] [IsProper c]
  (mul : pullback c c ⟶ J)
  {G : Type*} [AddCommGroup G] (pts : G ≃ {σ : Spec (.of K) ⟶ J // σ ≫ c = 𝟙 _})
  (hadd : ∀ x y : G, (pts (x + y)).1 =
    pullback.lift (pts x).1 (pts y).1 ((pts x).2.trans (pts y).2.symm) ≫ mul)

omit [IsAlgClosed K] [IsProper c] [Smooth c] in

theorem exists_eq_lift (σ : Spec (.of K) ⟶ pullback c c) (hσ : σ ≫ pullback.fst c c ≫ c = 𝟙 _) :
    ∃ a b : G, σ = pullback.lift (pts a).1 (pts b).1 ((pts a).2.trans (pts b).2.symm) := by
  refine ⟨pts.symm ⟨σ ≫ pullback.fst c c, by simpa using hσ⟩,
    pts.symm ⟨σ ≫ pullback.snd c c, ?_⟩, ?_⟩
  · rw [Category.assoc, ← pullback.condition]; simpa using hσ
  · ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

include hadd

theorem mul_comp_c : mul ≫ c = pullback.fst c c ≫ c := by
  have := isReduced_pullback c
  refine ext_of_forall_comp_eq_of_isAlgClosed (pullback.fst c c ≫ c)
    (terminal.from (Spec (.of K))) (terminal.hom_ext _ _) fun σ hσ ↦ ?_
  obtain ⟨a, b, rfl⟩ := exists_eq_lift c pts σ (by simpa using hσ)
  rw [← Category.assoc, ← hadd, (pts (a + b)).2, ← Category.assoc, pullback.lift_fst, (pts a).2]

theorem rightUnit : pullback.lift (𝟙 J) (c ≫ (pts 0).1) (by rw [Category.assoc, (pts 0).2,
    Category.id_comp, Category.comp_id]) ≫ mul = 𝟙 J := by
  have := isReduced_J c
  have hK := mul_comp_c c mul pts hadd
  refine ext_of_forall_comp_eq_of_isAlgClosed c c ?_ fun σ hσ ↦ ?_
  · rw [Category.assoc, hK, pullback.lift_fst_assoc]
  · obtain ⟨a, rfl⟩ : ∃ a, σ = (pts a).1 := ⟨pts.symm ⟨σ, hσ⟩, by simp⟩
    rw [comp_pullbackLift_assoc]
    conv_rhs => rw [Category.comp_id, ← add_zero a, hadd]
    congr 1
    ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% (pts a).2]

theorem leftUnit : pullback.lift (c ≫ (pts 0).1) (𝟙 J) (by rw [Category.assoc, (pts 0).2,
    Category.id_comp, Category.comp_id]) ≫ mul = 𝟙 J := by
  have := isReduced_J c
  have hK := mul_comp_c c mul pts hadd
  refine ext_of_forall_comp_eq_of_isAlgClosed c c ?_ fun σ hσ ↦ ?_
  · rw [Category.assoc, hK, pullback.lift_fst_assoc, Category.assoc, (pts 0).2, Category.id_comp,
      Category.comp_id]
  · obtain ⟨a, rfl⟩ : ∃ a, σ = (pts a).1 := ⟨pts.symm ⟨σ, hσ⟩, by simp⟩
    rw [comp_pullbackLift_assoc]
    conv_rhs => rw [Category.comp_id, ← zero_add a, hadd]
    congr 1
    ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% (pts a).2]

theorem e_idem : pullback.lift (pts 0).1 (pts 0).1 rfl ≫ mul = (pts 0).1 := by
  have h := congrArg ((pts 0).1 ≫ ·) (rightUnit c mul pts hadd)
  simp only [comp_pullbackLift_assoc, Category.comp_id] at h
  convert h using 2
  ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% (pts 0).2]

theorem pts_nsmul (k : ℕ) (a : G) :
    (pts (k • a)).1 =
      (pts a).1 ≫ (nsmulHom c mul (mul_comp_c c mul pts hadd) (pts 0).1 (pts 0).2 k).1 := by
  induction k with
  | zero => simp [nsmulHom_zero, reassoc_of% (pts a).2]
  | succ k ih =>
    rw [nsmulHom_succ, comp_pullbackLift_assoc, succ_nsmul, hadd]
    congr 1
    ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, ih]

theorem pts_comp_transl (a b : G) :
    (pts b).1 ≫ transl c mul (pts a) = (pts (b + a)).1 := by
  rw [transl, comp_pullbackLift_assoc, hadd]
  congr 1
  ext : 1 <;> simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% (pts b).2]

theorem transl_comp_transl_neg (a : G) :
    transl c mul (pts a) ≫ transl c mul (pts (-a)) = 𝟙 J := by
  have := isReduced_J c
  have hK := mul_comp_c c mul pts hadd
  refine ext_of_forall_comp_eq_of_isAlgClosed c c ?_ fun σ hσ ↦ ?_
  · simp only [Category.assoc, transl_comp_c c mul hK, Category.id_comp]
  · obtain ⟨b, rfl⟩ : ∃ b, σ = (pts b).1 := ⟨pts.symm ⟨σ, hσ⟩, by simp⟩
    rw [← Category.assoc, pts_comp_transl c mul pts hadd, pts_comp_transl c mul pts hadd,
      Category.comp_id, add_neg_cancel_right]

theorem isIso_transl (a : G) : IsIso (transl c mul (pts a)) :=
  ⟨transl c mul (pts (-a)), transl_comp_transl_neg c mul pts hadd a, by
    simpa using transl_comp_transl_neg c mul pts hadd (-a)⟩

theorem transl_comp_nsmul (n : ℕ) (a : G) :
    transl c mul (pts a) ≫ (nsmulHom c mul (mul_comp_c c mul pts hadd) (pts 0).1 (pts 0).2 n).1 =
      (nsmulHom c mul (mul_comp_c c mul pts hadd) (pts 0).1 (pts 0).2 n).1 ≫
        transl c mul (pts (n • a)) := by
  have := isReduced_J c
  have hK := mul_comp_c c mul pts hadd
  refine ext_of_forall_comp_eq_of_isAlgClosed c c ?_ fun σ hσ ↦ ?_
  · simp only [Category.assoc, transl_comp_c c mul hK, (nsmulHom c mul _ _ _ n).2]
  · obtain ⟨b, rfl⟩ : ∃ b, σ = (pts b).1 := ⟨pts.symm ⟨σ, hσ⟩, by simp⟩
    rw [← Category.assoc, pts_comp_transl c mul pts hadd, ← pts_nsmul c mul pts hadd,
      ← Category.assoc, ← pts_nsmul c mul pts hadd, pts_comp_transl c mul pts hadd, nsmul_add]

end Points

section Head

variable [IsAlgClosed K] (c : J ⟶ Spec (.of K)) [Smooth c] [IsProper c]
  [ConnectedSpace J] (mul : pullback c c ⟶ J)
  {G : Type*} [AddCommGroup G] (pts : G ≃ {σ : Spec (.of K) ⟶ J // σ ≫ c = 𝟙 _})
  (hadd : ∀ x y : G, (pts (x + y)).1 =
    pullback.lift (pts x).1 (pts y).1 ((pts x).2.trans (pts y).2.symm) ≫ mul)

include hadd

noncomputable def nmul (n : ℕ) : J ⟶ J :=
  (nsmulHom c mul (mul_comp_c c mul pts hadd) (pts 0).1 (pts 0).2 n).1

omit [ConnectedSpace J] in
theorem nmul_comp_c (n : ℕ) : nmul c mul pts hadd n ≫ c = c :=
  (nsmulHom c mul (mul_comp_c c mul pts hadd) (pts 0).1 (pts 0).2 n).2

omit [ConnectedSpace J] in
theorem nsmul_base_x₀ (n : ℕ) :
    (nmul c mul pts hadd n).base ((pts 0).1.base (closedPoint K)) =
      (pts 0).1.base (closedPoint K) := by
  have := e_comp_nsmulHom c mul (mul_comp_c c mul pts hadd) (pts 0).1 (pts 0).2
    (e_idem c mul pts hadd) n
  first | exact congrArg (fun φ ↦ φ.base (closedPoint K)) this | simpa using congrArg (fun φ ↦ φ.base (closedPoint K)) this | simpa +zetaDelta using congrArg (fun φ ↦ φ.base (closedPoint K)) this

omit [ConnectedSpace J] in

theorem exists_etale_nhd_unit (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) :
    ∃ U : J.Opens, (pts 0).1.base (closedPoint K) ∈ U ∧ Etale (U.ι ≫ nmul c mul pts hadd n) := by
  refine exists_etale_of_formallyUnramified_stalkMap c c (nmul c mul pts hadd n)
    (nmul_comp_c c mul pts hadd n) (pts 0).1 (pts 0).2 ?_ ?_
  · exact formallyUnramified_stalkMap_nsmulHom c mul _ _ _ (rightUnit c mul pts hadd)
      (leftUnit c mul pts hadd) n hn hchar
  · exact congrArg (fun y ↦ Module.finrank (IsLocalRing.ResidueField (J.presheaf.stalk y))
      (IsLocalRing.CotangentSpace (J.presheaf.stalk y))) (nsmul_base_x₀ c mul pts hadd n).symm

omit [ConnectedSpace J] in

theorem etale_nsmul (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) : Etale (nmul c mul pts hadd n) := by
  obtain ⟨U, hx₀U, hU⟩ := exists_etale_nhd_unit c mul pts hadd n hn hchar
  have hK := mul_comp_c c mul pts hadd
  have hiso : ∀ a, IsIso (transl c mul (pts a)) := isIso_transl c mul pts hadd

  let V : G → J.Opens := fun a ↦ (transl c mul (pts (-a))) ⁻¹ᵁ U
  have hV : ∀ a, Etale ((V a).ι ≫ nmul c mul pts hadd n) := by
    intro a
    have := hiso (-a)
    have := hiso (n • a)
    have h3 := transl_comp_transl_neg c mul pts hadd (-a)
    rw [neg_neg] at h3
    have h2 : (transl c mul (pts (-a)) ∣_ U) ≫ ((U.ι ≫ nmul c mul pts hadd n) ≫
        transl c mul (pts (n • a))) = (V a).ι ≫ nmul c mul pts hadd n := by
      simp only [Category.assoc, morphismRestrict_ι_assoc, nmul,
        ← transl_comp_nsmul c mul pts hadd n a, reassoc_of% h3, Category.id_comp, V]
    have : Etale ((transl c mul (pts (-a)) ∣_ U) ≫ ((U.ι ≫ nmul c mul pts hadd n) ≫
        transl c mul (pts (n • a)))) := inferInstance
    rwa [h2] at this
  have htop : ⨆ a, V a = ⊤ := by
    have : JacobsonSpace J := LocallyOfFiniteType.jacobsonSpace c
    by_contra hne
    have hne' : ((⨆ a, V a : J.Opens) : Set J)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h ↦ hne (Opens.ext (h.trans Opens.coe_top.symm))
    obtain ⟨x, hx, hxcl⟩ := nonempty_inter_closedPoints hne'
      (Opens.isOpen _).isClosed_compl.isLocallyClosed
    apply hx
    obtain ⟨a, ha⟩ : ∃ a, (pts a).1 = pointOfClosedPoint c x hxcl :=
      ⟨pts.symm ⟨_, pointOfClosedPoint_comp c x hxcl⟩, by simp⟩
    have hxa : x = (pts a).1.base (closedPoint K) := by
      rw [ha]; exact (pointOfClosedPoint_apply c x hxcl _).symm
    simp only [Opens.coe_iSup, Set.mem_iUnion]
    refine ⟨a, ?_⟩
    change (transl c mul (pts (-a))).base x ∈ U
    have hb : (transl c mul (pts (-a))).base ((pts a).1.base (closedPoint K)) =
        (pts 0).1.base (closedPoint K) := by
      simpa using congrArg (fun φ ↦ φ.base (closedPoint K)) (pts_comp_transl c mul pts hadd (-a) a)
    rw [hxa, hb]
    exact hx₀U
  exact IsZariskiLocalAtSource.of_iSup_eq_top V htop hV

theorem exists_nsmul_eq (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) (x : G) : ∃ y : G, n • y = x := by
  have hEt := etale_nsmul c mul pts hadd n hn hchar
  have : IsProper (nmul c mul pts hadd n ≫ c) := by rw [nmul_comp_c]; infer_instance
  have : IsProper (nmul c mul pts hadd n) := IsProper.of_comp _ c
  have : Nonempty J := ⟨(pts 0).1.base (closedPoint K)⟩
  have : Surjective (nmul c mul pts hadd n) := surjective_of_universallyOpen_of_universallyClosed _
  obtain ⟨q, hq⟩ := exists_comp_eq_of_surjective_of_isAlgClosed (nmul c mul pts hadd n) (pts x).1
  have hqc : q ≫ c = 𝟙 _ := by
    rw [← (pts x).2, ← hq, Category.assoc, nmul_comp_c]
  refine ⟨pts.symm ⟨q, hqc⟩, pts.injective (Subtype.ext ?_)⟩
  rw [pts_nsmul c mul pts hadd, Equiv.apply_symm_apply, ← hq]
  rfl

end Head

end JPHead

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero.AlgebraicGeometry"

theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (J : AlgebraicGeometry.Scheme)
    (c : J ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (hsm : AlgebraicGeometry.Smooth c)
    (hpr : AlgebraicGeometry.IsProper c)
    (hconn : ConnectedSpace J)
    (mul : CategoryTheory.Limits.pullback c c ⟶ J)
    (pts : Pic0 K F ≃
      {σ : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ J // σ ≫ c = 𝟙 _})
    (hadd : ∀ x y : Pic0 K F, (pts (x + y)).1 =
      CategoryTheory.Limits.pullback.lift (pts x).1 (pts y).1
        ((pts x).2.trans (pts y).2.symm) ≫ mul)
    (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) (x : Pic0 K F) :
    ∃ y : Pic0 K F, n • y = x := by
  haveI := hsm; haveI := hpr; haveI := hconn
  exact AlgebraicGeometry.JPHead.exists_nsmul_eq c mul pts hadd n hn hchar x

end S_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero (solution)
