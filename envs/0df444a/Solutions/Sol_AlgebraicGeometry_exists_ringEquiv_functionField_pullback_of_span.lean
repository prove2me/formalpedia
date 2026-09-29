-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/91ae29ff-0795-59b6-94e5-e584c22d3a80

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_span

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_span.AlgebraicGeometry AlgebraicCurve IsLocalRing"
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.germToFunctionField isPushout_appTop_of_isPullback Scheme.Hom Scheme.Hom.germ_stalkMap_apply isPullback_morphismRestrict IsAffineOpen.isoSpec_hom Spec IsIntegral Spec.map Scheme Scheme.Opens.toSpecΓ_naturality Scheme.toSpecΓ_appTop functionField_isFractionRing_of_isAffineOpen Scheme.Hom.comp_appTop IsAffineOpen Scheme.Opens Scheme.ΓSpecIso_naturality IsAffineHom toSpecΓ Scheme.ΓSpecIso"
namespace FunctionFieldPullbackSpan
p2m_open "AlgebraicGeometry"

section Pull

variable {X Y : Scheme.{0}}

def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

theorem pull_germ [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

end Pull

section Chart

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)

theorem fromSpec_appTop_ΓSpecIso_hom :
    hU.fromSpec.appTop ≫ (Scheme.ΓSpecIso Γ(X, U)).hom = X.presheaf.map (homOfLE le_top).op := by
  have h : (hU.fromSpec ≫ X.toSpecΓ).appTop =
      (Spec.map (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)).appTop := by
    rw [hU.fromSpec_toSpecΓ]
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
  have h2 := Scheme.ΓSpecIso_naturality (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
  rw [← h, Category.assoc] at h2
  exact (cancel_epi _).mp h2

end Chart

section Core

variable {R B E : Type*} [CommRing R] [CommRing B] [IsDomain B] [Field E]

theorem injective_of_forall_isAlgebraic (α : R →+* B) (ψ : B →+* E)
    (halg : ∀ b : B, @IsAlgebraic R B _ _ α.toAlgebra b)
    (hinj : Function.Injective (ψ.comp α)) : Function.Injective ψ := by
  letI : Algebra R B := α.toAlgebra
  rw [injective_iff_map_eq_zero]
  intro b hb
  by_contra hb0
  have hne := Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker ψ) hb0
    ((RingHom.mem_ker).mpr hb) (halg b)
  apply hne
  rw [eq_bot_iff]
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker] at hr
  have : (ψ.comp α) r = 0 := hr
  exact (Ideal.mem_bot).mpr ((injective_iff_map_eq_zero _).mp hinj r this)

end Core

end AlgebraicGeometry.FunctionFieldPullbackSpan

end

open AlgebraicGeometry.FunctionFieldPullbackSpan in
theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X₀]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hgen : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint X) = genericPoint X₀)
    {F : Type} [Field F] [Algebra L F]
    (j₀ : X₀.functionField →+* F)
    (hj₀ : ∀ a : A₀, j₀ (SemistableModel.baseToFunctionField toBase₀ a) = algebraMap L F ((ι a : ↥A) : L))
    (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → X₀.functionField) (d : Fin n → L)
      (g' : Fin n → X₀.functionField),
      (∑ i, d i • j₀ (g' i)) ≠ 0 ∧ f * (∑ i, d i • j₀ (g' i)) = ∑ i, c i • j₀ (g i)) :
    ∃ φ : F ≃+* X.functionField,
      (∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a) ∧
      (∀ g : X₀.functionField,
        φ (j₀ g) =
          ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint X)).hom
            ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g)) := by
  set pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι)) with hpr

  have hP : IsPullback pr toBase toBase₀ (Spec.map (CommRingCat.ofHom ι)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ iso rfl hiso
    rw [hpr, Category.assoc, pullback.condition, ← Category.assoc, hiso]
  haveI : IsAffineHom pr :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip inferInstance
  have hgen' : pr.base (genericPoint X) ⤳ genericPoint X₀ := specializes_of_eq hgen

  let φ₀ : X₀.functionField →+* X.functionField := (pull pr hgen').hom
  have hφgerm : ∀ (U : X₀.Opens) (hU : genericPoint X₀ ∈ U) (s : Γ(X₀, U)),
      φ₀ (X₀.presheaf.germ U (genericPoint X₀) hU s) =
        X.presheaf.germ (pr ⁻¹ᵁ U) (genericPoint X) (hgen'.mem_open U.isOpen hU) (pr.app U s) :=
    fun U hU s => pull_germ pr hgen' U hU s

  obtain ⟨U, hU, hxU⟩ : ∃ U : X₀.Opens, IsAffineOpen U ∧ genericPoint X₀ ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X₀)) isOpen_univ
    exact ⟨U, hU, hxU⟩
  have hyV : genericPoint X ∈ pr ⁻¹ᵁ U := hgen'.mem_open U.isOpen hxU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : Nonempty (pr ⁻¹ᵁ U) := ⟨⟨_, hyV⟩⟩
  have hV : IsAffineOpen (pr ⁻¹ᵁ U) := hU.preimage pr
  haveI := functionField_isFractionRing_of_isAffineOpen X₀ U hU
  haveI := functionField_isFractionRing_of_isAffineOpen X (pr ⁻¹ᵁ U) hV

  have hP1 : IsPullback (pr ∣_ U) ((pr ⁻¹ᵁ U).ι ≫ toBase) (U.ι ≫ toBase₀)
      (Spec.map (CommRingCat.ofHom ι)) :=
    (isPullback_morphismRestrict pr U).paste_vert hP
  have hP2 : IsPullback (Spec.map (pr.app U)) (hV.fromSpec ≫ toBase) (hU.fromSpec ≫ toBase₀)
      (Spec.map (CommRingCat.ofHom ι)) := by
    refine hP1.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
      exact (Scheme.Opens.toSpecΓ_naturality pr U).symm
    · simp [IsAffineOpen.isoSpec_hom]
    · simp [IsAffineOpen.isoSpec_hom]
    · simp
  have hPO := isPushout_appTop_of_isPullback hP2

  let gA : A₀ →+* Γ(X₀, U) :=
    ((Scheme.ΓSpecIso (.of A₀)).inv ≫ toBase₀.appTop ≫ X₀.presheaf.map (homOfLE le_top).op).hom
  let βB : ↥A →+* Γ(X, pr ⁻¹ᵁ U) :=
    ((Scheme.ΓSpecIso (.of ↥A)).inv ≫ toBase.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom
  letI instAlg₀ : Algebra A₀ ↥A := ι.toAlgebra
  letI instAlg₁ : Algebra A₀ Γ(X₀, U) := gA.toAlgebra
  have hPO' : IsPushout (CommRingCat.ofHom (algebraMap A₀ ↥A)) (CommRingCat.ofHom (algebraMap A₀ Γ(X₀, U)))
      (CommRingCat.ofHom βB) (pr.app U) := by
    refine hPO.flip.of_iso (Scheme.ΓSpecIso (.of A₀)) (Scheme.ΓSpecIso (.of ↥A))
      (Scheme.ΓSpecIso Γ(X₀, U)) (Scheme.ΓSpecIso Γ(X, pr ⁻¹ᵁ U)) ?_ ?_ ?_ ?_
    · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ι)
    · rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpec_appTop_ΓSpecIso_hom]
      change _ = (Scheme.ΓSpecIso (.of A₀)).hom ≫ (Scheme.ΓSpecIso (.of A₀)).inv ≫ toBase₀.appTop ≫
        X₀.presheaf.map (homOfLE le_top).op
      rw [Iso.hom_inv_id_assoc]
    · rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpec_appTop_ΓSpecIso_hom]
      change _ = (Scheme.ΓSpecIso (.of ↥A)).hom ≫ (Scheme.ΓSpecIso (.of ↥A)).inv ≫ toBase.appTop ≫
        X.presheaf.map (homOfLE le_top).op
      rw [Iso.hom_inv_id_assoc]
    · exact Scheme.ΓSpecIso_naturality (pr.app U)
  let Θ : CommRingCat.of (↥A ⊗[A₀] Γ(X₀, U)) ≅ Γ(X, pr ⁻¹ᵁ U) :=
    (CommRingCat.isPushout_tensorProduct A₀ ↥A Γ(X₀, U)).isoIsPushout _ _ hPO'
  let Λ : ↥A ⊗[A₀] Γ(X₀, U) ≃+* Γ(X, pr ⁻¹ᵁ U) := Θ.commRingCatIsoToRingEquiv
  have hΛl : ∀ t : ↥A, Λ (t ⊗ₜ 1) = βB t := fun t => by
    have := congrArg (fun ψ => ψ.hom t)
      ((CommRingCat.isPushout_tensorProduct A₀ ↥A Γ(X₀, U)).inl_isoIsPushout_hom _ _ hPO')
    exact this
  have hΛr : ∀ a : Γ(X₀, U), Λ (1 ⊗ₜ a) = pr.app U a := fun a => by
    have := congrArg (fun ψ => ψ.hom a)
      ((CommRingCat.isPushout_tensorProduct A₀ ↥A Γ(X₀, U)).inr_isoIsPushout_hom _ _ hPO')
    exact this

  have hsq : ∀ a : A₀, βB (ι a) = (pr.app U).hom (gA a) := fun a => by
    have := congrArg (fun ψ => ψ.hom a) hPO'.w
    exact this

  have hKX₀ : ∀ a : A₀, SemistableModel.baseToFunctionField toBase₀ a =
      algebraMap Γ(X₀, U) X₀.functionField (gA a) := by
    intro a
    change SemistableModel.baseToFunctionField toBase₀ a =
      X₀.germToFunctionField U
        ((X₀.presheaf.map (homOfLE le_top).op) (toBase₀.appTop ((Scheme.ΓSpecIso (.of A₀)).inv a)))
    dsimp only [SemistableModel.baseToFunctionField, Scheme.germToFunctionField, RingHom.coe_comp,
      Function.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
  have hKX : ∀ t : ↥A, SemistableModel.baseToFunctionField toBase t =
      algebraMap Γ(X, pr ⁻¹ᵁ U) X.functionField (βB t) := by
    intro t
    change SemistableModel.baseToFunctionField toBase t =
      X.germToFunctionField (pr ⁻¹ᵁ U)
        ((X.presheaf.map (homOfLE le_top).op) (toBase.appTop ((Scheme.ΓSpecIso (.of ↥A)).inv t)))
    dsimp only [SemistableModel.baseToFunctionField, Scheme.germToFunctionField, RingHom.coe_comp,
      Function.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
  have hφA : ∀ a : Γ(X₀, U), φ₀ (algebraMap Γ(X₀, U) X₀.functionField a) =
      algebraMap Γ(X, pr ⁻¹ᵁ U) X.functionField ((pr.app U).hom a) :=
    fun a => hφgerm U _ a

  have hgAinj : Function.Injective gA := by
    intro a b hab
    apply hι
    have h1 : algebraMap L F ((ι a : ↥A) : L) = algebraMap L F ((ι b : ↥A) : L) := by
      rw [← hj₀, ← hj₀, hKX₀, hKX₀, hab]
    exact Subtype.ext ((algebraMap L F).injective h1)

  letI instAlgF : Algebra A₀ F := ((algebraMap L F).comp ((algebraMap ↥A L).comp ι)).toAlgebra
  let fA : ↥A →ₐ[A₀] F :=
    { toRingHom := (algebraMap L F).comp (algebraMap ↥A L)
      commutes' := fun a => rfl }
  let gR : Γ(X₀, U) →ₐ[A₀] F :=
    { toRingHom := j₀.comp (algebraMap Γ(X₀, U) X₀.functionField)
      commutes' := fun a => by
        change j₀ (algebraMap Γ(X₀, U) X₀.functionField (gA a)) = algebraMap L F ((ι a : ↥A) : L)
        rw [← hKX₀, hj₀] }
  let liftT : ↥A ⊗[A₀] Γ(X₀, U) →ₐ[A₀] F :=
    Algebra.TensorProduct.lift fA gR (fun _ _ => Commute.all _ _)
  let ψ : Γ(X, pr ⁻¹ᵁ U) →+* F := liftT.toRingHom.comp Λ.symm.toRingHom
  have hψβ : ∀ t : ↥A, ψ (βB t) = algebraMap L F (t : L) := by
    intro t
    change liftT (Λ.symm (βB t)) = _
    rw [← hΛl, RingEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hψα : ∀ r : Γ(X₀, U), ψ ((pr.app U).hom r) = j₀ (algebraMap Γ(X₀, U) X₀.functionField r) := by
    intro r
    change liftT (Λ.symm ((pr.app U).hom r)) = _
    rw [← hΛr, RingEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

  letI instAlg₂ : Algebra Γ(X₀, U) Γ(X, pr ⁻¹ᵁ U) := (pr.app U).hom.toAlgebra
  have halgβ : ∀ t : ↥A, IsAlgebraic Γ(X₀, U) (βB t) := by
    intro t
    obtain ⟨p, hp0, hpt⟩ := halg t
    let e₀ : A₀ ≃+* ↥(ι.range) := RingEquiv.ofBijective ι.rangeRestrict
      ⟨fun a b h => hι (congrArg Subtype.val h : _), ι.rangeRestrict_surjective⟩
    let h : ↥(ι.range) →+* Γ(X₀, U) := gA.comp e₀.symm.toRingHom
    have he₀ : ∀ c : ↥(ι.range), ι (e₀.symm c) = (c : ↥A) := fun c =>
      congrArg Subtype.val (e₀.apply_symm_apply c)
    have hinj : Function.Injective h := fun a b hab => e₀.symm.injective (hgAinj hab)
    refine ⟨p.map h, (Polynomial.map_ne_zero_iff hinj).mpr hp0, ?_⟩
    have hcomp : (algebraMap Γ(X₀, U) Γ(X, pr ⁻¹ᵁ U)).comp h = βB.comp (algebraMap ↥(ι.range) ↥A) := by
      ext c
      change (pr.app U).hom (gA (e₀.symm c)) = βB (c : ↥A)
      rw [← hsq, he₀]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      hpt, map_zero]
  have hΛ : ∀ (t : ↥A) (a : Γ(X₀, U)), Λ (t ⊗ₜ a) = βB t * (pr.app U).hom a := by
    intro t a
    rw [show t ⊗ₜ[A₀] a = (t ⊗ₜ[A₀] (1 : Γ(X₀, U))) * ((1 : ↥A) ⊗ₜ[A₀] a) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    rw [map_mul, hΛl, hΛr]
  have halgB : ∀ b : Γ(X, pr ⁻¹ᵁ U), IsAlgebraic Γ(X₀, U) b := by
    intro b
    obtain ⟨x, rfl⟩ := Λ.surjective b
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact isAlgebraic_zero
    | tmul t a =>
      rw [hΛ]
      exact (halgβ t).mul (isAlgebraic_algebraMap a)
    | add x y hx hy =>
      rw [map_add]
      exact hx.add hy

  have hψinj : Function.Injective ψ := by
    refine injective_of_forall_isAlgebraic (pr.app U).hom ψ halgB ?_
    intro a b hab
    have h1 : j₀ (algebraMap Γ(X₀, U) X₀.functionField a) = j₀ (algebraMap Γ(X₀, U) X₀.functionField b) := by
      rw [← hψα, ← hψα]; exact hab
    exact IsFractionRing.injective Γ(X₀, U) X₀.functionField (j₀.injective h1)

  let θ : X.functionField →+* F := IsFractionRing.lift hψinj
  have hθB : ∀ b : Γ(X, pr ⁻¹ᵁ U), θ (algebraMap Γ(X, pr ⁻¹ᵁ U) X.functionField b) = ψ b :=
    fun b => IsFractionRing.lift_algebraMap hψinj b
  have hθbase : ∀ t : ↥A, θ (SemistableModel.baseToFunctionField toBase t) = algebraMap L F (t : L) := by
    intro t
    rw [hKX, hθB, hψβ]
  have hθφ₀ : ∀ g : X₀.functionField, θ (φ₀ g) = j₀ g := by
    have hext : θ.comp φ₀ = j₀ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors Γ(X₀, U)) ?_
      ext r
      change θ (φ₀ (algebraMap Γ(X₀, U) X₀.functionField r)) = j₀ (algebraMap Γ(X₀, U) X₀.functionField r)
      rw [hφA, hθB, hψα]
    intro g
    exact congrArg (fun χ : X₀.functionField →+* F => χ g) hext

  have hθsurj : Function.Surjective θ := by
    intro f
    obtain ⟨n, c, g, d, g', hne, hfeq⟩ := hspan f
    have hL : ∀ ℓ : L, algebraMap L F ℓ ∈ θ.fieldRange := by
      intro ℓ
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ↥A) ℓ
      rw [map_div₀]
      exact div_mem ⟨_, hθbase a⟩ ⟨_, hθbase b⟩
    have hj : ∀ g : X₀.functionField, j₀ g ∈ θ.fieldRange := fun g => ⟨φ₀ g, hθφ₀ g⟩
    have hsum : ∀ (c : Fin n → L) (g : Fin n → X₀.functionField),
        (∑ i, c i • j₀ (g i)) ∈ θ.fieldRange := by
      intro c g
      refine sum_mem fun i _ => ?_
      rw [Algebra.smul_def]
      exact mul_mem (hL _) (hj _)
    have hf : f = (∑ i, c i • j₀ (g i)) / (∑ i, d i • j₀ (g' i)) := by
      rw [eq_div_iff hne, hfeq]
    have hmem : f ∈ θ.fieldRange := by
      rw [hf]
      exact div_mem (hsum c g) (hsum d g')
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy⟩

  let θe : X.functionField ≃+* F := RingEquiv.ofBijective θ ⟨θ.injective, hθsurj⟩
  refine ⟨θe.symm, fun t => ?_, fun g => ?_⟩
  · apply θe.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hθbase t).symm
  · apply θe.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hθφ₀ g).symm

end S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_span
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_span (solution)
