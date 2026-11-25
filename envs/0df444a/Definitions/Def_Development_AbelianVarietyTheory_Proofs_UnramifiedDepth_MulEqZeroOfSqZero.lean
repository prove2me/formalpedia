-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulEqZeroOfSqZero
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulEqZeroOfSqZero
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:36:37.899357+00:00
-- url     : https://prove2.me/theorems/93ed9ce0-43e9-47c7-8d71-83f461f08472
-- title:
--   Mul Eq Zero Of Sq Zero
-- statement:
--   Definitions and structural lemmas for Mul Eq Zero Of Sq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MulEqZeroOfSqZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.GroupPointsBX
variable {R₀ : Type} [CommRing R₀]
theorem spMap_algHom_id (P : Type) [CommRing P] [Algebra R₀ P] :
    spMap (AlgHom.id R₀ P) = 𝟙 (sp (R₀ := R₀) P) := by
  apply Over.OverMorphism.ext
  simp only [spMap_left, Over.id_left]
  exact Spec.map_id _
theorem exists_lift (X : Over (Spec (CommRingCat.of R₀))) [Smooth X.hom]
    {B C : Type} [CommRing B] [Algebra R₀ B] [CommRing C] [Algebra R₀ C] [IsLocalRing C]
    (π : B →ₐ[R₀] C) (hπ : Function.Surjective π) (hk : IsNilpotent (RingHom.ker π))
    (z : sp (R₀ := R₀) C ⟶ X) : ∃ y : sp (R₀ := R₀) B ⟶ X, spMap π ≫ y = z := by
  let x₀ : Spec (CommRingCat.of C) ⟶ X.left := z.left
  have hw : x₀ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R₀ C)) := Over.w z
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x₀ (closedPoint C))) isOpen_univ
  have hx : Set.range x₀ ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of C) x₀ hxV).ge
      (Set.mem_univ y)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec x₀ hx)
  have hφ' : Spec.map φ ≫ hV.fromSpec = x₀ := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := Spec.map_surjective (hV.fromSpec ≫ X.hom)
  have hs : RingHom.Smooth α.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hα]
    infer_instance
  have hφα : α ≫ φ = CommRingCat.ofHom (algebraMap R₀ C) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, ← Category.assoc, hφ', hw]
  letI : Algebra R₀ Γ(X.left, V) := α.hom.toAlgebra
  haveI : Algebra.Smooth R₀ Γ(X.left, V) := hs
  let φ' : Γ(X.left, V) →ₐ[R₀] C := ⟨φ.hom, fun r => congr($hφα r)⟩
  let ψ := Algebra.FormallySmooth.liftOfSurjective φ' π hπ hk
  have hψ : π.comp ψ = φ' := Algebra.FormallySmooth.comp_liftOfSurjective φ' π hπ hk
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec) ?_, ?_⟩
  · simp only [sp, Over.mk_hom]
    rw [Category.assoc, ← hα, ← Spec.map_comp]
    congr 1
    ext r
    exact ψ.commutes r
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom π.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec = x₀
    rw [← hφ', ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact congr($hψ a)
section
variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
structure Coord (g : ℕ)
    (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)) :
    Prop where
  zero : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1
  nat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S),
    (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))
  inj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b
  ker : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ → (∀ a ∈ RingHom.ker ρ, IsNilpotent a) →
    ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
    ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a
variable {G} {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
open TrivSqZeroExt in

theorem Coord.mul_inr (h : Coord G g x) {K : Type} [AddCommGroup K] [Module R₀ K]
    [Module R₀ᵐᵒᵖ K] [IsCentralScalar R₀ K] (a b : Fin g → K) :
    x (TrivSqZeroExt R₀ (K × K)) (fun i => inr (a i, 0)) *
      x (TrivSqZeroExt R₀ (K × K)) (fun i => inr (0, b i)) =
      x (TrivSqZeroExt R₀ (K × K)) (fun i => inr (a i, b i)) := by
  have nil : ∀ {M : Type} [AddCommGroup M] [Module R₀ M] [Module R₀ᵐᵒᵖ M] [IsCentralScalar R₀ M]
      (m : M), IsNilpotent (inr m : TrivSqZeroExt R₀ M) := fun m =>
    ⟨2, by rw [pow_two, inr_mul_inr]⟩
  have hfst : ∀ c : TrivSqZeroExt R₀ (K × K), c ∈ RingHom.ker (fstHom R₀ R₀ (K × K)) →
      c = inr c.snd := fun c hc => by
    have : c.fst = 0 := hc
    ext <;> simp [this]
  obtain ⟨c, hc, hxc⟩ := h.ker _ R₀ (fstHom R₀ R₀ (K × K)) (fun r => ⟨inl r, rfl⟩)
    (fun c hc => by rw [hfst c hc]; exact nil _)
    (x (TrivSqZeroExt R₀ (K × K)) (fun i => inr (a i, 0)) *
      x (TrivSqZeroExt R₀ (K × K)) (fun i => inr (0, b i))) (by
      rw [MonObj.comp_mul, h.nat _ _ _ _ (fun i => nil _), h.nat _ _ _ _ (fun i => nil _)]
      have e : x R₀ (fun _ => 0) = 1 := h.zero R₀
      simp [e])
  have cnil : ∀ i, IsNilpotent (c i) := fun i => by rw [hfst _ (hc i)]; exact nil _
  have e0 : x (TrivSqZeroExt R₀ K) (fun _ => 0) = 1 := h.zero _
  have h1 := congrArg (spMap (map (LinearMap.fst R₀ K K)) ≫ ·) hxc
  have h2 := congrArg (spMap (map (LinearMap.snd R₀ K K)) ≫ ·) hxc
  simp only [MonObj.comp_mul] at h1 h2
  rw [h.nat _ _ _ _ (fun i => nil _), h.nat _ _ _ _ (fun i => nil _), h.nat _ _ _ _ cnil] at h1 h2
  simp only [map_inr, LinearMap.fst_apply, LinearMap.snd_apply, inr_zero, e0] at h1 h2
  rw [_root_.mul_one] at h1
  rw [_root_.one_mul] at h2
  have h1' := h.inj _ _ _ (fun i => nil _) (fun i => (cnil i).map _) h1
  have h2' := h.inj _ _ _ (fun i => nil _) (fun i => (cnil i).map _) h2
  rw [hxc]
  congr 1
  funext i
  rw [hfst _ (hc i)]
  congr 1
  have e1 := congrArg snd (congrFun h1' i)
  have e2 := congrArg snd (congrFun h2' i)
  simp only [snd_inr, snd_map, LinearMap.fst_apply, LinearMap.snd_apply] at e1 e2
  exact Prod.ext e1.symm e2.symm
open TrivSqZeroExt in

theorem Coord.mul_eq (h : Coord G g x) {S : Type} [CommRing S] [Algebra R₀ S]
    (K : Submodule R₀ S) (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = 0) (a b : Fin g → K) :
    x S (fun i => a i) * x S (fun i => b i) = x S (fun i => (a i : S) + b i) := by
  letI : Module R₀ᵐᵒᵖ K := Module.compHom K ((RingHom.id R₀).fromOpposite mul_comm)
  haveI : IsCentralScalar R₀ K := ⟨fun _ _ => rfl⟩
  let l : K × K →ₗ[R₀] S := K.subtype ∘ₗ (LinearMap.fst R₀ K K + LinearMap.snd R₀ K K)
  let φ : TrivSqZeroExt R₀ (K × K) →ₐ[R₀] S :=
    liftEquivOfComm ⟨l, fun u v => hK _ (u.1 + u.2).2 _ (v.1 + v.2).2⟩
  have hφ : ∀ u v : K, φ (inr (u, v)) = (u : S) + v := fun u v => by
    simp only [φ]
    rw [liftEquivOfComm_apply, lift_apply_inr]
    rfl
  have nil : ∀ m : K × K, IsNilpotent (inr m : TrivSqZeroExt R₀ (K × K)) := fun m =>
    ⟨2, by rw [pow_two, inr_mul_inr]⟩
  have e := congrArg (spMap φ ≫ ·) (h.mul_inr a b)
  simp only [MonObj.comp_mul] at e
  rw [h.nat _ _ _ _ (fun i => nil _), h.nat _ _ _ _ (fun i => nil _),
    h.nat _ _ _ _ (fun i => nil _)] at e
  simpa only [hφ, Submodule.coe_zero, add_zero, zero_add] using e
end
def coords (g : ℕ) (K : Type) [AddCommGroup K] [Module R₀ K] :
    (Fin g → R₀) ⊗[R₀] K ≃ₗ[R₀] (Fin g → K) :=
  TensorProduct.comm R₀ _ _ ≪≫ₗ TensorProduct.piScalarRight R₀ R₀ K (Fin g)
theorem coords_lTensor (g : ℕ) {K K' : Type} [AddCommGroup K] [Module R₀ K] [AddCommGroup K']
    [Module R₀ K'] (f : K →ₗ[R₀] K') (v : (Fin g → R₀) ⊗[R₀] K) (i : Fin g) :
    coords g K' (LinearMap.lTensor _ f v) i = f (coords g K v i) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul r k => simp [coords]
  | add a b ha hb => simp [ha, hb]
theorem mul_eq_zero_of_sqZero {R S : LAlg R₀} {π : LHom R S} (hπ : π.SqZero) :
    ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = 0 := fun a ha b hb => by
  have h : a * b ∈ RingHom.ker π.1 ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [hπ.2] at h
  exact (Ideal.mem_bot).1 h
theorem isNilpotent_of_sqZero {R S : LAlg R₀} {π : LHom R S} (hπ : π.SqZero) {a : (R : Type)}
    (ha : a ∈ π.ker) : IsNilpotent a :=
  ⟨2, by rw [pow_two, mul_eq_zero_of_sqZero hπ a ha a ha]⟩
section
variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G]
def ptMap {R S : LAlg R₀} (f : LHom R S) :
    Additive (sp (R₀ := R₀) (R : Type) ⟶ G) →+ Additive (sp (R₀ := R₀) (S : Type) ⟶ G) where
  toFun z := Additive.ofMul (spMap f.1 ≫ z.toMul)
  map_zero' := congrArg Additive.ofMul (MonObj.comp_one _)
  map_add' a b := congrArg Additive.ofMul (MonObj.comp_mul _ _ _)
variable {G} {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
def ptTg (h : Coord G g x) {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero) :
    (Fin g → R₀) ⊗[R₀] π.ker →+ Additive (sp (R₀ := R₀) (R : Type) ⟶ G) where
  toFun v := Additive.ofMul (x R fun i => coords g π.ker v i)
  map_zero' := by
    rw [map_zero]
    exact congrArg Additive.ofMul (h.zero R)
  map_add' a b := by
    rw [map_add]
    exact congrArg Additive.ofMul (h.mul_eq π.ker (mul_eq_zero_of_sqZero hπ) _ _).symm
def ptBX [Smooth G.hom] (h : Coord G g x)
    (fib : ∀ {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
      (f₂ : LHom R₂ R), IsFibreSq p₁ p₂ f₁ f₂ →
      CarriesFibre (ptMap G p₁) (ptMap G p₂) (ptMap G f₁) (ptMap G f₂)) : BX R₀ where
  G R := Additive (sp (R₀ := R₀) (R : Type) ⟶ G)
  map f := ptMap G f
  map_id R z := by
    change spMap (AlgHom.id R₀ R) ≫ z.toMul = z.toMul
    rw [spMap_algHom_id, Category.id_comp]
  map_comp f f' z := by
    change spMap (f'.1.comp f.1) ≫ z.toMul = spMap f'.1 ≫ spMap f.1 ≫ z.toMul
    rw [← Category.assoc, spMap_comp]
  gg := Fin g → R₀
  tg π hπ := ptTg h π hπ
  tg_nat π π' hπ hπ' f hf v := by
    change x _ _ = spMap f.1 ≫ x _ _
    rw [h.nat _ _ _ _ (fun i => isNilpotent_of_sqZero hπ (Submodule.coe_mem _))]
    congr 1
    funext i
    rw [coords_lTensor]
    rfl
  surj π hπ z := exists_lift G π.1 hπ.1 ⟨2, hπ.2⟩ z.toMul
  tg_inj π hπ v w e := by
    have e' := h.inj _ _ _ (fun i => isNilpotent_of_sqZero hπ (Submodule.coe_mem _))
      (fun i => isNilpotent_of_sqZero hπ (Submodule.coe_mem _)) e
    exact (coords g π.ker).injective (funext fun i => Subtype.ext (congrFun e' i))
  tg_ker := fun {R S} π hπ z => by
    constructor
    · intro e
      obtain ⟨a, ha, e'⟩ := h.ker _ _ π.1 hπ.1 (fun a ha => isNilpotent_of_sqZero hπ ha) z.toMul e
      refine ⟨(coords g π.ker).symm fun i => ⟨a i, ha i⟩, ?_⟩
      change x R (fun i => coords g π.ker ((coords g π.ker).symm _) i) = z.toMul
      rw [LinearEquiv.apply_symm_apply, e']
    · rintro ⟨v, rfl⟩
      change spMap π.1 ≫ x _ _ = 1
      rw [h.nat _ _ _ _ (fun i => isNilpotent_of_sqZero hπ (Submodule.coe_mem _)), ← h.zero S]
      congr 1
      funext i
      exact (coords g π.ker v i).2
  P R _ _ := (R : Type)ˣ
  smul l u := l * u
  one_smul u := one_mul u
  mul_smul l l' u := mul_assoc l l' u
  nonempty R _ _ := ⟨1⟩
  trans u w := ⟨w * u⁻¹, by simp, fun l h => by rw [← h]; simp⟩
  pmap f _ _ u := Units.map (f.1 : _ →* _) u
  pmap_smul f _ _ l u := map_mul _ l u
  pmap_id u := heq_of_eq (by ext; rfl)
  pmap_comp f g _ _ u := heq_of_eq (by ext; rfl)
  add1 u u' := u * u'
  add2 u u' := u * u'
  zero1 _ := 1
  zero2 _ := 1
  addFst_assoc u u' u'' := heq_of_eq (mul_assoc u u' u'')
  addSnd_assoc u u' u'' := heq_of_eq (mul_assoc u u' u'')
  addFst_comm u u' := heq_of_eq (mul_comm u u')
  addSnd_comm u u' := heq_of_eq (mul_comm u u')
  zeroFst_add u := heq_of_eq (one_mul u)
  zeroSnd_add u := heq_of_eq (one_mul u)
  addFst_smul l l' u u' := mul_mul_mul_comm l u l' u'
  addSnd_smul l l' u u' := mul_mul_mul_comm l u l' u'
  interchange u u' w w' := mul_mul_mul_comm u u' w w'
  addFst_nat f _ _ _ u u' := heq_of_eq (map_mul _ u u')
  addSnd_nat f _ _ _ u u' := heq_of_eq (map_mul _ u u')
  zeroFst_nat f _ := heq_of_eq (map_one _)
  zeroSnd_nat f _ := heq_of_eq (map_one _)
  sw u := u
  sw_smul _ _ := rfl
  sw_nat _ _ _ _ := rfl
  swap_addFst _ _ := rfl
  sw_sw _ := rfl
  fibre_G := fib
  fibre_P p₁ p₂ f₁ f₂ hf := by
    rintro ⟨x₁, y₁, u₁⟩ ⟨x₂, y₂, u₂⟩ hab
    simp only [Sigma.mk.inj_iff, heq_iff_eq] at hab
    obtain ⟨hx, hy, hu⟩ := hab
    obtain ⟨cx, ⟨hcx₁, hcx₂⟩, hcxu⟩ := fib p₁ p₂ f₁ f₂ hf x₁ x₂ hx
    obtain ⟨cy, ⟨hcy₁, hcy₂⟩, hcyu⟩ := fib p₁ p₂ f₁ f₂ hf y₁ y₂ hy
    have hu' : f₁.1 (u₁ : _) = f₂.1 (u₂ : _) := congrArg Units.val hu
    obtain ⟨cu, ⟨hcu₁, hcu₂⟩, hcuu⟩ := hf.2.2.2 _ _ hu'
    have hunit : IsUnit cu := by
      have h1 := u₁.isUnit
      rw [← hcu₁] at h1
      exact p₁.2.map_nonunit cu h1
    refine ⟨⟨cx, cy, hunit.unit⟩, ⟨?_, ?_⟩, ?_⟩
    · simp only [Sigma.mk.inj_iff, heq_iff_eq]
      exact ⟨hcx₁, hcy₁, Units.ext hcu₁⟩
    · simp only [Sigma.mk.inj_iff, heq_iff_eq]
      exact ⟨hcx₂, hcy₂, Units.ext hcu₂⟩
    · rintro ⟨dx, dy, du⟩ ⟨hd₁, hd₂⟩
      simp only [Sigma.mk.inj_iff, heq_iff_eq] at hd₁ hd₂
      simp only [Sigma.mk.inj_iff, heq_iff_eq]
      exact ⟨hcxu dx ⟨hd₁.1, hd₂.1⟩, hcyu dy ⟨hd₁.2.1, hd₂.2.1⟩,
        Units.ext (hcuu du.1 ⟨congrArg Units.val hd₁.2.2, congrArg Units.val hd₂.2.2⟩)⟩
end
end GlobalTheory.GroupPointsBX


