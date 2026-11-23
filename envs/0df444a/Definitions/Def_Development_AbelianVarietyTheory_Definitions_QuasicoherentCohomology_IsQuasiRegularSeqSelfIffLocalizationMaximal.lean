-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:57.406172+00:00
-- url     : https://prove2.me/theorems/404416c1-715a-4c75-a0b4-290c44ef627f
-- title:
--   Is Quasi Regular Seq Self Iff Localization Maximal
-- statement:
--   Definitions and structural lemmas for Is Quasi Regular Seq Self Iff Localization Maximal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory
section Monomials
abbrev MonoDeg (ι : Type*) (a : ℕ) : Type _ := {α : ι →₀ ℕ // α.degree = a}
instance MonoDeg.finite (ι : Type*) [Finite ι] (a : ℕ) : Finite (MonoDeg ι a) :=
  (Finsupp.finite_of_degree_eq (σ := ι) a).to_subtype
noncomputable instance MonoDeg.fintype (ι : Type*) [Finite ι] (a : ℕ) : Fintype (MonoDeg ι a) :=
  Fintype.ofFinite _
noncomputable def MonoDeg.congr {ι κ : Type*} (e : ι ≃ κ) (a : ℕ) : MonoDeg ι a ≃ MonoDeg κ a :=
  (Finsupp.equivCongrLeft e).subtypeEquiv fun α => by
    simp [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]
variable {R : Type*} {ι : Type*}
def monoVal [CommMonoid R] (f : ι → R) (α : ι →₀ ℕ) : R := α.prod fun i k => f i ^ k
@[simp] theorem monoVal_zero [CommMonoid R] (f : ι → R) : monoVal f 0 = 1 := by
  simp [monoVal]
@[simp] theorem monoVal_single [CommMonoid R] (f : ι → R) (i : ι) (k : ℕ) :
    monoVal f (Finsupp.single i k) = f i ^ k := by
  simp [monoVal]
theorem monoVal_add [CommMonoid R] (f : ι → R) (α β : ι →₀ ℕ) :
    monoVal f (α + β) = monoVal f α * monoVal f β :=
  Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _)
theorem monoVal_eq_eval [CommSemiring R] (f : ι → R) (α : ι →₀ ℕ) :
    monoVal f α = MvPolynomial.eval f (MvPolynomial.monomial α 1) := by
  simp [monoVal, MvPolynomial.eval_monomial]
theorem monoVal_X [CommSemiring R] (α : ι →₀ ℕ) :
    monoVal (MvPolynomial.X : ι → MvPolynomial ι R) α = MvPolynomial.monomial α 1 := by
  simp [monoVal, MvPolynomial.monomial_eq]
variable [CommRing R]
theorem monoVal_mem_pow (f : ι → R) {a : ℕ} (α : MonoDeg ι a) :
    monoVal f α.1 ∈ Ideal.span (Set.range f) ^ a := by
  rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
  exact ⟨_, MvPolynomial.isHomogeneous_monomial 1 α.2, (monoVal_eq_eval f α.1).symm⟩
theorem span_range_pow_eq_span_monoVal (f : ι → R) (a : ℕ) :
    Ideal.span (Set.range f) ^ a =
      Ideal.span (Set.range fun α : MonoDeg ι a => monoVal f α.1) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f y).mp hy
    rw [MvPolynomial.eval_eq]
    refine Ideal.sum_mem _ fun d hd => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    refine ⟨⟨d, ?_⟩, rfl⟩
    have := hp (MvPolynomial.mem_support_iff.mp hd)
    rwa [Finsupp.degree_eq_weight_one]
  · rw [Ideal.span_le]
    rintro _ ⟨α, rfl⟩
    exact monoVal_mem_pow f α
variable [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]
theorem mem_pow_smul_top_iff (f : ι → R) (a : ℕ) (x : M) :
    x ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) ↔
      ∃ c : MonoDeg ι a → M, ∑ α, monoVal f α.1 • c α = x := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      rw [span_range_pow_eq_span_monoVal, Ideal.mem_span_range_iff_exists_fun] at hr
      obtain ⟨b, rfl⟩ := hr
      exact ⟨fun α => b α • m, by simp [Finset.sum_smul, mul_comm, smul_smul]⟩
    · rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨c + d, by simp [Finset.sum_add_distrib]⟩
  · rintro ⟨c, rfl⟩
    exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem_smul (monoVal_mem_pow f α) trivial
end Monomials
section Piece
variable {R : Type*} [CommRing R]
abbrev powGr (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ) : Type _ :=
  ↥(I ^ a • ⊤ : Submodule R M) ⧸
    (I ^ (a + 1) • ⊤ : Submodule R M).submoduleOf (I ^ a • ⊤ : Submodule R M)
namespace powGr
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)
def mk : ↥(I ^ a • ⊤ : Submodule R M) →ₗ[R] powGr I M a := Submodule.mkQ _
theorem mk_surjective : Function.Surjective (mk I M a) := Submodule.mkQ_surjective _
variable {I M a} in

theorem mk_eq_zero (x : ↥(I ^ a • ⊤ : Submodule R M)) :
    mk I M a x = 0 ↔ (x : M) ∈ (I ^ (a + 1) • ⊤ : Submodule R M) :=
  Submodule.Quotient.mk_eq_zero _
theorem pow_succ_smul_le : (I ^ (a + 1) • ⊤ : Submodule R M) ≤ I ^ a • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ a))
theorem isTorsionBySet : Module.IsTorsionBySet R (powGr I M a) I := by
  rintro x ⟨r, hr⟩
  obtain ⟨x, rfl⟩ := mk_surjective I M a x
  change r • mk I M a x = 0
  rw [← map_smul, mk_eq_zero, pow_succ', mul_smul]
  exact Submodule.smul_mem_smul hr x.2
instance module : Module (R ⧸ I) (powGr I M a) := (isTorsionBySet I M a).module
variable {I M a} in

@[simp] theorem mk_smul (r : R) (x : powGr I M a) : Ideal.Quotient.mk I r • x = r • x := rfl
instance isScalarTower {A : Type*} [Semiring A] [SMul A R] [IsScalarTower A R R] [Module A M]
    [IsScalarTower A R M] : IsScalarTower A (R ⧸ I) (powGr I M a) where
  smul_assoc s r x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact smul_assoc s r x
variable {M} in

def map {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    powGr I M a →ₗ[R ⧸ I] powGr I N a :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    Submodule.mapQ _ _
      (g.restrict fun _ hx => Submodule.smul_top_le_comap_smul_top (I ^ a) g hx)
      fun _ hx => Submodule.smul_top_le_comap_smul_top (I ^ (a + 1)) g hx
@[simp] theorem map_id : map I a (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := mk_surjective I M a x
  rfl
def toQuot : powGr I M a →ₗ[R] M ⧸ (I ^ (a + 1) • ⊤ : Submodule R M) :=
  Submodule.mapQ _ _ (Submodule.subtype _) le_rfl
variable {I M a} in

@[simp] theorem toQuot_mk (x : ↥(I ^ a • ⊤ : Submodule R M)) :
    toQuot I M a (mk I M a x) = Submodule.Quotient.mk (x : M) := rfl
variable {I a} in

def mulElem (r : R) (hr : r ∈ I ^ a) : (M ⧸ (I • ⊤ : Submodule R M)) →ₗ[R ⧸ I] powGr I M a :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    Submodule.mapQ _ _
      ((LinearMap.lsmul R M r).codRestrict _ fun _ => Submodule.smul_mem_smul hr trivial)
      fun x hx => by
        change r • x ∈ (I ^ (a + 1) • ⊤ : Submodule R M)
        rw [pow_succ, mul_smul]
        exact Submodule.smul_mem_smul hr hx
variable {I M a} in

theorem mulElem_mk (r : R) (hr : r ∈ I ^ a) (x : M) :
    mulElem M r hr (Submodule.Quotient.mk x) =
      mk I M a ⟨r • x, Submodule.smul_mem_smul hr trivial⟩ := rfl
end powGr
end Piece
section Quasi
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
def IsQuasiRegularSeq (M : Type*) [AddCommGroup M] [Module R M] (f : ι → R) : Prop :=
  ∀ (a : ℕ) (c : MonoDeg ι a → M),
    ∑ α, monoVal f α.1 • c α ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) →
      ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M)
variable (M : Type*) [AddCommGroup M] [Module R M]
noncomputable def monoToPowGr (f : ι → R) (a : ℕ) :
    (MonoDeg ι a → M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) →ₗ[R ⧸
      Ideal.span (Set.range f)] powGr (Ideal.span (Set.range f)) M a :=
  ∑ α : MonoDeg ι a, powGr.mulElem M (monoVal f α.1) (monoVal_mem_pow f α) ∘ₗ LinearMap.proj α
variable {M}
theorem monoToPowGr_apply (f : ι → R) (a : ℕ)
    (c : MonoDeg ι a → M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) :
    monoToPowGr M f a c = ∑ α, powGr.mulElem M (monoVal f α.1) (monoVal_mem_pow f α) (c α) := by
  simp only [monoToPowGr, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
theorem monoToPowGr_mk (f : ι → R) (a : ℕ) (c : MonoDeg ι a → M) :
    monoToPowGr M f a (fun α => Submodule.Quotient.mk (c α)) =
      powGr.mk _ M a ⟨∑ α, monoVal f α.1 • c α, (mem_pow_smul_top_iff f a _).mpr ⟨c, rfl⟩⟩ := by
  rw [monoToPowGr_apply]
  simp only [powGr.mulElem_mk]
  rw [← map_sum]
  congr 1
  ext
  simp
variable (M) in

theorem monoToPowGr_surjective (f : ι → R) (a : ℕ) : Function.Surjective (monoToPowGr M f a) := by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := powGr.mk_surjective _ M a x
  obtain ⟨c, rfl⟩ := (mem_pow_smul_top_iff f a x).mp hx
  exact ⟨_, monoToPowGr_mk f a c⟩
theorem monoToPowGr_injective_iff (f : ι → R) (a : ℕ) :
    Function.Injective (monoToPowGr M f a) ↔ ∀ c : MonoDeg ι a → M,
      ∑ α, monoVal f α.1 • c α ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) →
        ∀ α, c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h c hc α
    have := h _ ((monoToPowGr_mk f a c).trans ((powGr.mk_eq_zero _).mpr hc))
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun this α)
  · intro h c hc
    choose d hd using fun α => Submodule.Quotient.mk_surjective _ (c α)
    obtain rfl : c = fun α => Submodule.Quotient.mk (d α) := funext fun α => (hd α).symm
    rw [monoToPowGr_mk, powGr.mk_eq_zero] at hc
    exact funext fun α => (Submodule.Quotient.mk_eq_zero _).mpr (h d hc α)
theorem isQuasiRegularSeq_iff_injective (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ a, Function.Injective (monoToPowGr M f a) :=
  forall_congr' fun a => (monoToPowGr_injective_iff f a).symm
theorem isQuasiRegularSeq_iff_bijective (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ a, Function.Bijective (monoToPowGr M f a) :=
  (isQuasiRegularSeq_iff_injective f).trans <| forall_congr' fun a =>
    ⟨fun h => ⟨h, monoToPowGr_surjective M f a⟩, fun h => h.1⟩
namespace IsQuasiRegularSeq
noncomputable def powGrEquiv {f : ι → R} (h : IsQuasiRegularSeq M f) (a : ℕ) :
    (MonoDeg ι a → M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) ≃ₗ[R ⧸
      Ideal.span (Set.range f)] powGr (Ideal.span (Set.range f)) M a :=
  LinearEquiv.ofBijective (monoToPowGr M f a) ((isQuasiRegularSeq_iff_bijective f).mp h a)
@[simp] theorem powGrEquiv_apply {f : ι → R} (h : IsQuasiRegularSeq M f) (a : ℕ)
    (c : MonoDeg ι a → M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) :
    h.powGrEquiv a c = monoToPowGr M f a c := rfl
end IsQuasiRegularSeq
end Quasi
section Basis
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
noncomputable def quotSMulTopEquivQuot (I : Ideal R) :
    (R ⧸ (I • ⊤ : Submodule R R)) ≃ₗ[R ⧸ I] R ⧸ I :=
  LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    Submodule.quotEquivOfEq _ _ (by simp)
noncomputable def IsQuasiRegularSeq.powGrBasis {f : ι → R} (h : IsQuasiRegularSeq R f) (a : ℕ) :
    Module.Basis (MonoDeg ι a) (R ⧸ Ideal.span (Set.range f))
      (powGr (Ideal.span (Set.range f)) R a) :=
  Module.Basis.ofEquivFun <| (h.powGrEquiv a).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => quotSMulTopEquivQuot _
end Basis
section Flat
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
noncomputable def monoToQuotPow (f : ι → R) (a : ℕ) :
    (MonoDeg ι a → R ⧸ Ideal.span (Set.range f)) →ₗ[R] R ⧸ Ideal.span (Set.range f) ^ (a + 1) :=
  ∑ α : MonoDeg ι a,
    Submodule.mapQ (Ideal.span (Set.range f)) (Ideal.span (Set.range f) ^ (a + 1))
      (LinearMap.lsmul R R (monoVal f α.1))
      (fun _ hx => by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (monoVal_mem_pow f α) hx) ∘ₗ LinearMap.proj α
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]
end Flat
section Examples
variable {R : Type*} [CommRing R]
theorem isQuasiRegularSeq_X (ι : Type*) [Finite ι] :
    IsQuasiRegularSeq (MvPolynomial ι R) (MvPolynomial.X : ι → MvPolynomial ι R) := by
  classical
  intro a c hc α
  simp only [smul_eq_mul, Ideal.mul_top, monoVal_X] at hc ⊢
  have h1 := (MvPolynomial.mem_pow_idealOfVars_iff' _ _).mp hc α.1 (by simp [α.2])
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single α] at h1
  · rw [← pow_one (Ideal.span _)]
    refine (MvPolynomial.mem_pow_idealOfVars_iff' _ _).mpr fun x hx => ?_
    obtain rfl : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (by omega)
    simpa [MvPolynomial.coeff_monomial_mul'] using h1
  · intro β _ hβ
    rw [MvPolynomial.coeff_monomial_mul', if_neg]
    intro hle
    obtain ⟨γ, hγ⟩ := exists_add_of_le hle
    have hd := congrArg Finsupp.degree hγ
    rw [map_add, α.2, β.2] at hd
    obtain rfl : γ = 0 := (Finsupp.degree_eq_zero_iff γ).mp (by omega)
    exact hβ (Subtype.ext (by simpa using hγ.symm))
  · simp
noncomputable instance MonoDeg.unique (ι : Type*) [Unique ι] (a : ℕ) : Unique (MonoDeg ι a) where
  default := ⟨Finsupp.single default a, by simp⟩
  uniq α := by
    obtain ⟨α, rfl⟩ := α
    ext
    simp [Finsupp.degree_eq_sum]
theorem isQuasiRegularSeq_singleton_iff {M : Type*} [AddCommGroup M] [Module R M] (x : R) :
    IsQuasiRegularSeq M ![x] ↔
      ∀ (a : ℕ) (m m' : M), x ^ a • m = x ^ (a + 1) • m' → ∃ m'', m = x • m'' := by
  have hI : Ideal.span (Set.range ![x]) = Ideal.span {x} := by simp
  have hm : ∀ (y : R) (m : M), m ∈ (Ideal.span {y} • ⊤ : Submodule R M) ↔ ∃ m', m = y • m' := by
    intro y m
    simp [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, eq_comm]
  have hv : ∀ a, monoVal ![x] (default : MonoDeg (Fin 1) a).1 = x ^ a :=
    fun a => monoVal_single _ _ _
  simp only [IsQuasiRegularSeq, hI, Ideal.span_singleton_pow, hm, Fintype.sum_unique, hv,
    Unique.forall_iff]
  exact ⟨fun h a m m' hm => h a (fun _ => m) ⟨m', hm⟩, fun h a c ⟨m', hm⟩ => h a _ m' hm⟩
theorem isQuasiRegularSeq_singleton {M : Type*} [AddCommGroup M] [Module R M] {x : R}
    (hx : IsSMulRegular M x) : IsQuasiRegularSeq M ![x] :=
  (isQuasiRegularSeq_singleton_iff x).mpr fun a _ m' h =>
    ⟨m', hx.pow a (by simpa only [pow_succ, mul_smul] using h)⟩
example : IsQuasiRegularSeq ℤ ![(2 : ℤ)] :=
  isQuasiRegularSeq_singleton (IsSMulRegular.of_ne_zero two_ne_zero)
example : ¬ IsQuasiRegularSeq ℤ ![(0 : ℤ)] := fun h => by
  simpa using (isQuasiRegularSeq_singleton_iff _).mp h 1 1 0 (by simp)
example : ¬ IsQuasiRegularSeq (ZMod 4) ![(2 : ℤ)] := fun h => by
  have := (isQuasiRegularSeq_singleton_iff _).mp h 2 1 0 (by decide)
  revert this
  decide
example : monoVal ![(2 : ℤ), 3] (Finsupp.single 0 2 + Finsupp.single 1 1) = 12 := by
  simp [monoVal_add]
example (a : ℕ) : Nontrivial (powGr (MvPolynomial.idealOfVars (Fin 2) ℚ)
    (MvPolynomial (Fin 2) ℚ) a) := by
  have hI : MvPolynomial.idealOfVars (Fin 2) ℚ ≠ ⊤ := fun h => by
    have := (MvPolynomial.C_mem_pow_idealOfVars_iff (σ := Fin 2) 1 (1 : ℚ)).mp (by simp [h])
    simp at this
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  exact nontrivial_of_ne _ _
    (((isQuasiRegularSeq_X (R := ℚ) (Fin 2)).powGrBasis a).ne_zero ⟨Finsupp.single 0 a, by simp⟩)
end Examples
end GlobalTheory


