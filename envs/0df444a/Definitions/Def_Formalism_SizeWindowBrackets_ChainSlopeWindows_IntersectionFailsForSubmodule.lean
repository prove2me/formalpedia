-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_IntersectionFailsForSubmodule
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_IntersectionFailsForSubmodule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:07.876486+00:00
-- url     : https://prove2.me/theorems/7b082200-cb8c-4dff-b8f7-ea8bdedcae7b
-- title:
--   Intersection Fails For Submodule
-- statement:
--   Definitions and structural lemmas for Intersection Fails For Submodule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/IntersectionFailsForSubmodule.lean

import Definitions.Def_Formalism_SizeWindowBrackets_CutFailsForRSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.DiagonalSublatticeLength
open scoped Pointwise
open Module
set_option maxHeartbeats 800000
noncomputable section
section generic
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
def diagSub {F ι : Type*} [AddCommGroup F] [Module R F] [Finite ι] (c : Basis ι R F) (ϖ : R) (k : ι → ℕ) :
    Submodule R F :=
  (Submodule.pi Set.univ (fun i => (Ideal.span {ϖ ^ k i} : Submodule R R))).comap
    c.equivFun.toLinearMap
theorem mem_diagSub {F ι : Type*} [AddCommGroup F] [Module R F] [Finite ι] (c : Basis ι R F) (ϖ : R)
    (k : ι → ℕ) (x : F) : x ∈ diagSub c ϖ k ↔ ∀ i, ϖ ^ k i ∣ c.repr x i := by
  simp [diagSub, Submodule.mem_pi, Ideal.mem_span_singleton]
theorem length_quot_diagSub {F ι : Type*} [AddCommGroup F] [Module R F] [Fintype ι] [DecidableEq ι]
    (c : Basis ι R F) {ϖ : R} (hϖ : Irreducible ϖ) (k : ι → ℕ) :
    Module.length R (F ⧸ diagSub c ϖ k) = ((∑ i, k i : ℕ) : ℕ∞) := by
  let I : ι → Submodule R R := fun i => (Ideal.span {ϖ ^ k i} : Submodule R R)
  have hmap : (diagSub c ϖ k).map (c.equivFun : F →ₗ[R] (ι → R)) = Submodule.pi Set.univ I :=
    Submodule.map_comap_eq_of_surjective (f := (c.equivFun : F →ₗ[R] (ι → R))) c.equivFun.surjective _
  let e1 := Submodule.Quotient.equiv (diagSub c ϖ k) (Submodule.pi Set.univ I) c.equivFun hmap
  let e2 := Submodule.quotientPi I
  rw [(e1.trans e2).length_eq, Module.length_pi_of_fintype]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (I i) = (IsLocalRing.maximalIdeal R ^ k i : Ideal R) := by
    simp only [I, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [this]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R (k i)
theorem length_tower {X : Type*} [AddCommGroup X] [Module R X] (A B C : Submodule R X)
    (hAB : A ≤ B) (hBC : B ≤ C) :
    Module.length R (C ⧸ A.comap C.subtype) =
      Module.length R (B ⧸ A.comap B.subtype) + Module.length R (C ⧸ B.comap C.subtype) := by
  let f : (B ⧸ A.comap B.subtype) →ₗ[R] (C ⧸ A.comap C.subtype) :=
    (A.comap B.subtype).mapQ (A.comap C.subtype) (Submodule.inclusion hBC) (fun x hx => hx)
  let g : (C ⧸ A.comap C.subtype) →ₗ[R] (C ⧸ B.comap C.subtype) :=
    (A.comap C.subtype).mapQ (B.comap C.subtype) LinearMap.id (fun x hx => hAB hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker] at hy
      have hy' : (Submodule.Quotient.mk (Submodule.inclusion hBC x) : C ⧸ A.comap C.subtype) = 0 := hy
      rw [Submodule.Quotient.mk_eq_zero] at hy'
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact hy'
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H s => exact ⟨Submodule.Quotient.mk s, rfl⟩
  have hex : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext y
    induction y using Submodule.Quotient.induction_on with
    | H s =>
      simp only [LinearMap.mem_ker, g, Submodule.mapQ_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      constructor
      · intro hs
        refine ⟨Submodule.Quotient.mk ⟨s, hs⟩, ?_⟩
        rfl
      · rintro ⟨z, hz⟩
        induction z using Submodule.Quotient.induction_on with
        | H b =>
          have hz' : (Submodule.Quotient.mk (Submodule.inclusion hBC b) : C ⧸ A.comap C.subtype) =
              Submodule.Quotient.mk s := hz
          rw [Submodule.Quotient.eq] at hz'
          have h1 : ((Submodule.inclusion hBC b - s : C) : X) ∈ B := hAB hz'
          have h2 : ((Submodule.inclusion hBC b : C) : X) ∈ B := b.2
          show (s : X) ∈ B
          have : (s : X) = ((Submodule.inclusion hBC b : C) : X) -
              ((Submodule.inclusion hBC b - s : C) : X) := by
            rw [Submodule.coe_sub]; abel
          rw [this]
          exact B.sub_mem h2 h1
  rw [Module.length_eq_add_of_exact f g hf hg hex]
theorem length_inf_le {X : Type*} [AddCommGroup X] [Module R X] (A B V : Submodule R X) :
    Module.length R ((B ⊓ V : Submodule R X) ⧸ (A ⊓ V).comap (B ⊓ V).subtype) ≤
      Module.length R (B ⧸ A.comap B.subtype) := by
  let ι : (B ⊓ V : Submodule R X) →ₗ[R] B := Submodule.inclusion inf_le_left
  let q : ((B ⊓ V : Submodule R X) ⧸ (A ⊓ V).comap (B ⊓ V).subtype) →ₗ[R] (B ⧸ A.comap B.subtype) :=
    ((A ⊓ V).comap (B ⊓ V).subtype).mapQ (A.comap B.subtype) ι (fun x hx => hx.1)
  have hq : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker] at hy
      have hy' : (Submodule.Quotient.mk (ι x) : B ⧸ A.comap B.subtype) = 0 := hy
      rw [Submodule.Quotient.mk_eq_zero] at hy'
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact ⟨hy', x.2.2⟩
  exact Module.length_le_of_injective q hq
theorem length_quot_pow_smul {X : Type*} [AddCommGroup X] [Module R X] {ϖ : R} (hϖ : Irreducible ϖ)
    (τ : ℕ) (L : Submodule R X) [Module.Free R L] [Module.Finite R L] :
    Module.length R (L ⧸ (ϖ ^ τ • L).comap L.subtype) = ((Module.finrank R L * τ : ℕ) : ℕ∞) := by
  let c := Module.finBasis R L
  have hD : (ϖ ^ τ • L).comap L.subtype = diagSub c ϖ (fun _ => τ) := by
    ext y
    rw [mem_diagSub, Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : y = ϖ ^ τ • (⟨z, hz⟩ : L) := Subtype.ext (by simp [hzy])
      intro i
      rw [this, map_smul]
      exact ⟨c.repr ⟨z, hz⟩ i, by simp [smul_eq_mul]⟩
    · intro h
      choose r hr using h
      refine ⟨((c.equivFun.symm r : L) : X), (c.equivFun.symm r).2, ?_⟩
      have : ϖ ^ τ • c.equivFun.symm r = y := by
        apply c.equivFun.injective
        rw [map_smul, LinearEquiv.apply_symm_apply]
        ext i
        simp [Basis.equivFun_apply, hr i, smul_eq_mul]
      rw [← this]
      rfl
  rw [hD, length_quot_diagSub c hϖ]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]
end generic
section main
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
variable {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
variable {W : Type} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
theorem algebraMap_pow_ne_zero (hϖ : Irreducible ϖ) (τ : ℕ) : algebraMap R K (ϖ ^ τ) ≠ 0 := by
  intro h
  have : ϖ ^ τ = 0 := IsFractionRing.injective R K (by rw [h, map_zero])
  exact pow_ne_zero τ hϖ.ne_zero this
include K in
theorem pow_smul_eq_zero (hϖ : Irreducible ϖ) (τ : ℕ) (x : W) (h : ϖ ^ τ • x = 0) : x = 0 := by
  rw [← algebraMap_smul K (ϖ ^ τ) x] at h
  exact (smul_eq_zero.1 h).resolve_left (algebraMap_pow_ne_zero hϖ τ)
theorem claim2 (hϖ : Irreducible ϖ) (τ : ℕ) (M : Submodule R W) (V : Submodule K W) :
    (ϖ ^ τ • M) ⊓ V.restrictScalars R = ϖ ^ τ • latV M V := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists, Submodule.restrictScalars_mem,
    latV]
  constructor
  · rintro ⟨⟨m, hm, rfl⟩, hv⟩
    refine ⟨m, ⟨hm, ?_⟩, rfl⟩
    have hu := algebraMap_pow_ne_zero (K := K) hϖ τ
    have : m = (algebraMap R K (ϖ ^ τ))⁻¹ • (ϖ ^ τ • m) := by
      rw [← algebraMap_smul K (ϖ ^ τ) m, smul_smul, inv_mul_cancel₀ hu, one_smul]
    rw [this]
    exact V.smul_mem _ hv
  · rintro ⟨m, ⟨hm, hv⟩, rfl⟩
    exact ⟨⟨m, hm, rfl⟩, Submodule.smul_of_tower_mem V (ϖ ^ τ) hv⟩
theorem span_eq_map_diagSub {d : ℕ} (M : Submodule R W) (b : Basis (Fin d) R M) (e : Fin d → ℕ) :
    Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W)) = (diagSub b ϖ e).map M.subtype := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨ϖ ^ e i • b i, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_diagSub]
    intro j
    rw [map_smul, Basis.repr_self]
    by_cases hji : j = i
    · subst hji; simp
    · simp [Ne.symm hji]
  · rintro _ ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, mem_diagSub] at hm
    choose r hr using hm
    have hm' : (m : W) = ∑ i, r i • (ϖ ^ e i • (b i : W)) := by
      conv_lhs => rw [← b.sum_repr m]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, hr i, mul_comm, mul_smul]
    change (m : W) ∈ _
    rw [hm']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
theorem pow_dvd_shift (hϖ : Irreducible ϖ) (a τ : ℕ) (c : R) :
    ϖ ^ a ∣ ϖ ^ τ * c ↔ ϖ ^ (a - τ) ∣ c := by
  by_cases h : a ≤ τ
  · rw [Nat.sub_eq_zero_of_le h, pow_zero]
    exact ⟨fun _ => one_dvd c, fun _ => dvd_mul_of_dvd_left (pow_dvd_pow ϖ h) c⟩
  · have ha : a = τ + (a - τ) := by omega
    conv_lhs => rw [ha, pow_add]
    exact mul_dvd_mul_iff_left (pow_ne_zero τ hϖ.ne_zero)
include K in
theorem length_top_part (hϖ : Irreducible ϖ) {d : ℕ} (M : Submodule R W) (b : Basis (Fin d) R M)
    (e : Fin d → ℕ) (N : Submodule R W)
    (hN : N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W))) (τ : ℕ) :
    Module.length R ((ϖ ^ τ • M : Submodule R W) ⧸
        (N ⊓ ϖ ^ τ • M).comap (ϖ ^ τ • M : Submodule R W).subtype) = ((∑ i, (e i - τ) : ℕ) : ℕ∞) := by
  set P : Submodule R W := ϖ ^ τ • M with hPdef
  let g : M →ₗ[R] W := (ϖ ^ τ) • M.subtype
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : ((x : W)) = 0 := pow_smul_eq_zero (K := K) hϖ τ (x : W) hx
    exact Subtype.ext this
  have hrange : LinearMap.range g = P := by
    ext x
    rw [LinearMap.mem_range, hPdef, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, y.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
  let f : M ≃ₗ[R] P := (LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)
  have hf : ∀ m : M, ((f m : P) : W) = ϖ ^ τ • (m : W) := fun m => rfl
  have hNmem : ∀ m : M, ϖ ^ τ • (m : W) ∈ N ↔ ϖ ^ τ • m ∈ diagSub b ϖ e := by
    intro m
    rw [hN, span_eq_map_diagSub, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = ϖ ^ τ • m := Subtype.ext (by simpa using hyx)
      rwa [← this]
    · intro h
      exact ⟨_, h, by simp⟩
  have hD : diagSub b ϖ (fun i => e i - τ) =
      ((N ⊓ P).comap P.subtype).comap (f : M →ₗ[R] P) := by
    ext m
    rw [mem_diagSub, Submodule.mem_comap, Submodule.mem_comap]
    change _ ↔ ((f m : P) : W) ∈ N ⊓ P
    rw [hf, Submodule.mem_inf]
    have hP : ϖ ^ τ • (m : W) ∈ P := Submodule.smul_mem_pointwise_smul _ _ _ m.2
    rw [hNmem, mem_diagSub]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, pow_dvd_shift hϖ]
    exact ⟨fun h => ⟨h, hP⟩, fun h => h.1⟩
  have hmap : (diagSub b ϖ (fun i => e i - τ)).map (f : M →ₗ[R] P) = (N ⊓ P).comap P.subtype := by
    rw [hD]
    exact Submodule.map_comap_eq_of_surjective (f := (f : M →ₗ[R] P)) f.surjective _
  rw [← (Submodule.Quotient.equiv _ _ f hmap).length_eq, length_quot_diagSub b hϖ]
end main
section final
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
variable {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
variable {W : Type} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
theorem claim1 (hϖ : Irreducible ϖ) (τ : ℕ) (M N : Submodule R W) (V : Submodule K W) :
    cutN ϖ τ M N V ≤ ϖ ^ τ • latV M V := by
  intro x hx
  rw [← claim2 hϖ τ M V]
  exact ⟨hx.1.2, hx.2⟩
theorem smul_latV_le (τ : ℕ) (M : Submodule R W) (V : Submodule K W) :
    ϖ ^ τ • latV M V ≤ latV M V := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  exact (latV M V).smul_mem _ hy
theorem latV_free {d : ℕ} (M : Submodule R W) (b : Basis (Fin d) R M) (V : Submodule K W) :
    Module.Free R (latV M V) ∧ Module.Finite R (latV M V) := by
  have : Module.Free R M := Module.Free.of_basis b
  have : Module.Finite R M := Module.Finite.of_basis b
  let Kc : Submodule R M := (latV M V).comap M.subtype
  let eK : Kc ≃ₗ[R] (latV M V) := Submodule.comapSubtypeEquivOfLe inf_le_left
  have : Module.Finite R Kc := inferInstance
  have : Module.IsTorsionFree R Kc := inferInstance
  have : Module.Free R Kc := inferInstance
  exact ⟨Module.Free.of_equiv eK, Module.Finite.equiv eK⟩
theorem cut_top_bound (hϖ : Irreducible ϖ) {d : ℕ} (M : Submodule R W) (b : Basis (Fin d) R M)
    (e : Fin d → ℕ) (N : Submodule R W)
    (hN : N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W))) (τ : ℕ) (V : Submodule K W) :
    Module.length R ((ϖ ^ τ • latV M V : Submodule R W) ⧸
        (cutN ϖ τ M N V).comap (ϖ ^ τ • latV M V : Submodule R W).subtype) ≤ ((∑ i, (e i - τ) : ℕ) : ℕ∞) := by
  have h := length_inf_le (N ⊓ ϖ ^ τ • M) (ϖ ^ τ • M) (V.restrictScalars R)
  rw [claim2 hϖ τ M V, length_top_part (K := K) hϖ M b e N hN τ] at h
  exact h
theorem cut_bottom_eq (hϖ : Irreducible ϖ) {d : ℕ} (M : Submodule R W) (b : Basis (Fin d) R M) (τ : ℕ)
    (V : Submodule K W) :
    Module.length R (latV M V ⧸ (ϖ ^ τ • latV M V).comap (latV M V).subtype) =
      ((Module.finrank R (latV M V) * τ : ℕ) : ℕ∞) := by
  obtain ⟨h1, h2⟩ := latV_free M b V
  exact length_quot_pow_smul hϖ τ (latV M V)
end final
theorem claimC_lattice_intersection : LemmaC := by
  intro R _ _ _ ϖ hϖ K _ _ _ W _ _ _ _ _ d M b _ e N hN τ V
  refine ⟨claim1 hϖ τ M N V, claim2 hϖ τ M V, ?_⟩
  rw [length_tower _ _ _ (claim1 hϖ τ M N V) (smul_latV_le τ M V), cut_bottom_eq hϖ M b τ V]
  push_cast
  rw [add_comm]
  exact add_le_add_right (by exact_mod_cast cut_top_bound hϖ M b e N hN τ V) _
section examples
variable (p : ℕ) [Fact p.Prime]
def stdLat : Submodule ℤ_[p] (Fin 2 → ℚ_[p]) :=
  Submodule.span ℤ_[p] (Set.range (Pi.basisFun ℚ_[p] (Fin 2)))
def stdBasis : Basis (Fin 2) ℤ_[p] (stdLat p) :=
  Basis.span (LinearIndependent.restrict_scalars' (K := ℚ_[p]) ℤ_[p] (Pi.basisFun ℚ_[p] (Fin 2)).linearIndependent)
theorem stdLat_span : Submodule.span ℚ_[p] (stdLat p : Set (Fin 2 → ℚ_[p])) = ⊤ := by
  rw [stdLat, Submodule.span_span_of_tower, Basis.span_eq]
example : Module.length ℤ_[p]
    (latV (stdLat p) (⊤ : Submodule ℚ_[p] (Fin 2 → ℚ_[p])) ⧸
      (cutN (p : ℤ_[p]) 2 (stdLat p)
        (Submodule.span ℤ_[p] (Set.range fun i => (p : ℤ_[p]) ^ (![1, 3] : Fin 2 → ℕ) i • (stdBasis p i : Fin 2 → ℚ_[p])))
        (⊤ : Submodule ℚ_[p] (Fin 2 → ℚ_[p]))).comap
        (latV (stdLat p) (⊤ : Submodule ℚ_[p] (Fin 2 → ℚ_[p]))).subtype) ≤
    ((Module.finrank ℤ_[p] (latV (stdLat p) (⊤ : Submodule ℚ_[p] (Fin 2 → ℚ_[p]))) * 2 +
      ∑ i, ((![1, 3] : Fin 2 → ℕ) i - 2) : ℕ) : ℕ∞) :=
  (claimC_lattice_intersection ℤ_[p] (p : ℤ_[p]) PadicInt.irreducible_p ℚ_[p] (Fin 2 → ℚ_[p]) 2 (stdLat p) (stdBasis p)
    (stdLat_span p) ![1, 3] _ rfl 2 ⊤).2.2
example : ∑ i, ((![1, 3] : Fin 2 → ℕ) i - 2) = 1 := by decide
end examples
end
end Formalism.LFunctionChainParameters.DiagonalSublatticeLength


