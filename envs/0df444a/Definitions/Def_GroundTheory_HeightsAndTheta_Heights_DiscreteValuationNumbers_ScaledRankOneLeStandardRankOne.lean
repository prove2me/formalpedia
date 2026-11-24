-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:02.246086+00:00
-- url     : https://prove2.me/theorems/3101b27c-a9b5-4047-a851-a1b03c7268b9
-- title:
--   Scaled Rank One Le Standard Rank One
-- statement:
--   Definitions and structural lemmas for Scaled Rank One Le Standard Rank One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ScaledRankOneLeStandardRankOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
section FrameBundle
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {σ : Type*}
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
def frameLat (y : σ → Ω) (b : Module.Basis (Fin N) Ω E) (i : σ) : AddSubgroup E where
  carrier := {e | ∀ q, b.repr e q ∈ chartRing o y i}
  add_mem' := by
    intro e e' he he' q
    simpa using add_mem (he q) (he' q)
  zero_mem' := by
    intro q
    simp
  neg_mem' := by
    intro e he q
    simpa using neg_mem (he q)
variable {o}
theorem mem_frameLat {y : σ → Ω} {b : Module.Basis (Fin N) Ω E} {i : σ} {e : E} :
    e ∈ frameLat o y b i ↔ ∀ q, b.repr e q ∈ chartRing o y i :=
  Iff.rfl
theorem repr_sum_smul (b : Module.Basis (Fin N) Ω E) (a : Fin N → Ω) (q : Fin N) :
    b.repr (∑ j, a j • b j) q = a q := by
  have h := congrFun (b.equivFun.apply_symm_apply a) q
  rwa [b.equivFun_apply, b.equivFun_symm_apply] at h
theorem frameLat_iff (y : σ → Ω) (b : Module.Basis (Fin N) Ω E) (i : σ) (e : E) :
    e ∈ frameLat o y b i ↔ ∃ a : Fin N → Ω, (∀ q, a q ∈ chartRing o y i) ∧ e = ∑ q, a q • b q := by
  constructor
  · intro he
    exact ⟨fun q => b.repr e q, he, (b.sum_repr e).symm⟩
  · rintro ⟨a, ha, rfl⟩ q
    rw [repr_sum_smul]
    exact ha q
variable (o)
def frameBundle (y : σ → Ω) (b : Module.Basis (Fin N) Ω E) : ChartBundle o y N E where
  lat := frameLat o y b
  stable i a ha e he q := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ha (he q)
  frame i _ := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨b, b.linearIndependent, b.span_eq, fun e => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    exact frameLat_iff y b i e
  overlap i j hi hj e he := by
    choose m hm using fun q => exists_pow_mul_mem_chartRing y i j hi (he q)
    refine ⟨∑ q, m q, fun q => ?_⟩
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hle : m q ≤ ∑ q, m q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact mul_mem (pow_mem (div_mem_chartRing y j i) _) (hm q)
end FrameBundle
section GradedFrame
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
theorem isGradedFrame_frameBundle (x : (Σ k, ι k) → Ω) (b : Module.Basis (Fin N) Ω E)
    (Vs : Fin (N + 1) → Submodule Ω E) :
    IsGradedFrame o x (frameBundle o (mseg x) b) Vs 0 b := by
  intro s _
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
  refine ⟨b, b.linearIndependent, b.span_eq, fun e => ?_, fun i => ⟨1, ⟨one_ne_zero, ⟨0, ?_⟩, ⟨0, ?_⟩⟩, ?_⟩⟩
  · simp only [one_pow, one_smul, one_mul, exists_const]
    exact frameLat_iff (mseg x) b s e
  · simp
  · simp
  · simp [chartMon]
end GradedFrame
section Point
variable {R : Type*} [CommRing R] [IsDomain R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
theorem mseg_of_one {y : (Σ k, ι k) → Ω} (hy : ∀ p, y p = 1) (s : ∀ k, ι k) : mseg y s = 1 := by
  simp [mseg, hy]
theorem mem_chartRing_of_one {y : (Σ k, ι k) → Ω} (hy : ∀ p, y p = 1) (s : ∀ k, ι k) {a : Ω} :
    a ∈ chartRing R (mseg y) s ↔ ∃ c : R, algebraMap R Ω c = a := by
  constructor
  · intro ha
    have hle : chartRing R (mseg y) s ≤ ⊥ := by
      unfold chartRing
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨t, rfl⟩
      simp only [mseg_of_one hy, div_one]
      exact one_mem _
    exact Algebra.mem_bot.mp (hle ha)
  · rintro ⟨c, rfl⟩
    exact Subalgebra.algebraMap_mem _ c
theorem fst_injective_of_subsingleton (hsub : ∀ k, Subsingleton (ι k)) :
    Function.Injective (Sigma.fst : (Σ k, ι k) → K) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  simp only at h
  subst h
  rw [Subsingleton.elim i j]
theorem mcIdeal_of_one (hinj : Function.Injective (algebraMap R Ω)) (hsub : ∀ k, Subsingleton (ι k))
    {y : (Σ k, ι k) → Ω} (hy : ∀ p, y p = 1) : mcIdeal R y = ⊥ := by
  have key : mcMap R y = (MvPolynomial.mapAlgHom (Algebra.ofId R Ω)).comp
      (MvPolynomial.rename (Sigma.fst : (Σ k, ι k) → K)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mcMap, hy]
  have hi : Function.Injective (mcMap R y) := by
    rw [key]
    exact (MvPolynomial.map_injective _ hinj).comp
      (MvPolynomial.rename_injective _ (fst_injective_of_subsingleton hsub))
  exact (RingHom.injective_iff_ker_eq_bot _).mp hi
theorem isMultiProjPrime_bot (hne : ∀ k, Nonempty (ι k)) :
    IsMultiProjPrime (⊥ : Ideal (MRingOver R ι)) := by
  refine ⟨Ideal.isPrime_bot, ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun k => ⟨(hne k).some, ?_⟩⟩
  rw [Ideal.mem_bot]
  exact MvPolynomial.X_ne_zero _
theorem krull_bot [IsNoetherianRing R] :
    ringKrullDim (MRingOver R ι ⧸ (⊥ : Ideal (MRingOver R ι))) =
      ringKrullDim R + Nat.card (Σ k, ι k) := by
  rw [RingEquiv.ringKrullDim (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
theorem card_sigma_of_point (hsub : ∀ k, Subsingleton (ι k)) (hne : ∀ k, Nonempty (ι k)) :
    Nat.card (Σ k, ι k) = Fintype.card K := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have h1 : ∀ k, Fintype.card (ι k) = 1 := fun k =>
    Fintype.card_eq_one_iff.mpr ⟨(hne k).some, fun _ => @Subsingleton.elim _ (hsub k) _ _⟩
  simp [h1]
end Point
section ModelInhabitants
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
theorem isModelOver_bot [Nonempty K] (hne : ∀ k, Nonempty (ι k)) (d : ℕ)
    (hd : Nat.card (Σ k, ι k) = d + Fintype.card K) :
    IsModelOver O (⊥ : Ideal (MRingOver O ι)) d := by
  refine ⟨inferInstance, isMultiProjPrime_bot hne, Ideal.comap_bot_of_injective _ (C_injective _ _), ?_⟩
  rw [krull_bot, IsDiscreteValuationRing.ringKrullDim_eq_one, hd,
    show d + 1 + Fintype.card K = 1 + (d + Fintype.card K) by omega]
  push_cast
  rfl
theorem isMultiHomog_C (c : O) : IsMultiHomog (C c : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm
theorem isVertDiv_const (c : O) (hc : c ≠ 0) :
    IsVertDiv O (⊥ : Ideal (MRingOver O ι)) 0 (C c) 1 := by
  refine ⟨⟨0, 0, isMultiHomog_C O c, by simpa using isMultiHomog_C O (1 : O), by simp⟩, ?_, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact fun h => hc ((C_injective _ _) (h.trans C_0.symm))
  · rw [Ideal.mem_bot]
    exact one_ne_zero
  · intro Q hQ _ hcom
    refine ⟨1, C c, ⟨0, by simpa using isMultiHomog_C O (1 : O)⟩, ⟨0, isMultiHomog_C O c⟩, ?_, ?_, ?_⟩
    · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
    · intro h
      have : c ∈ Q.comap (C : O →+* MRingOver O ι) := h
      rw [hcom, Ideal.mem_bot] at this
      exact hc this
    · simp
def unif : O :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible O)
theorem unif_ne_zero : unif O ≠ 0 :=
  (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible O)).ne_zero
end ModelInhabitants
section Flags
variable {Ω : Type*} [Field Ω]
def flag2 : Fin 3 → Submodule Ω (Fin 2 → Ω) := fun i =>
  if (i : ℕ) = 0 then ⊥ else if (i : ℕ) = 1 then Submodule.span Ω {Pi.single 0 1} else ⊤
theorem standardFlagTwo_monotone : Monotone (flag2 (Ω := Ω)) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  fin_cases i <;> simp [flag2]
theorem standardFlagTwo_zero : flag2 (Ω := Ω) 0 = ⊥ := by
  simp [flag2]
theorem standardFlagTwo_one : flag2 (Ω := Ω) 1 = Submodule.span Ω {Pi.single 0 1} := by
  simp [flag2]
theorem standardFlagTwo_two : flag2 (Ω := Ω) 2 = ⊤ := by
  simp [flag2]
theorem finrank_standardFlagTwo : ∀ i : Fin 3, Module.finrank Ω (flag2 (Ω := Ω) i) = (i : ℕ)
  | 0 => by
    rw [standardFlagTwo_zero, finrank_bot]
    rfl
  | 1 => by
    rw [standardFlagTwo_one, finrank_span_singleton (by simp : (Pi.single 0 1 : Fin 2 → Ω) ≠ 0)]
    rfl
  | 2 => by
    rw [standardFlagTwo_two, finrank_top, Module.finrank_fin_fun]
    rfl
theorem standardFlagTwo_last : flag2 (Ω := Ω) (Fin.last 2) = ⊤ := by
  simp [flag2]
def bPi (c : Ω) (hc : c ≠ 0) : Module.Basis (Fin 2) Ω (Fin 2 → Ω) :=
  (Pi.basisFun Ω (Fin 2)).isUnitSMul (w := ![1, c]) (by
    intro i
    fin_cases i
    · simp
    · simpa using hc)
theorem bPi_apply (c : Ω) (hc : c ≠ 0) (i : Fin 2) :
    bPi c hc i = (![1, c] i) • Pi.single i 1 := by
  rw [bPi, Module.Basis.isUnitSMul_apply, Pi.basisFun_apply]
variable (o : Type*) [CommRing o] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def stdFlag (x : (Σ k, ι k) → Ω) :
    FullFlag o x (frameBundle o (mseg x) (Pi.basisFun Ω (Fin 2))) where
  Vs := flag2
  mono := standardFlagTwo_monotone
  dim := finrank_standardFlagTwo
  top := standardFlagTwo_last
  deg := 0
  gen := Pi.basisFun Ω (Fin 2)
  gen_mem := by
    intro i
    fin_cases i <;> simp [flag2, Submodule.mem_span_singleton_self]
  frame := isGradedFrame_frameBundle o x _ flag2
end Flags
section FlagPairs
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
abbrev stdE (x : (Σ k, ι k) → Ω) : ChartBundle O (mseg x) 2 (Fin 2 → Ω) :=
  frameBundle O (mseg x) (Pi.basisFun Ω (Fin 2))
abbrev cE (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    ChartBundle O (mseg x) 2 (Fin 2 → Ω) :=
  frameBundle O (mseg x) (bPi (algebraMap O Ω c) hc)
def stdFlagPair (x : (Σ k, ι k) → Ω) (c : O) (hc0 : c ≠ 0) (hc : algebraMap O Ω c ≠ 0)
    (hx : mcIdeal O x = ⊥) : FlagPair O x (stdE O x) (cE O x c hc) where
  toFullFlag := stdFlag O x
  deg' := 0
  gen' := bPi (algebraMap O Ω c) hc
  gen'_mem := by
    intro i
    fin_cases i <;> simp [stdFlag, flag2, bPi_apply, Submodule.mem_span_singleton_self]
  frame' := isGradedFrame_frameBundle O x _ flag2
  f := ![1, C c]
  g := fun _ => 1
  rel := by
    intro i
    fin_cases i <;> simp [stdFlag, flag2, bPi_apply]
  vert := by
    intro i
    rw [hx]
    fin_cases i
    · simpa [stdFlag] using isVertDiv_const O (1 : O) one_ne_zero
    · simpa [stdFlag] using isVertDiv_const O c hc0
end FlagPairs
section PointModel
abbrev ptIdx : Unit → Type := fun _ => Fin 1
abbrev noIdx : Empty → Type := fun e => e.elim
instance instFintypeNoIdx : ∀ k : Empty, Fintype (noIdx k) := fun k => k.elim
variable {Ω : Type*} [Field Ω]
def ptCoord : (Σ k : Unit, ptIdx k) → Ω := fun _ => 1
def noCoord : (Σ k : Empty, noIdx k) → Ω := fun p => p.1.elim
theorem ptCoord_eq (p : Σ k : Unit, ptIdx k) : ptCoord (Ω := Ω) p = 1 :=
  rfl
theorem join_pt_eq (p : Σ k : Unit ⊕ Empty, Sum.elim ptIdx noIdx k) :
    joinCoord (ptCoord (Ω := Ω)) (noCoord (Ω := Ω)) p = 1 := by
  rcases p with ⟨k | k, i⟩
  · rfl
  · exact k.elim
theorem join_sub : ∀ k, Subsingleton (Sum.elim ptIdx noIdx k)
  | .inl _ => inferInstanceAs (Subsingleton (Fin 1))
  | .inr k => k.elim
theorem join_ne : ∀ k, Nonempty (Sum.elim ptIdx noIdx k)
  | .inl _ => ⟨(0 : Fin 1)⟩
  | .inr k => k.elim
theorem ratios_of_one {K₀ : Type} {κ : K₀ → Type} {y : (Σ k, κ k) → Ω} (hy : ∀ p, y p = 1)
    (hne : Nonempty (Σ k, κ k × κ k)) :
    Set.range (fun q : (Σ k, κ k × κ k) => y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) = {1} := by
  ext a
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    simp [hy]
  · rintro rfl
    exact ⟨hne.some, by simp [hy]⟩
end PointModel
section PointDVR
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
theorem frac_inj : Function.Injective (algebraMap O (FractionRing O)) :=
  IsFractionRing.injective O (FractionRing O)
theorem unif_frac_ne : algebraMap O (FractionRing O) (unif O) ≠ 0 :=
  (map_ne_zero_iff _ (frac_inj O)).mpr (unif_ne_zero O)
theorem fnField_of_one {Ω : Type*} [Field Ω] [Algebra O Ω] {K₀ : Type} {κ : K₀ → Type}
    {y : (Σ k, κ k) → Ω} (hy : ∀ p, y p = 1) (hne : Nonempty (Σ k, κ k × κ k)) :
    fnField O y = Subfield.closure (Set.range (algebraMap O Ω) ∪ {1}) := by
  unfold fnField
  rw [ratios_of_one hy hne]
theorem join_model :
    IsModelOver O (mcIdeal O (joinCoord (ptCoord (Ω := FractionRing O)) noCoord)) 0 := by
  rw [mcIdeal_of_one (frac_inj O) join_sub join_pt_eq]
  exact isModelOver_bot O join_ne 0 (by rw [card_sigma_of_point join_sub join_ne]; simp)
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
theorem isPull_frame_of_one {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω} (hx : ∀ p, x p = 1)
    (hxz : ∀ p, joinCoord x z p = 1) {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (b : Module.Basis (Fin N) Ω E) :
    IsPull O x z (frameBundle O (mseg x) b) (frameBundle O (mseg (joinCoord x z)) b) := by
  intro s _
  have tr : ∀ a : Ω, a ∈ chartRing O (mseg (joinCoord x z)) s ↔
      a ∈ chartRing O (mseg x) (restrictChart s) := fun a => by
    rw [mem_chartRing_of_one hxz, mem_chartRing_of_one hx]
  apply le_antisymm
  · intro v hv
    apply AddSubgroup.subset_closure
    exact ⟨1, one_mem _, v, mem_frameLat.mpr fun q => (tr _).mp (mem_frameLat.mp hv q),
      (one_smul _ _).symm⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    refine mem_frameLat.mpr fun q => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ha ((tr _).mpr (mem_frameLat.mp he q))
def ptFlagModel : FlagModel O (ptCoord (Ω := FractionRing O)) 0 2 (stdE O ptCoord)
    (cE O ptCoord (unif O) (unif_frac_ne O)) where
  K' := Empty
  ι' := noIdx
  z := noCoord
  model := join_model O
  birat := by
    rw [fnField_of_one O join_pt_eq ⟨⟨.inl (), ((0 : Fin 1), (0 : Fin 1))⟩⟩,
      fnField_of_one O ptCoord_eq ⟨⟨(), ((0 : Fin 1), (0 : Fin 1))⟩⟩]
  EB := stdE O (joinCoord ptCoord noCoord)
  E'B := cE O (joinCoord ptCoord noCoord) (unif O) (unif_frac_ne O)
  pull := isPull_frame_of_one O ptCoord_eq join_pt_eq _
  pull' := isPull_frame_of_one O ptCoord_eq join_pt_eq _
  flag := stdFlagPair O _ (unif O) (unif_ne_zero O) (unif_frac_ne O)
    (mcIdeal_of_one (frac_inj O) join_sub join_pt_eq)
end PointDVR
section FieldInhabitants
variable (F : Type*) [Field F]
variable {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end FieldInhabitants
section SubQuot
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def bSc1 (c : Ω) (hc : c ≠ 0) : Module.Basis (Fin 1) Ω (Fin 1 → Ω) :=
  (Pi.basisFun Ω (Fin 1)).isUnitSMul (w := fun _ => c) (fun _ => IsUnit.mk0 c hc)
def bG (c : Ω) (hc : c ≠ 0) : Module.Basis (Fin 2) Ω (Fin 2 → Ω) :=
  (Pi.basisFun Ω (Fin 2)).isUnitSMul (w := fun _ => c) (fun _ => IsUnit.mk0 c hc)
abbrev std1 (x : (Σ k, ι k) → Ω) : ChartBundle O (mseg x) 1 (Fin 1 → Ω) :=
  frameBundle O (mseg x) (Pi.basisFun Ω (Fin 1))
abbrev sc1 (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    ChartBundle O (mseg x) 1 (Fin 1 → Ω) :=
  frameBundle O (mseg x) (bSc1 (algebraMap O Ω c) hc)
abbrev gE (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    ChartBundle O (mseg x) 2 (Fin 2 → Ω) :=
  frameBundle O (mseg x) (bG (algebraMap O Ω c) hc)
def iSub : (Fin 1 → Ω) →ₗ[Ω] (Fin 2 → Ω) where
  toFun v := fun j => if j = 0 then v 0 else 0
  map_add' v w := by
    ext j
    by_cases h : j = 0 <;> simp [h]
  map_smul' c v := by
    ext j
    by_cases h : j = 0 <;> simp [h]
def qSub : (Fin 2 → Ω) →ₗ[Ω] (Fin 1 → Ω) where
  toFun v := fun _ => v 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def shearEquiv (V : Type*) [AddCommGroup V] [Module Ω V] : (V × V) ≃ₗ[Ω] (V × V) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  map_add' p q := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add]
    abel
  map_smul' c p := by
    ext <;> simp [smul_add]
  left_inv p := by
    ext <;> simp
  right_inv p := by
    ext <;> simp
def bGraph (c : Ω) (hc : c ≠ 0) : Module.Basis (Fin (1 + 1)) Ω ((Fin 1 → Ω) × (Fin 1 → Ω)) :=
  (((bSc1 c hc).prod (Pi.basisFun Ω (Fin 1))).map (shearEquiv (Fin 1 → Ω))).reindex finSumFinEquiv
end SubQuot
section PullBC
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end PullBC
section RankOne
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end RankOne
section Gaussian
def gi : GaussianInt := ⟨1, 1⟩
def gI : GaussianInt := ⟨0, 1⟩
theorem gi_norm : Zsqrtd.norm gi = 2 := by
  simp [gi, Zsqrtd.norm]
theorem gi_ne_zero : gi ≠ 0 := by
  intro h
  have := congrArg Zsqrtd.re h
  simp [gi] at this
theorem gi_irreducible : Irreducible gi := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (Zsqrtd.norm_eq_one_iff' (by norm_num) gi).mpr hu
    rw [gi_norm] at this
    norm_num at this
  · have hn := congrArg Zsqrtd.norm hab
    rw [Zsqrtd.norm_mul, gi_norm] at hn
    have ha := Zsqrtd.norm_nonneg (by norm_num) a
    have hb := Zsqrtd.norm_nonneg (by norm_num) b
    rcases le_or_gt (Zsqrtd.norm a) 1 with h | h
    · left
      refine (Zsqrtd.norm_eq_one_iff' (by norm_num) a).mp ?_
      have h0 : Zsqrtd.norm a ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hn
        norm_num at hn
      omega
    · right
      refine (Zsqrtd.norm_eq_one_iff' (by norm_num) b).mp ?_
      have h0 : Zsqrtd.norm b ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hn
        norm_num at hn
      have h1 : Zsqrtd.norm b ≤ 1 := by nlinarith
      omega
theorem gi_prime : Prime gi :=
  gi_irreducible.prime
def gIdeal : Ideal GaussianInt := Ideal.span {gi}
instance gIdeal_isPrime : gIdeal.IsPrime :=
  (Ideal.span_singleton_prime gi_ne_zero).mpr gi_prime
theorem gIdeal_ne_bot : gIdeal ≠ ⊥ := by
  rw [gIdeal, Ne, Ideal.span_singleton_eq_bot]
  exact gi_ne_zero
abbrev GO := Localization.AtPrime gIdeal
instance GO_dvr : IsDiscreteValuationRing GO :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain GaussianInt gIdeal_ne_bot GO
theorem GO_inj : Function.Injective (algebraMap GaussianInt GO) :=
  IsLocalization.injective GO gIdeal.primeCompl_le_nonZeroDivisors
instance GO_charZero : CharZero GO :=
  charZero_of_injective_algebraMap GO_inj
def gG : GO := algebraMap GaussianInt GO gi
def uG : GO := algebraMap GaussianInt GO gI
theorem gG_ne_zero : gG ≠ 0 := by
  rw [gG, Ne, map_eq_zero_iff _ GO_inj]
  exact gi_ne_zero
end Gaussian
section FrobInhabitant
local notation "ΩG" => FractionRing GaussianInt
theorem GO_frac_ne (c : GO) (hc : c ≠ 0) : algebraMap GO ΩG c ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective GO ΩG)).mpr hc
def frobSq : (∀ k : Unit, ptIdx k) → (Fin 1 → ΩG) → (Fin 1 → ΩG) :=
  fun _ v => fun _ => v 0 ^ 2
def clR (s : ∀ k : Unit, ptIdx k) (t : ΩG) : chartRing GO (mseg (ptCoord (Ω := ΩG))) s := by
  classical
  exact if h : t ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s then ⟨t, h⟩ else 0
end FrobInhabitant
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles


