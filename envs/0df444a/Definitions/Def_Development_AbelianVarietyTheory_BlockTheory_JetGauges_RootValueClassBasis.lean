-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_RootValueClassBasis
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_RootValueClassBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:01.773375+00:00
-- url     : https://prove2.me/theorems/a5a73e0c-b6ff-46c2-96ac-bd6c96ab0c38
-- title:
--   Root Value Class Basis
-- statement:
--   Definitions and structural lemmas for Root Value Class Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/RootValueClassBasis.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis
noncomputable section
section Defs
variable {E : Type} [Field E] [NumberField E]
def IsRanks [IsCMField E] (r : ℕ) (rk : (E ≃ₐ[ℚ] E) → ℕ) : Prop :=
  ∀ σ : E ≃ₐ[ℚ] E, rk σ + rk ((IsCMField.complexConj E).restrictScalars ℚ * σ) = r
def Psi (rk : (E ≃ₐ[ℚ] E) → ℕ) (γ : E) : E := ∏ σ : E ≃ₐ[ℚ] E, σ γ ^ rk σ
theorem Psi_one (rk : (E ≃ₐ[ℚ] E) → ℕ) : Psi rk (1 : E) = 1 := by
  simp [Psi]
theorem Psi_ne_zero (rk : (E ≃ₐ[ℚ] E) → ℕ) {x : E} (hx : x ≠ 0) : Psi rk x ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun σ _ => pow_ne_zero _ ?_
  exact (map_ne_zero σ).mpr hx
variable (E) in

structure ClassBasis where

  k : ℕ

  c : Fin k → (FractionalIdeal (𝓞 E)⁰ E)ˣ

  γ : Fin k → Eˣ
  span : ∀ x : ClassGroup (𝓞 E), ∃ a : Fin k → ℤ, x = ∏ i, ClassGroup.mk E (c i) ^ a i
  indep : ∀ a : Fin k → ℤ, ∏ i, ClassGroup.mk E (c i) ^ a i = 1 →
    ∀ i, ClassGroup.mk E (c i) ^ a i = 1
  pow_eq : ∀ i, c i ^ orderOf (ClassGroup.mk E (c i)) = toPrincipalIdeal (𝓞 E) E (γ i)
def ClassBasis.h (B : ClassBasis E) (i : Fin B.k) : ℕ := orderOf (ClassGroup.mk E (B.c i))
theorem ClassBasis.h_pos (B : ClassBasis E) (i : Fin B.k) : 0 < B.h i := by
  unfold ClassBasis.h
  exact orderOf_pos _
structure Roots (rk : (E ≃ₐ[ℚ] E) → ℕ) (B : ClassBasis E) (Ω : Type) [Field Ω] [Algebra E Ω] where

  ψ : Fin B.k → Ω
  pow_eq : ∀ i, ψ i ^ B.h i = algebraMap E Ω (Psi rk (B.γ i : E))
variable {rk : (E ≃ₐ[ℚ] E) → ℕ} {B : ClassBasis E} {Ω : Type} [Field Ω] [Algebra E Ω]
theorem Roots.ψ_ne_zero (R : Roots rk B Ω) (i : Fin B.k) : R.ψ i ≠ 0 := by
  intro h0
  have h1 := R.pow_eq i
  rw [h0, zero_pow (B.h_pos i).ne'] at h1
  exact Psi_ne_zero rk (B.γ i).ne_zero ((map_eq_zero (algebraMap E Ω)).mp h1.symm)
def Roots.field (R : Roots rk B Ω) : IntermediateField E Ω :=
  IntermediateField.adjoin E (Set.range R.ψ)
def Roots.IsValue (R : Roots rk B Ω) (𝔫 : (Ideal (𝓞 E))⁰) (b : Ω) : Prop :=
  ∃ (γ : Eˣ) (a : Fin B.k → ℤ),
    FractionalIdeal.mk0 E 𝔫 = toPrincipalIdeal (𝓞 E) E γ * ∏ i, B.c i ^ a i ∧
      b = algebraMap E Ω (Psi rk (γ : E)) * ∏ i, R.ψ i ^ a i
theorem Roots.IsValue.mem {R : Roots rk B Ω} {𝔫 : (Ideal (𝓞 E))⁰} {b : Ω}
    (h : R.IsValue 𝔫 b) : b ∈ R.field := by
  obtain ⟨γ, a, -, rfl⟩ := h
  refine mul_mem (IntermediateField.algebraMap_mem _ _) (prod_mem fun i _ => zpow_mem ?_ _)
  exact IntermediateField.subset_adjoin E _ (Set.mem_range_self i)
theorem Roots.IsValue.ne_zero {R : Roots rk B Ω} {𝔫 : (Ideal (𝓞 E))⁰} {b : Ω}
    (h : R.IsValue 𝔫 b) : b ≠ 0 := by
  obtain ⟨γ, a, -, rfl⟩ := h
  refine mul_ne_zero ((map_ne_zero _).mpr (Psi_ne_zero rk γ.ne_zero)) ?_
  exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (R.ψ_ne_zero i)
theorem Roots.isValue_one (R : Roots rk B Ω) : R.IsValue 1 1 := by
  refine ⟨1, 0, ?_, ?_⟩ <;> simp [Psi_one]
structure BetaChoice (R : Roots rk B Ω) where

  β : (Ideal (𝓞 E))⁰ → R.field
  isValue : ∀ 𝔫, R.IsValue 𝔫 (β 𝔫 : Ω)
  β_one : β 1 = 1
def DegreeBound (R : Roots rk B Ω) : Prop :=
  FiniteDimensional E R.field ∧ Module.finrank E R.field ≤ classNumber E
def AbsValue_sq (r : ℕ) {R : Roots rk B Ω} (C : BetaChoice R) : Prop :=
  ∀ (𝔫 : (Ideal (𝓞 E))⁰) (s : R.field →+* ℂ),
    ‖s (C.β 𝔫)‖ ^ 2 = (Ideal.absNorm (𝔫 : Ideal (𝓞 E)) : ℝ) ^ r
def MulUpToUnit {R : Roots rk B Ω} (C : BetaChoice R) : Prop :=
  ∀ 𝔫₁ 𝔫₂ : (Ideal (𝓞 E))⁰, ∃ u : (𝓞 R.field)ˣ,
    C.β (𝔫₁ * 𝔫₂) = ((u : 𝓞 R.field) : R.field) * (C.β 𝔫₁ * C.β 𝔫₂) ∧
      ∀ s : R.field →+* ℂ, ‖s ((u : 𝓞 R.field) : R.field)‖ = 1
def conjIdeal (R : Roots rk B Ω) {K : Type} [Field K] (s : R.field →+* K) (σ : E ≃ₐ[ℚ] E)
    (𝔫 : Ideal (𝓞 E)) : Ideal (𝓞 K) :=
  𝔫.map (RingOfIntegers.mapRingHom
    (s.comp ((algebraMap E R.field).comp (σ : E →+* E))))
def ValuationAtPlace_vw {R : Roots rk B Ω} (C : BetaChoice R) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (s : R.field →+* K) (w : HeightOneSpectrum (𝓞 K))
    (𝔫 : (Ideal (𝓞 E))⁰),
    FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (s (C.β 𝔫))) =
      ∑ σ : E ≃ₐ[ℚ] E, (rk σ : ℤ) *
        FractionalIdeal.count K w (conjIdeal R s σ (𝔫 : Ideal (𝓞 E)) : FractionalIdeal (𝓞 K)⁰ K)
def ValuationAny {R : Roots rk B Ω} (C : BetaChoice R) : Prop :=
  ∀ (Γ₀ : Type) [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R.field Γ₀)
    (𝔫 : (Ideal (𝓞 E))⁰) (m : (E ≃ₐ[ℚ] E) → Γ₀),
    (∀ σ : E ≃ₐ[ℚ] E, IsGreatest
      {t | ∃ x ∈ (𝔫 : Ideal (𝓞 E)), t = v (algebraMap E R.field (σ (x : E)))} (m σ)) →
    v (C.β 𝔫) = ∏ σ : E ≃ₐ[ℚ] E, m σ ^ rk σ
def ChangeOfChoices (rk : (E ≃ₐ[ℚ] E) → ℕ) (B : ClassBasis E) (Ω : Type) [Field Ω]
    [Algebra E Ω] : Prop :=
  ∀ (R R' : Roots rk B Ω) (𝔫 : (Ideal (𝓞 E))⁰) (b b' : Ω), R.IsValue 𝔫 b → R'.IsValue 𝔫 b' →
    ∃ (u : (𝓞 E)ˣ) (ζ : Ω), IsOfFinOrder ζ ∧
      b' = algebraMap E Ω (Psi rk ((u : 𝓞 E) : E)) * ζ * b ∧ (R.ψ = R'.ψ → ζ = 1)
end Defs
def BetaProperties (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (rk : (E ≃ₐ[ℚ] E) → ℕ), IsRanks r rk →
    ∀ (B : ClassBasis E) (Ω : Type) [Field Ω] [Algebra E Ω],
      ChangeOfChoices rk B Ω ∧
      ∀ R : Roots rk B Ω, DegreeBound R ∧
        ∀ C : BetaChoice R,
          AbsValue_sq r C ∧ MulUpToUnit C ∧ ValuationAtPlace_vw C ∧ ValuationAny C
section Exist
lemma prod_mulSingle_zpow_eq_symm {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [CommGroup G]
    {n : ι → ℕ} (e : G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (b : ι → ℤ) :
    ∏ j, e.symm (Pi.mulSingle j (Multiplicative.ofAdd 1)) ^ b j =
      e.symm (fun j => Multiplicative.ofAdd (b j : ZMod (n j))) := by
  apply e.injective
  rw [map_prod, MulEquiv.apply_symm_apply]
  simp only [map_zpow, MulEquiv.apply_symm_apply, ← Pi.mulSingle_zpow]
  refine (Finset.univ_prod_mulSingle
    (fun j => Multiplicative.ofAdd (1 : ZMod (n j)) ^ b j)).trans (funext fun j => ?_)
  rw [← ofAdd_zsmul]
  simp
theorem exists_basis (G : Type) [CommGroup G] [Finite G] :
    ∃ (k : ℕ) (g : Fin k → G), (∀ x, ∃ a : Fin k → ℤ, x = ∏ i, g i ^ a i) ∧
      ∀ a : Fin k → ℤ, ∏ i, g i ^ a i = 1 → ∀ i, g i ^ a i = 1 := by
  obtain ⟨ι, _, n, -, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  classical
  set q := Fintype.equivFin ι
  have key : ∀ a : Fin (Fintype.card ι) → ℤ,
      ∏ i, e.symm (Pi.mulSingle (q.symm i) (Multiplicative.ofAdd 1)) ^ a i =
        e.symm (fun j => Multiplicative.ofAdd (a (q j) : ZMod (n j))) := by
    intro a
    rw [← prod_mulSingle_zpow_eq_symm e (fun j => a (q j))]
    exact Fintype.prod_equiv q.symm _ _ (fun i => by simp)
  refine ⟨Fintype.card ι, fun i => e.symm (Pi.mulSingle (q.symm i) (Multiplicative.ofAdd 1)),
    ?_, ?_⟩
  · intro x
    choose b hb using fun j => ZMod.intCast_surjective (Multiplicative.toAdd (e x j))
    refine ⟨fun i => b (q.symm i), ?_⟩
    rw [key]
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    funext j
    simp [hb]
  · intro a ha i
    rw [key] at ha
    have h0 : ∀ j, (a (q j) : ZMod (n j)) = 0 := by
      intro j
      have h1 := congrFun (e.symm.injective (ha.trans (map_one e.symm).symm)) j
      simpa using h1
    have h2 := h0 (q.symm i)
    simp only [Equiv.apply_symm_apply] at h2
    rw [← map_zpow, ← Pi.mulSingle_zpow, ← ofAdd_zsmul]
    simp [h2]
variable {E : Type} [Field E] [NumberField E]
theorem exists_gen {I : (FractionalIdeal (𝓞 E)⁰ E)ˣ} (h : ClassGroup.mk E I = 1) :
    ∃ γ : Eˣ, I = toPrincipalIdeal (𝓞 E) E γ := by
  obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.mp h).principal
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply I.ne_zero
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [hx]
    simp
  refine ⟨Units.mk0 x hx0, ?_⟩
  symm
  rw [toPrincipalIdeal_eq_iff]
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [FractionalIdeal.coe_spanSingleton, hx]
  simp
instance : Nonempty (ClassBasis E) := by
  obtain ⟨k, g, hs, hi⟩ := exists_basis (ClassGroup (𝓞 E))
  have hsurj : ∀ x : ClassGroup (𝓞 E), ∃ I, ClassGroup.mk E I = x :=
    ClassGroup.induction E fun I => ⟨I, rfl⟩
  choose c hc using fun i => hsurj (g i)
  choose γ hγ using fun i => exists_gen (I := c i ^ orderOf (ClassGroup.mk E (c i)))
    (by rw [map_pow, pow_orderOf_eq_one])
  exact ⟨⟨k, c, γ, by simpa only [hc] using hs, by simpa only [hc] using hi, hγ⟩⟩
instance (rk : (E ≃ₐ[ℚ] E) → ℕ) (B : ClassBasis E) (Ω : Type) [Field Ω] [Algebra E Ω]
    [IsAlgClosed Ω] : Nonempty (Roots rk B Ω) := by
  choose ψ hψ using fun i =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (Psi rk (B.γ i : E))) (B.h_pos i)
  exact ⟨⟨ψ, hψ⟩⟩
variable {rk : (E ≃ₐ[ℚ] E) → ℕ} {B : ClassBasis E} {Ω : Type} [Field Ω] [Algebra E Ω]
theorem Roots.exists_isValue (R : Roots rk B Ω) (𝔫 : (Ideal (𝓞 E))⁰) : ∃ b, R.IsValue 𝔫 b := by
  obtain ⟨a, ha⟩ := B.span (ClassGroup.mk E (FractionalIdeal.mk0 E 𝔫))
  obtain ⟨γ, hγ⟩ := exists_gen (I := FractionalIdeal.mk0 E 𝔫 * (∏ i, B.c i ^ a i)⁻¹) (by
    rw [map_mul, map_inv, ha, map_prod]
    simp only [map_zpow, mul_inv_cancel])
  exact ⟨_, γ, a, by rw [← hγ, inv_mul_cancel_right], rfl⟩
instance (R : Roots rk B Ω) : Nonempty (BetaChoice R) := by
  classical
  have : ∀ 𝔫, ∃ b, R.IsValue 𝔫 b ∧ (𝔫 = 1 → b = 1) := fun 𝔫 => by
    by_cases h : 𝔫 = 1
    · exact ⟨1, h ▸ R.isValue_one, fun _ => rfl⟩
    · obtain ⟨b, hb⟩ := R.exists_isValue 𝔫
      exact ⟨b, hb, fun h' => (h h').elim⟩
  choose b hb h1 using this
  exact ⟨⟨fun 𝔫 => ⟨b 𝔫, (hb 𝔫).mem⟩, hb, Subtype.ext (h1 1 rfl)⟩⟩
example [IsCMField E] (n : ℕ) : IsRanks (E := E) (2 * n) (fun _ => n) := fun _ => by ring
end Exist
end
end GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis


