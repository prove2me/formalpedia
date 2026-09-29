-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.exists_localizedBaseChange_of_layer_pos_localization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/60ee849e-da9f-58b6-90b5-0ff7046dfe4a

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le
import Theorems.Thm_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_localizedBaseChange_of_layer_pos_localization

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing

namespace NodeLayerRingEd3Sol

section Eval

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem evalAt_add_of_mem (P : Place L F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring)
    (hg : g ∈ P.toValuationSubring) : P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  apply P.algebraMap_residueField_injective
  rw [map_add, P.algebraMap_evalAt hP (add_mem hf hg), P.algebraMap_evalAt hP hf, P.algebraMap_evalAt hP hg,
    ← map_add]
  rfl

theorem evalAt_zero (P : Place L F) : P.evalAt (0 : F) = 0 := by
  rw [P.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : P.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap L P.ResidueField), P.residueInv_algebraMap]

noncomputable def evalHom (A : ValuationSubring L) (P : Place L F) (hP : P.IsRational) (N : Subring F)
    (hN : ∀ f : F, f ∈ N → f ∈ P.toValuationSubring) (hval : ∀ f : F, f ∈ N → P.evalAt f ∈ A) : ↥N →+* ↥A where
  toFun f := ⟨P.evalAt (f : F), hval f f.2⟩
  map_one' := by ext; change P.evalAt 1 = 1; exact P.evalAt_one
  map_mul' f g := by ext; change P.evalAt (f * g) = P.evalAt f * P.evalAt g; exact P.evalAt_mul_of_mem hP (hN _ f.2) (hN _ g.2)
  map_zero' := by ext; change P.evalAt 0 = 0; exact evalAt_zero P
  map_add' f g := by ext; change P.evalAt (f + g) = P.evalAt f + P.evalAt g; exact evalAt_add_of_mem P hP (hN _ f.2) (hN _ g.2)

theorem evalHom_apply (A : ValuationSubring L) (P : Place L F) (hP : P.IsRational) (N : Subring F)
    (hN : ∀ f : F, f ∈ N → f ∈ P.toValuationSubring) (hval : ∀ f : F, f ∈ N → P.evalAt f ∈ A) (f : ↥N) :
    ((evalHom A P hP N hN hval f : ↥A) : L) = P.evalAt (f : F) := rfl

theorem ord_nonneg_of_mem {K F' : Type*} [Field K] [Field F'] [Algebra K F'] (v : Place K F') {f : F'}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨f, hf⟩ : v.toValuationSubring)) (by
      intro h; exact hf0 (congrArg Subtype.val h)) hπ
  have : f = ((u : v.toValuationSubring) : F') * (π : F') ^ (n : ℤ) := by
    have := congrArg Subtype.val hu
    simpa [zpow_natCast] using this
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

end Eval

section Loc

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] (D : Subalgebra R F) (𝔮 : Ideal ↥D)

def locSubring [h𝔮 : 𝔮.IsPrime] : Subring F where
  carrier := {f | ∃ a b : ↥D, b ∉ 𝔮 ∧ f * (b : F) = a}
  mul_mem' := by
    rintro f g ⟨a, b, hb, hf⟩ ⟨a', b', hb', hg⟩
    refine ⟨a * a', b * b', fun h => (h𝔮.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    calc f * g * ((b : F) * b') = (f * b) * (g * b') := by ring
      _ = a * a' := by rw [hf, hg]
  one_mem' := ⟨1, 1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by push_cast; ring⟩
  add_mem' := by
    rintro f g ⟨a, b, hb, hf⟩ ⟨a', b', hb', hg⟩
    refine ⟨a * b' + a' * b, b * b', fun h => (h𝔮.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    calc (f + g) * ((b : F) * b') = (f * b) * b' + (g * b') * b := by ring
      _ = a * b' + a' * b := by rw [hf, hg]
  zero_mem' := ⟨0, 1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by push_cast; ring⟩
  neg_mem' := by
    rintro f ⟨a, b, hb, hf⟩
    refine ⟨-a, b, hb, ?_⟩
    push_cast
    rw [neg_mul, hf]

variable [h𝔮 : 𝔮.IsPrime]

theorem mem_locSubring_iff (f : F) : f ∈ locSubring D 𝔮 ↔ ∃ a b : ↥D, b ∉ 𝔮 ∧ f * (b : F) = a := Iff.rfl

theorem le_locSubring : ∀ d : F, d ∈ D → d ∈ locSubring D 𝔮 :=
  fun d hd => ⟨⟨d, hd⟩, 1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by push_cast; ring⟩

theorem coe_ne_zero_of_notMem {b : ↥D} (hb : b ∉ 𝔮) : (b : F) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := Subtype.ext h
  rw [this]; exact zero_mem _

def toLoc : ↥D →+* ↥(locSubring D 𝔮) where
  toFun d := ⟨d, le_locSubring D 𝔮 d d.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toLoc_apply (d : ↥D) : ((toLoc D 𝔮 d : ↥(locSubring D 𝔮)) : F) = d := rfl

theorem toLoc_injective : Function.Injective (toLoc D 𝔮) := by
  intro a b h
  exact Subtype.ext (congrArg (fun t : ↥(locSubring D 𝔮) => (t : F)) h)

noncomputable scoped instance algebraLoc : Algebra ↥D ↥(locSubring D 𝔮) := (toLoc D 𝔮).toAlgebra

theorem algebraMap_loc_apply (d : ↥D) : ((algebraMap ↥D ↥(locSubring D 𝔮) d : ↥(locSubring D 𝔮)) : F) = d := rfl

scoped instance isLocalization_loc : IsLocalization.AtPrime ↥(locSubring D 𝔮) 𝔮 where
  map_units y := by
    obtain ⟨b, hb⟩ := y
    have hb' : b ∉ 𝔮 := hb
    have hb0 := coe_ne_zero_of_notMem D 𝔮 hb'
    refine isUnit_iff_exists_inv.mpr ⟨⟨(b : F)⁻¹, ⟨1, b, hb', by push_cast; rw [inv_mul_cancel₀ hb0]⟩⟩, ?_⟩
    ext
    change (b : F) * (b : F)⁻¹ = 1
    exact mul_inv_cancel₀ hb0
  surj z := by
    obtain ⟨a, b, hb, hz⟩ := z.2
    refine ⟨⟨a, ⟨b, hb⟩⟩, ?_⟩
    ext
    exact hz
  exists_of_eq {a a'} h := ⟨1, by rw [toLoc_injective D 𝔮 h]⟩

theorem isLocalRing_loc : IsLocalRing ↥(locSubring D 𝔮) := IsLocalization.AtPrime.isLocalRing _ 𝔮

theorem isNoetherianRing_loc [IsNoetherianRing ↥D] : IsNoetherianRing ↥(locSubring D 𝔮) :=
  IsLocalization.isNoetherianRing 𝔮.primeCompl _ inferInstance

theorem eq_mk' (f : ↥(locSubring D 𝔮)) (a b : ↥D) (hb : b ∉ 𝔮) (h : (f : F) * b = a) :
    f = IsLocalization.mk' ↥(locSubring D 𝔮) a (⟨b, hb⟩ : 𝔮.primeCompl) := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  ext
  exact h

theorem isUnit_iff (f : ↥(locSubring D 𝔮)) (a b : ↥D) (hb : b ∉ 𝔮) (h : (f : F) * b = a) :
    IsUnit f ↔ a ∉ 𝔮 := by
  rw [eq_mk' D 𝔮 f a b hb h, IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

end Loc

section LD

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem ld_fintype (C : Subring L) (𝒩₀ : Subring F)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    {ι : Type*} [Fintype ι] (c : ι → L) (a : ι → ↥𝒩₀) (hc : LinearIndependent ↥C c)
    (h : ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0) : ∀ i, a i = 0 := by
  classical
  set e := Fintype.equivFin ι
  have hc' : LinearIndependent ↥C (c ∘ e.symm) := hc.comp _ e.symm.injective
  have h' : ∑ i, (c ∘ e.symm) i • (((a ∘ e.symm) i : ↥𝒩₀) : F) = 0 := by
    rw [← h]
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  intro i
  have := hld _ (c ∘ e.symm) (a ∘ e.symm) hc' h' (e i)
  simpa using this

end LD

end NodeLayerRingEd3Sol
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_localizedBaseChange_of_layer_pos_localization.NodeLayerRingEd3Sol"

open NodeLayerRingEd3Sol in
theorem solution
    {k : Type*} [Field k] [CharZero k]
    {L : Type*} [Field L] [Algebra k L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)

    (S : Set (Place L F)) (hrat : ∀ P ∈ S, P.IsRational) (hSne : S.Nonempty)
    (𝒩 : Subring F)
    (h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring)
    (hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A)

    (K₀ K' : IntermediateField k L) [FiniteDimensional k ↥K₀] [FiniteDimensional k ↥K'] (hK : K₀ ≤ K')
    (C : Subring L) (hCK₀ : ∀ c : L, c ∈ C ↔ c ∈ A ∧ c ∈ K₀) (hC : ∀ c : L, c ∈ C → c ∈ A)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (C' : Subring L) (hC'K' : ∀ c : L, c ∈ C' ↔ c ∈ A ∧ c ∈ K') (hC' : ∀ c : L, c ∈ C' → c ∈ A)
    [IsDomain ↥C'] [IsDiscreteValuationRing ↥C']
    (ϖ' : ↥C')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue A ⟨(d : L), hC' d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')

    (𝒩₀ : Subring F) (h𝒩₀ : 𝒩₀ ≤ 𝒩) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)

    (hres : ∀ g : ↥𝒩₀, ∃ (o : ↥C) (h : algebraMap L F (o : L) ∈ 𝒩₀), ¬ IsUnit (g - ⟨_, h⟩))

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)

    (hreg₁ : ∀ (f : ↥𝒩₀) (h₁ : (f : F) ∈ R₁.integers), 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩) ∧
      (¬ IsUnit f → R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 < x₁.ord (R₁.residue ⟨f, h₁⟩)))
    (hreg₂ : ∀ (f : ↥𝒩₀) (h₂ : (f : F) ∈ R₂.integers), 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩) ∧
      (¬ IsUnit f → R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 < x₂.ord (R₂.residue ⟨f, h₂⟩)))

    (x y : F) (hx : x ∈ 𝒩₀) (hy : y ∈ 𝒩₀)
    (x_fst : ∀ h₁ : x ∈ R₁.integers, R₁.residue ⟨x, h₁⟩ = 0)
    (x_snd : ∀ h₂ : x ∈ R₂.integers, R₂.residue ⟨x, h₂⟩ ≠ 0)
    (y_snd : ∀ h₂ : y ∈ R₂.integers, R₂.residue ⟨y, h₂⟩ = 0)
    (y_fst : ∀ h₁ : y ∈ R₁.integers, R₁.residue ⟨y, h₁⟩ ≠ 0) :
    ∃ (𝒩₀' : Subring F) (_ : IsLocalRing ↥𝒩₀') (_ : IsNoetherianRing ↥𝒩₀') (h01 : 𝒩₀ ≤ 𝒩₀'),
      𝒩₀' ≤ 𝒩 ∧

      (∀ P : Place L F, P ∈ S ↔
        (∀ f : F, f ∈ 𝒩₀' → f ∈ P.toValuationSubring) ∧
        (∀ f : ↥𝒩₀', ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧

      (∀ c : L, c ∈ C' → algebraMap L F c ∈ 𝒩₀') ∧
      (∀ g : ↥𝒩₀', ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ 𝒩₀'), ¬ IsUnit (g - ⟨_, h⟩)) ∧

      (∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀'), LinearIndependent ↥C' c →
        ∑ i, c i • ((a i : ↥𝒩₀') : F) = 0 → ∀ i, a i = 0) ∧

      (∀ f : ↥𝒩₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion h01 f)) ∧
      (∀ hϖ : algebraMap L F (ϖ' : L) ∈ 𝒩₀',
        maximalIdeal ↥𝒩₀' ≤ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h01) ⊔ Ideal.span {⟨_, hϖ⟩}) ∧

      (∀ (f : ↥𝒩₀') (h₁ : (f : F) ∈ R₁.integers), 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩) ∧
        (¬ IsUnit f → R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 < x₁.ord (R₁.residue ⟨f, h₁⟩))) ∧
      (∀ (f : ↥𝒩₀') (h₂ : (f : F) ∈ R₂.integers), 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩) ∧
        (¬ IsUnit f → R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 < x₂.ord (R₂.residue ⟨f, h₂⟩))) ∧

      2 ≤ ringKrullDim ↥𝒩₀' ∧

      (∀ B₀ : Subring F, B₀ ≤ 𝒩₀ →
        (∀ f : F, f ∈ 𝒩₀ ↔ ∃ g h : F, g ∈ B₀ ∧ h ∈ B₀ ∧ (∀ hh : h ∈ 𝒩₀, IsUnit (⟨h, hh⟩ : ↥𝒩₀)) ∧ f * h = g) →
        ∀ f : F, f ∈ 𝒩₀' ↔ ∃ g h : F,
          g ∈ Subring.closure ((B₀ : Set F) ∪ {x : F | ∃ c : L, c ∈ C' ∧ x = algebraMap L F c}) ∧
          h ∈ Subring.closure ((B₀ : Set F) ∪ {x : F | ∃ c : L, c ∈ C' ∧ x = algebraMap L F c}) ∧
          (∀ hh : h ∈ 𝒩₀', IsUnit (⟨h, hh⟩ : ↥𝒩₀')) ∧ f * h = g) := by
  classical

  obtain ⟨P₀, hP₀⟩ := hSne
  have h1N : ∀ f : F, f ∈ 𝒩 → f ∈ R₁.integers := fun f hf => ((h𝒩 f).1 hf).1
  have h2N : ∀ f : F, f ∈ 𝒩 → f ∈ R₂.integers := fun f hf => ((h𝒩 f).1 hf).2.1
  have hPN : ∀ f : F, f ∈ 𝒩 → ∀ P ∈ S, f ∈ P.toValuationSubring := fun f hf => ((h𝒩 f).1 hf).2.2
  have hconstN : ∀ c : L, c ∈ A → algebraMap L F c ∈ 𝒩 := by
    intro c hc
    rw [h𝒩]
    exact ⟨(R₁.algebraMap_mem_iff c).mpr hc, (R₂.algebraMap_mem_iff c).mpr hc, fun P _ => P.algebraMap_mem' c⟩
  have hCC' : ∀ c : L, c ∈ C → c ∈ C' := fun c hc =>
    (hC'K' c).mpr ⟨((hCK₀ c).mp hc).1, hK ((hCK₀ c).mp hc).2⟩

  have hϖ'res : IsLocalRing.residue A ⟨((ϖ' : ↥C') : L), hC' _ ϖ'.2⟩ = 0 := (hϖ' ϖ').mpr ⟨1, by rw [mul_one]⟩
  have hϖ'ne : ((ϖ' : ↥C') : L) ≠ 0 := by
    intro h0

    obtain ⟨d, hd⟩ := IsDiscreteValuationRing.exists_irreducible ↥C'
    have hdnu : ¬ IsUnit d := hd.not_isUnit
    have hd0 : d ≠ 0 := hd.ne_zero
    have hdres : IsLocalRing.residue A ⟨((d : ↥C') : L), hC' _ d.2⟩ = 0 := by
      by_contra hne
      have hu : IsUnit (⟨((d : ↥C') : L), hC' _ d.2⟩ : ↥A) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
      have hwval : (d : L) * (w : L) = 1 := congrArg (fun z : ↥A => (z : L)) hw
      have hd0' : ((d : ↥C') : L) ≠ 0 := fun h => hd0 (Subtype.ext h)
      have hwinv : (w : L) = ((d : ↥C') : L)⁻¹ := (eq_inv_of_mul_eq_one_right hwval)
      have hwC' : (w : L) ∈ C' := by
        rw [hC'K', hwinv]
        exact ⟨hwinv ▸ w.2, inv_mem ((hC'K' _).mp d.2).2⟩
      apply hdnu
      refine isUnit_iff_exists_inv.mpr ⟨⟨(w : L), hwC'⟩, ?_⟩
      ext; exact hwval
    obtain ⟨d', hd'⟩ := (hϖ' d).mp hdres
    apply hd0
    rw [hd']
    ext
    change ((ϖ' : ↥C') : L) * d' = 0
    rw [h0, zero_mul]
  have hϖ'inv : (((ϖ' : ↥C') : L))⁻¹ ∉ C' := by
    intro hinv
    have hu : IsUnit (⟨((ϖ' : ↥C') : L), hC' _ ϖ'.2⟩ : ↥A) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨(((ϖ' : ↥C') : L))⁻¹, hC' _ hinv⟩, ?_⟩
      ext
      change ((ϖ' : ↥C') : L) * ((ϖ' : ↥C') : L)⁻¹ = 1
      exact mul_inv_cancel₀ hϖ'ne
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu hϖ'res

  obtain ⟨G, hGC', hGdiv⟩ :=
    ValuationSubring.exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le A K₀ K' hK C hCK₀ C'
      hC'K' _ ϖ'.2 hϖ'inv
  set Gimg : Set F := (algebraMap L F) '' (G : Set L) with hGimg
  set D : Subalgebra ↥𝒩₀ F := Algebra.adjoin ↥𝒩₀ Gimg with hDdef

  let 𝒩alg : Subalgebra ↥𝒩₀ F := { 𝒩 with algebraMap_mem' := fun r => h𝒩₀ r.2 }
  have hGimgN : Gimg ⊆ (𝒩alg : Set F) := by
    rintro _ ⟨g, hg, rfl⟩
    exact hconstN g (hC' _ (hGC' hg))
  have hDN : ∀ d : F, d ∈ D → d ∈ 𝒩 := by
    intro d hd
    have : D ≤ 𝒩alg := Algebra.adjoin_le hGimgN
    exact this hd
  have h0D : ∀ r : F, r ∈ 𝒩₀ → r ∈ D := fun r hr => Subalgebra.algebraMap_mem D (⟨r, hr⟩ : ↥𝒩₀)
  have hCD : ∀ c : L, c ∈ C → algebraMap L F c ∈ D := fun c hc => h0D _ (hCmem c hc)
  have hGD : ∀ g : L, g ∈ G → algebraMap L F g ∈ D := fun g hg => Algebra.subset_adjoin ⟨g, hg, rfl⟩

  have hspanD : ∀ y : L, y ∈ Submodule.span ↥C (G : Set L) → algebraMap L F y ∈ D := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem g hg => exact hGD g hg
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul]
      exact mul_mem (hCD _ c.2) ha

  haveI : Algebra.FiniteType ↥𝒩₀ ↥D := by
    refine ⟨(Subalgebra.fg_top _).mpr ⟨G.image (algebraMap L F), ?_⟩⟩
    rw [Finset.coe_image]
  haveI hDnoe : IsNoetherianRing ↥D := Algebra.FiniteType.isNoetherianRing ↥𝒩₀ ↥D

  set J : Ideal ↥D := (maximalIdeal ↥𝒩₀).map (algebraMap ↥𝒩₀ ↥D) with hJdef
  have halgD : ∀ r : ↥𝒩₀, ((algebraMap ↥𝒩₀ ↥D r : ↥D) : F) = r := fun r => rfl

  have hQ : ∀ (d : F) (hd : d ∈ D), ∃ c : L, c ∈ C' ∧ ∃ hc : algebraMap L F c ∈ D,
      (⟨d, hd⟩ - ⟨algebraMap L F c, hc⟩ : ↥D) ∈ J := by
    intro d hd
    induction hd using Algebra.adjoin_induction with
    | mem g hg =>
      obtain ⟨g', hg', rfl⟩ := hg
      exact ⟨g', hGC' hg', hGD g' hg', by rw [sub_self]; exact zero_mem _⟩
    | algebraMap r =>
      obtain ⟨o, ho, hnu⟩ := hres r
      refine ⟨(o : L), hCC' _ o.2, hCD _ o.2, ?_⟩
      have hm : r - ⟨algebraMap L F (o : L), ho⟩ ∈ maximalIdeal ↥𝒩₀ := (mem_maximalIdeal _).mpr hnu
      have := Ideal.mem_map_of_mem (algebraMap ↥𝒩₀ ↥D) hm
      rw [map_sub] at this
      convert this using 2 <;> first | rfl | exact Subtype.ext rfl
    | add a b ha hb iha ihb =>
      obtain ⟨c, hcC', hcD, hca⟩ := iha
      obtain ⟨c', hc'C', hc'D, hcb⟩ := ihb
      have hccD : algebraMap L F (c + c') ∈ D := by rw [map_add]; exact add_mem hcD hc'D
      refine ⟨c + c', add_mem hcC' hc'C', hccD, ?_⟩
      have : (⟨a + b, add_mem ha hb⟩ - ⟨algebraMap L F (c + c'), hccD⟩ : ↥D) =
          (⟨a, ha⟩ - ⟨algebraMap L F c, hcD⟩) + (⟨b, hb⟩ - ⟨algebraMap L F c', hc'D⟩) := by
        ext; simp [map_add]; ring
      rw [this]
      exact add_mem hca hcb
    | mul a b ha hb iha ihb =>
      obtain ⟨c, hcC', hcD, hca⟩ := iha
      obtain ⟨c', hc'C', hc'D, hcb⟩ := ihb
      have hccD : algebraMap L F (c * c') ∈ D := by rw [map_mul]; exact mul_mem hcD hc'D
      refine ⟨c * c', mul_mem hcC' hc'C', hccD, ?_⟩
      have : (⟨a * b, mul_mem ha hb⟩ - ⟨algebraMap L F (c * c'), hccD⟩ : ↥D) =
          (⟨a, ha⟩ - ⟨algebraMap L F c, hcD⟩) * ⟨b, hb⟩ +
            ⟨algebraMap L F c, hcD⟩ * (⟨b, hb⟩ - ⟨algebraMap L F c', hc'D⟩) := by
        ext; simp [map_mul]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_right _ _ hca) (Ideal.mul_mem_left _ _ hcb)

  let inclDN : ↥D →+* ↥𝒩 :=
    { toFun := fun d => ⟨d, hDN d d.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hinclDN : ∀ d : ↥D, ((inclDN d : ↥𝒩) : F) = d := fun d => rfl

  let evN : ∀ P : Place L F, P ∈ S → (↥𝒩 →+* ↥A) := fun P hP =>
    evalHom A P (hrat P hP) 𝒩 (fun f hf => hPN f hf P hP) (fun f hf => hval f hf P hP)
  have hevN : ∀ (P : Place L F) (hP : P ∈ S) (f : ↥𝒩), ((evN P hP f : ↥A) : L) = P.evalAt (f : F) :=
    fun P hP f => rfl
  let evD : ∀ P : Place L F, P ∈ S → (↥D →+* ↥A) := fun P hP => (evN P hP).comp inclDN
  have hevD : ∀ (P : Place L F) (hP : P ∈ S) (d : ↥D), ((evD P hP d : ↥A) : L) = P.evalAt (d : F) :=
    fun P hP d => rfl

  have hJev : ∀ (P : Place L F) (hP : P ∈ S), J ≤ (maximalIdeal ↥A).comap (evD P hP) := by
    intro P hP
    rw [hJdef, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap]
    obtain ⟨h, hm⟩ := ((hS P).mp hP).2 r ((mem_maximalIdeal _).mp hr)
    convert hm using 1
    rfl

  have hev_dec : ∀ (P : Place L F) (hP : P ∈ S) (d : ↥D) (c : L) (hcC' : c ∈ C') (hcD : algebraMap L F c ∈ D),
      (d - ⟨algebraMap L F c, hcD⟩ : ↥D) ∈ J →
      IsLocalRing.residue ↥A (evD P hP d) = IsLocalRing.residue ↥A ⟨c, hC' c hcC'⟩ := by
    intro P hP d c hcC' hcD hmem
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have h1 := hJev P hP hmem
    rw [Ideal.mem_comap, map_sub] at h1
    have hc : (evD P hP ⟨algebraMap L F c, hcD⟩ : ↥A) = ⟨c, hC' c hcC'⟩ := by
      ext
      rw [hevD P hP]
      exact P.evalAt_algebraMap_eq c
    rw [hc] at h1
    exact h1

  set 𝔮 : Ideal ↥D := RingHom.ker ((IsLocalRing.residue ↥A).comp (evD P₀ hP₀)) with h𝔮def
  haveI h𝔮prime : 𝔮.IsPrime := RingHom.ker_isPrime _
  have hmem𝔮 : ∀ d : ↥D, d ∈ 𝔮 ↔ IsLocalRing.residue ↥A (evD P₀ hP₀ d) = 0 := fun d => RingHom.mem_ker

  have h𝔮_dec : ∀ (d : ↥D) (c : L) (hcC' : c ∈ C') (hcD : algebraMap L F c ∈ D),
      (d - ⟨algebraMap L F c, hcD⟩ : ↥D) ∈ J →
      (d ∈ 𝔮 ↔ IsLocalRing.residue ↥A ⟨c, hC' c hcC'⟩ = 0) := by
    intro d c hcC' hcD hmem
    rw [hmem𝔮, hev_dec P₀ hP₀ d c hcC' hcD hmem]

  have h𝔮P : ∀ (P : Place L F) (hP : P ∈ S) (d : ↥D), d ∈ 𝔮 ↔ evD P hP d ∈ maximalIdeal ↥A := by
    intro P hP d
    obtain ⟨c, hcC', hcD, hmem⟩ := hQ d d.2
    rw [h𝔮_dec d c hcC' hcD hmem, ← IsLocalRing.residue_eq_zero_iff, hev_dec P hP d c hcC' hcD hmem]
  have hJ𝔮 : J ≤ 𝔮 := by
    intro m hm
    rw [h𝔮P P₀ hP₀]
    exact hJev P₀ hP₀ hm

  let resN₁ : ↥𝒩 →+* Fbar₁ :=
    { toFun := fun f => R₁.residue ⟨(f : F), h1N f f.2⟩
      map_one' := by
        have : (⟨((1 : ↥𝒩) : F), h1N _ (1 : ↥𝒩).2⟩ : R₁.integers) = 1 := rfl
        simp only [this, map_one]
      map_mul' := fun f g => by
        have : (⟨((f * g : ↥𝒩) : F), h1N _ (f * g).2⟩ : R₁.integers) =
            ⟨(f : F), h1N f f.2⟩ * ⟨(g : F), h1N g g.2⟩ := rfl
        simp only [this, map_mul]
      map_zero' := by
        have : (⟨((0 : ↥𝒩) : F), h1N _ (0 : ↥𝒩).2⟩ : R₁.integers) = 0 := rfl
        simp only [this, map_zero]
      map_add' := fun f g => by
        have : (⟨((f + g : ↥𝒩) : F), h1N _ (f + g).2⟩ : R₁.integers) =
            ⟨(f : F), h1N f f.2⟩ + ⟨(g : F), h1N g g.2⟩ := rfl
        simp only [this, map_add] }
  have hresN₁ : ∀ (f : F) (hf : f ∈ 𝒩) (h₁ : f ∈ R₁.integers), R₁.residue ⟨f, h₁⟩ = resN₁ ⟨f, hf⟩ :=
    fun f hf h₁ => rfl
  let resN₂ : ↥𝒩 →+* Fbar₂ :=
    { toFun := fun f => R₂.residue ⟨(f : F), h2N f f.2⟩
      map_one' := by
        have : (⟨((1 : ↥𝒩) : F), h2N _ (1 : ↥𝒩).2⟩ : R₂.integers) = 1 := rfl
        simp only [this, map_one]
      map_mul' := fun f g => by
        have : (⟨((f * g : ↥𝒩) : F), h2N _ (f * g).2⟩ : R₂.integers) =
            ⟨(f : F), h2N f f.2⟩ * ⟨(g : F), h2N g g.2⟩ := rfl
        simp only [this, map_mul]
      map_zero' := by
        have : (⟨((0 : ↥𝒩) : F), h2N _ (0 : ↥𝒩).2⟩ : R₂.integers) = 0 := rfl
        simp only [this, map_zero]
      map_add' := fun f g => by
        have : (⟨((f + g : ↥𝒩) : F), h2N _ (f + g).2⟩ : R₂.integers) =
            ⟨(f : F), h2N f f.2⟩ + ⟨(g : F), h2N g g.2⟩ := rfl
        simp only [this, map_add] }
  have hresN₂ : ∀ (f : F) (hf : f ∈ 𝒩) (h₂ : f ∈ R₂.integers), R₂.residue ⟨f, h₂⟩ = resN₂ ⟨f, hf⟩ :=
    fun f hf h₂ => rfl
  let resD₁ : ↥D →+* Fbar₁ := resN₁.comp inclDN
  let resD₂ : ↥D →+* Fbar₂ := resN₂.comp inclDN
  have hresD₁ : ∀ (d : ↥D) (h₁ : (d : F) ∈ R₁.integers), R₁.residue ⟨d, h₁⟩ = resD₁ d := fun d h₁ => rfl
  have hresD₂ : ∀ (d : ↥D) (h₂ : (d : F) ∈ R₂.integers), R₂.residue ⟨d, h₂⟩ = resD₂ d := fun d h₂ => rfl

  have hres_const₁ : ∀ (c : L) (hc : c ∈ A) (hcD : algebraMap L F c ∈ D),
      resD₁ ⟨algebraMap L F c, hcD⟩ = algebraMap (ResidueField ↥A) Fbar₁ (IsLocalRing.residue ↥A ⟨c, hc⟩) := by
    intro c hc hcD
    rw [← hresD₁ _ ((R₁.algebraMap_mem_iff c).mpr hc)]
    exact R₁.residue_algebraMap ⟨c, hc⟩
  have hres_const₂ : ∀ (c : L) (hc : c ∈ A) (hcD : algebraMap L F c ∈ D),
      resD₂ ⟨algebraMap L F c, hcD⟩ = algebraMap (ResidueField ↥A) Fbar₂ (IsLocalRing.residue ↥A ⟨c, hc⟩) := by
    intro c hc hcD
    rw [← hresD₂ _ ((R₂.algebraMap_mem_iff c).mpr hc)]
    exact R₂.residue_algebraMap ⟨c, hc⟩

  have hDreg₁ : ∀ d : ↥D, resD₁ d ∈ x₁.toValuationSubring := by
    intro d
    obtain ⟨d, hd⟩ := d
    induction hd using Algebra.adjoin_induction with
    | mem g hg =>
      obtain ⟨g', hg', rfl⟩ := hg
      rw [hres_const₁ g' (hC' _ (hGC' hg'))]
      exact x₁.algebraMap_mem' _
    | algebraMap r =>
      have h := (hreg₁ r (h1N _ (h𝒩₀ r.2))).1
      by_cases h0 : R₁.residue ⟨(r : F), h1N _ (h𝒩₀ r.2)⟩ = 0
      · change R₁.residue ⟨(r : F), _⟩ ∈ _
        rw [h0]; exact zero_mem _
      · exact x₁.mem_toValuationSubring_of_ord_nonneg_alt h0 h
    | add a b ha hb iha ihb =>
      have : resD₁ ⟨a + b, add_mem ha hb⟩ = resD₁ ⟨a, ha⟩ + resD₁ ⟨b, hb⟩ := by
        rw [← map_add]; rfl
      rw [this]; exact add_mem iha ihb
    | mul a b ha hb iha ihb =>
      have : resD₁ ⟨a * b, mul_mem ha hb⟩ = resD₁ ⟨a, ha⟩ * resD₁ ⟨b, hb⟩ := by
        rw [← map_mul]; rfl
      rw [this]; exact mul_mem iha ihb
  have hDreg₂ : ∀ d : ↥D, resD₂ d ∈ x₂.toValuationSubring := by
    intro d
    obtain ⟨d, hd⟩ := d
    induction hd using Algebra.adjoin_induction with
    | mem g hg =>
      obtain ⟨g', hg', rfl⟩ := hg
      rw [hres_const₂ g' (hC' _ (hGC' hg'))]
      exact x₂.algebraMap_mem' _
    | algebraMap r =>
      have h := (hreg₂ r (h2N _ (h𝒩₀ r.2))).1
      by_cases h0 : R₂.residue ⟨(r : F), h2N _ (h𝒩₀ r.2)⟩ = 0
      · change R₂.residue ⟨(r : F), _⟩ ∈ _
        rw [h0]; exact zero_mem _
      · exact x₂.mem_toValuationSubring_of_ord_nonneg_alt h0 h
    | add a b ha hb iha ihb =>
      have : resD₂ ⟨a + b, add_mem ha hb⟩ = resD₂ ⟨a, ha⟩ + resD₂ ⟨b, hb⟩ := by
        rw [← map_add]; rfl
      rw [this]; exact add_mem iha ihb
    | mul a b ha hb iha ihb =>
      have : resD₂ ⟨a * b, mul_mem ha hb⟩ = resD₂ ⟨a, ha⟩ * resD₂ ⟨b, hb⟩ := by
        rw [← map_mul]; rfl
      rw [this]; exact mul_mem iha ihb

  let resO₁ : ↥D →+* ↥x₁.toValuationSubring := resD₁.codRestrict _ hDreg₁
  let resO₂ : ↥D →+* ↥x₂.toValuationSubring := resD₂.codRestrict _ hDreg₂
  have hresO₁ : ∀ d : ↥D, ((resO₁ d : ↥x₁.toValuationSubring) : Fbar₁) = resD₁ d := fun d => rfl
  have hresO₂ : ∀ d : ↥D, ((resO₂ d : ↥x₂.toValuationSubring) : Fbar₂) = resD₂ d := fun d => rfl

  have hJres₁ : J ≤ (maximalIdeal ↥x₁.toValuationSubring).comap resO₁ := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hpos := (hreg₁ r (h1N _ (h𝒩₀ r.2))).2 ((mem_maximalIdeal _).mp hr)
    have hval : ((resO₁ (algebraMap ↥𝒩₀ ↥D r) : ↥x₁.toValuationSubring) : Fbar₁) =
        R₁.residue ⟨(r : F), h1N _ (h𝒩₀ r.2)⟩ := rfl
    obtain ⟨w, hw⟩ := hu
    have hord := x₁.ord_coe_unit w
    rw [hw, hval] at hord
    by_cases h0 : R₁.residue ⟨(r : F), h1N _ (h𝒩₀ r.2)⟩ = 0
    · have : (w : ↥x₁.toValuationSubring) = 0 := by ext; rw [hw, hval, h0]; rfl
      exact w.ne_zero this
    · have := hpos h0; omega
  have hJres₂ : J ≤ (maximalIdeal ↥x₂.toValuationSubring).comap resO₂ := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hpos := (hreg₂ r (h2N _ (h𝒩₀ r.2))).2 ((mem_maximalIdeal _).mp hr)
    have hval : ((resO₂ (algebraMap ↥𝒩₀ ↥D r) : ↥x₂.toValuationSubring) : Fbar₂) =
        R₂.residue ⟨(r : F), h2N _ (h𝒩₀ r.2)⟩ := rfl
    obtain ⟨w, hw⟩ := hu
    have hord := x₂.ord_coe_unit w
    rw [hw, hval] at hord
    by_cases h0 : R₂.residue ⟨(r : F), h2N _ (h𝒩₀ r.2)⟩ = 0
    · have : (w : ↥x₂.toValuationSubring) = 0 := by ext; rw [hw, hval, h0]; rfl
      exact w.ne_zero this
    · have := hpos h0; omega

  have hunit_of_notMem₁ : ∀ b : ↥D, b ∉ 𝔮 → IsUnit (resO₁ b) := by
    intro b hb
    obtain ⟨β, hβC', hβD, hmem⟩ := hQ b b.2
    have hβres : IsLocalRing.residue ↥A ⟨β, hC' β hβC'⟩ ≠ 0 := fun h0 => hb ((h𝔮_dec b β hβC' hβD hmem).mpr h0)
    have hdecomp : resO₁ b = resO₁ ⟨algebraMap L F β, hβD⟩ + resO₁ (b - ⟨algebraMap L F β, hβD⟩) := by
      rw [← map_add]; congr 1; ring
    rw [hdecomp]
    have hu : IsUnit (resO₁ ⟨algebraMap L F β, hβD⟩) := by
      have hval : ((resO₁ ⟨algebraMap L F β, hβD⟩ : ↥x₁.toValuationSubring) : Fbar₁) =
          algebraMap (ResidueField ↥A) Fbar₁ (IsLocalRing.residue ↥A ⟨β, hC' β hβC'⟩) := hres_const₁ β _ hβD
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap (ResidueField ↥A) Fbar₁
        (IsLocalRing.residue ↥A ⟨β, hC' β hβC'⟩)⁻¹, x₁.algebraMap_mem' _⟩, ?_⟩
      ext
      change ((resO₁ ⟨algebraMap L F β, hβD⟩ : ↥x₁.toValuationSubring) : Fbar₁) * _ = 1
      rw [hval, ← map_mul, mul_inv_cancel₀ hβres, map_one]
    have hm : resO₁ (b - ⟨algebraMap L F β, hβD⟩) ∈ maximalIdeal ↥x₁.toValuationSubring := hJres₁ hmem
    obtain ⟨g, hg⟩ := hu
    rw [← hg]
    have : (g : ↥x₁.toValuationSubring) + resO₁ (b - ⟨algebraMap L F β, hβD⟩) =
        g * (1 + ↑g⁻¹ * resO₁ (b - ⟨algebraMap L F β, hβD⟩)) := by
      rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]
    refine (Units.isUnit g).mul ?_
    have hj := (maximalIdeal_le_jacobson (⊥ : Ideal ↥x₁.toValuationSubring)) (Ideal.mul_mem_left _ (↑g⁻¹) hm)
    rw [Ideal.mem_jacobson_bot] at hj
    simpa [mul_one, add_comm] using hj 1
  have hunit_of_notMem₂ : ∀ b : ↥D, b ∉ 𝔮 → IsUnit (resO₂ b) := by
    intro b hb
    obtain ⟨β, hβC', hβD, hmem⟩ := hQ b b.2
    have hβres : IsLocalRing.residue ↥A ⟨β, hC' β hβC'⟩ ≠ 0 := fun h0 => hb ((h𝔮_dec b β hβC' hβD hmem).mpr h0)
    have hdecomp : resO₂ b = resO₂ ⟨algebraMap L F β, hβD⟩ + resO₂ (b - ⟨algebraMap L F β, hβD⟩) := by
      rw [← map_add]; congr 1; ring
    rw [hdecomp]
    have hu : IsUnit (resO₂ ⟨algebraMap L F β, hβD⟩) := by
      have hval : ((resO₂ ⟨algebraMap L F β, hβD⟩ : ↥x₂.toValuationSubring) : Fbar₂) =
          algebraMap (ResidueField ↥A) Fbar₂ (IsLocalRing.residue ↥A ⟨β, hC' β hβC'⟩) := hres_const₂ β _ hβD
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap (ResidueField ↥A) Fbar₂
        (IsLocalRing.residue ↥A ⟨β, hC' β hβC'⟩)⁻¹, x₂.algebraMap_mem' _⟩, ?_⟩
      ext
      change ((resO₂ ⟨algebraMap L F β, hβD⟩ : ↥x₂.toValuationSubring) : Fbar₂) * _ = 1
      rw [hval, ← map_mul, mul_inv_cancel₀ hβres, map_one]
    have hm : resO₂ (b - ⟨algebraMap L F β, hβD⟩) ∈ maximalIdeal ↥x₂.toValuationSubring := hJres₂ hmem
    obtain ⟨g, hg⟩ := hu
    rw [← hg]
    have : (g : ↥x₂.toValuationSubring) + resO₂ (b - ⟨algebraMap L F β, hβD⟩) =
        g * (1 + ↑g⁻¹ * resO₂ (b - ⟨algebraMap L F β, hβD⟩)) := by
      rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]
    refine (Units.isUnit g).mul ?_
    have hj := (maximalIdeal_le_jacobson (⊥ : Ideal ↥x₂.toValuationSubring)) (Ideal.mul_mem_left _ (↑g⁻¹) hm)
    rw [Ideal.mem_jacobson_bot] at hj
    simpa [mul_one, add_comm] using hj 1

  have hinvC' : ∀ (β : L) (hβ : β ∈ C'), IsLocalRing.residue ↥A ⟨β, hC' β hβ⟩ ≠ 0 → β⁻¹ ∈ C' := by
    intro β hβ hres0
    have hu : IsUnit (⟨β, hC' β hβ⟩ : ↥A) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres0
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hwval : β * (w : L) = 1 := congrArg (fun z : ↥A => (z : L)) hw
    have hwinv : (w : L) = β⁻¹ := eq_inv_of_mul_eq_one_right hwval
    rw [hC'K', ← hwinv]
    exact ⟨w.2, hwinv ▸ inv_mem ((hC'K' β).mp hβ).2⟩

  set 𝒩₀' : Subring F := locSubring D 𝔮 with h𝒩₀'def
  haveI hloc' : IsLocalRing ↥𝒩₀' := isLocalRing_loc D 𝔮
  haveI hnoe' : IsNoetherianRing ↥𝒩₀' := isNoetherianRing_loc D 𝔮
  have h01 : 𝒩₀ ≤ 𝒩₀' := fun r hr => le_locSubring D 𝔮 r (h0D r hr)
  have hD0' : ∀ d : F, d ∈ D → d ∈ 𝒩₀' := le_locSubring D 𝔮
  have hunit' : ∀ (f : ↥𝒩₀') (a b : ↥D) (hb : b ∉ 𝔮) (h : (f : F) * b = a), IsUnit f ↔ a ∉ 𝔮 :=
    fun f a b hb h => isUnit_iff D 𝔮 f a b hb h

  have hres_ne₁ : ∀ b : ↥D, b ∉ 𝔮 → resD₁ b ≠ 0 := by
    intro b hb h0
    obtain ⟨w, hw⟩ := hunit_of_notMem₁ b hb
    apply w.ne_zero
    ext
    rw [hw, hresO₁, h0]
    rfl
  have hres_ne₂ : ∀ b : ↥D, b ∉ 𝔮 → resD₂ b ≠ 0 := by
    intro b hb h0
    obtain ⟨w, hw⟩ := hunit_of_notMem₂ b hb
    apply w.ne_zero
    ext
    rw [hw, hresO₂, h0]
    rfl

  have hinv₁ : ∀ b : ↥D, b ∉ 𝔮 → ((b : F))⁻¹ ∈ R₁.integers := by
    intro b hb
    have hbu : IsUnit (⟨(b : F), h1N _ (hDN _ b.2)⟩ : R₁.integers) :=
      R₁.isUnit_of_residue_ne_zero (by rw [hresD₁ b]; exact hres_ne₁ b hb)
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hbu
    have hwval : (b : F) * (w : F) = 1 := congrArg (fun z : R₁.integers => (z : F)) hw
    rw [← eq_inv_of_mul_eq_one_right hwval]
    exact w.2
  have hinv₂ : ∀ b : ↥D, b ∉ 𝔮 → ((b : F))⁻¹ ∈ R₂.integers := by
    intro b hb
    have hbu : IsUnit (⟨(b : F), h2N _ (hDN _ b.2)⟩ : R₂.integers) :=
      R₂.isUnit_of_residue_ne_zero (by rw [hresD₂ b]; exact hres_ne₂ b hb)
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hbu
    have hwval : (b : F) * (w : F) = 1 := congrArg (fun z : R₂.integers => (z : F)) hw
    rw [← eq_inv_of_mul_eq_one_right hwval]
    exact w.2
  have hev_ne : ∀ (P : Place L F) (hP : P ∈ S) (b : ↥D), b ∉ 𝔮 → P.evalAt (b : F) ≠ 0 := by
    intro P hP b hb h0
    apply hb
    rw [h𝔮P P hP]
    have : (evD P hP b : ↥A) = 0 := by ext; rw [hevD P hP]; exact h0
    rw [this]; exact zero_mem _
  have hinvP : ∀ (P : Place L F) (hP : P ∈ S) (b : ↥D), b ∉ 𝔮 → ((b : F))⁻¹ ∈ P.toValuationSubring := by
    intro P hP b hb
    have hbP : (b : F) ∈ P.toValuationSubring := hPN _ (hDN _ b.2) P hP
    have hbu : IsUnit (⟨(b : F), hbP⟩ : P.toValuationSubring) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      intro h0
      apply hev_ne P hP b hb
      have := P.algebraMap_evalAt (hrat P hP) hbP
      rw [h0, map_eq_zero] at this
      exact this
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hbu
    have hwval : (b : F) * (w : F) = 1 := congrArg (fun z : P.toValuationSubring => (z : F)) hw
    rw [← eq_inv_of_mul_eq_one_right hwval]
    exact w.2

  have h0N : 𝒩₀' ≤ 𝒩 := by
    rintro f ⟨a, b, hb, hfb⟩
    have hb0 : (b : F) ≠ 0 := coe_ne_zero_of_notMem D 𝔮 hb
    have hf : f = (a : F) * ((b : F))⁻¹ := by rw [← hfb, mul_inv_cancel_right₀ hb0]
    rw [h𝒩, hf]
    exact ⟨mul_mem (h1N _ (hDN _ a.2)) (hinv₁ b hb), mul_mem (h2N _ (hDN _ a.2)) (hinv₂ b hb),
      fun P hP => mul_mem (hPN _ (hDN _ a.2) P hP) (hinvP P hP b hb)⟩

  let inclN' : ↥𝒩₀' →+* ↥𝒩 :=
    { toFun := fun f => ⟨f, h0N f.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ev' : ∀ P : Place L F, P ∈ S → (↥𝒩₀' →+* ↥A) := fun P hP => (evN P hP).comp inclN'
  have hev' : ∀ (P : Place L F) (hP : P ∈ S) (f : ↥𝒩₀'), ((ev' P hP f : ↥A) : L) = P.evalAt (f : F) :=
    fun P hP f => rfl
  have hev'D : ∀ (P : Place L F) (hP : P ∈ S) (d : ↥D), ev' P hP ⟨d, hD0' d d.2⟩ = evD P hP d :=
    fun P hP d => rfl

  have hev'_frac : ∀ (P : Place L F) (hP : P ∈ S) (f : ↥𝒩₀') (a b : ↥D), (f : F) * b = a →
      ev' P hP f * evD P hP b = evD P hP a := by
    intro P hP f a b h
    rw [← hev'D P hP b, ← hev'D P hP a, ← map_mul]
    congr 1
    exact Subtype.ext h

  have hev'_nonunit : ∀ (P : Place L F) (hP : P ∈ S) (f : ↥𝒩₀'), ¬ IsUnit f → ev' P hP f ∈ maximalIdeal ↥A := by
    intro P hP f hf
    obtain ⟨a, b, hb, hfb⟩ := f.2
    have ha : a ∈ 𝔮 := by
      by_contra ha
      exact hf ((hunit' f a b hb hfb).mpr ha)
    have hbu : IsUnit (evD P hP b) := IsLocalRing.notMem_maximalIdeal.mp ((h𝔮P P hP b).not.mp hb)
    obtain ⟨u, hu⟩ := hbu
    have : ev' P hP f = evD P hP a * ↑u⁻¹ := by
      rw [← hev'_frac P hP f a b hfb, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ ((h𝔮P P hP a).mp ha)

  have hS' : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀' → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀', ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A) := by
    intro P
    constructor
    · intro hP
      refine ⟨fun f hf => hPN f (h0N hf) P hP, fun f hf => ⟨(ev' P hP f).2, ?_⟩⟩
      exact hev'_nonunit P hP f hf
    · rintro ⟨hint, hnu⟩
      rw [hS]
      refine ⟨fun f hf => hint f (h01 hf), fun r hr => ?_⟩
      have hloc_r : ¬ IsUnit (⟨(r : F), h01 r.2⟩ : ↥𝒩₀') := by
        rw [hunit' ⟨(r : F), h01 r.2⟩ (algebraMap ↥𝒩₀ ↥D r) 1
          (fun h => h𝔮prime.ne_top ((Ideal.eq_top_iff_one _).mpr h)) (by push_cast; rw [mul_one]; rfl)]
        intro hnot
        exact hnot (hJ𝔮 (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hr)))
      exact hnu ⟨(r : F), h01 r.2⟩ hloc_r

  have hC'mem' : ∀ c : L, c ∈ C' → algebraMap L F c ∈ 𝒩₀' := by
    intro c hc
    obtain ⟨yy, zz, hy, hz, hzC', hzinvC', hz0, hcz⟩ := hGdiv c hc
    have hzres : IsLocalRing.residue ↥A ⟨zz, hC' zz hzC'⟩ ≠ 0 := by
      rw [IsLocalRing.residue_ne_zero_iff_isUnit]
      refine isUnit_iff_exists_inv.mpr ⟨⟨zz⁻¹, hC' _ hzinvC'⟩, ?_⟩
      ext
      change zz * zz⁻¹ = 1
      exact mul_inv_cancel₀ hz0
    have hzD : algebraMap L F zz ∈ D := hspanD zz hz
    have hyD : algebraMap L F yy ∈ D := hspanD yy hy
    have hz𝔮 : (⟨algebraMap L F zz, hzD⟩ : ↥D) ∉ 𝔮 := by
      rw [h𝔮_dec ⟨algebraMap L F zz, hzD⟩ zz hzC' hzD (by rw [sub_self]; exact zero_mem _)]
      exact hzres
    refine ⟨⟨algebraMap L F yy, hyD⟩, ⟨algebraMap L F zz, hzD⟩, hz𝔮, ?_⟩
    change algebraMap L F c * algebraMap L F zz = algebraMap L F yy
    rw [← map_mul, hcz]

  have hres'' : ∀ g : ↥𝒩₀', ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ 𝒩₀'), ¬ IsUnit (g - ⟨_, h⟩) := by
    intro g
    obtain ⟨a, b, hb, hgb⟩ := g.2
    obtain ⟨α, hαC', hαD, hαJ⟩ := hQ a a.2
    obtain ⟨β, hβC', hβD, hβJ⟩ := hQ b b.2
    have hβres : IsLocalRing.residue ↥A ⟨β, hC' β hβC'⟩ ≠ 0 :=
      fun h0 => hb ((h𝔮_dec b β hβC' hβD hβJ).mpr h0)
    have hβinvC' : β⁻¹ ∈ C' := hinvC' β hβC' hβres
    set o : L := α * β⁻¹ with ho
    have hoC' : o ∈ C' := mul_mem hαC' hβinvC'
    refine ⟨⟨o, hoC'⟩, hC'mem' o hoC', ?_⟩
    intro hu

    have hunit_ev : IsUnit (ev' P₀ hP₀ (g - ⟨algebraMap L F o, hC'mem' o hoC'⟩)) := hu.map _
    have hres_ev : IsLocalRing.residue ↥A (ev' P₀ hP₀ (g - ⟨algebraMap L F o, hC'mem' o hoC'⟩)) = 0 := by
      rw [map_sub, map_sub, sub_eq_zero]

      have hfrac := congrArg (IsLocalRing.residue ↥A) (hev'_frac P₀ hP₀ g a b hgb)
      rw [map_mul, hev_dec P₀ hP₀ b β hβC' hβD hβJ, hev_dec P₀ hP₀ a α hαC' hαD hαJ] at hfrac

      have hevo : ev' P₀ hP₀ ⟨algebraMap L F o, hC'mem' o hoC'⟩ = ⟨o, hC' o hoC'⟩ := by
        ext
        rw [hev' P₀ hP₀]
        exact P₀.evalAt_algebraMap_eq o
      rw [hevo]
      have hβA : (⟨β, hC' β hβC'⟩ : ↥A) * ⟨β⁻¹, hC' _ hβinvC'⟩ = 1 := by
        ext
        change β * β⁻¹ = 1
        refine mul_inv_cancel₀ ?_
        rintro rfl
        apply hβres
        have : (⟨(0 : L), hC' 0 hβC'⟩ : ↥A) = 0 := rfl
        rw [this, map_zero]
      have hoA : (⟨o, hC' o hoC'⟩ : ↥A) = ⟨α, hC' α hαC'⟩ * ⟨β⁻¹, hC' _ hβinvC'⟩ := rfl
      rw [hoA, map_mul]
      have hβinvres : IsLocalRing.residue ↥A ⟨β⁻¹, hC' _ hβinvC'⟩ =
          (IsLocalRing.residue ↥A ⟨β, hC' β hβC'⟩)⁻¹ := by
        have := congrArg (IsLocalRing.residue ↥A) hβA
        rw [map_mul, map_one] at this
        exact (eq_inv_of_mul_eq_one_right this)
      rw [hβinvres, ← hfrac, mul_inv_cancel_right₀ hβres]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunit_ev) hres_ev

  have hincl_loc : ∀ f : ↥𝒩₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion h01 f) := by
    intro r hr
    have : Subring.inclusion h01 r = ⟨(r : F), h01 r.2⟩ := rfl
    rw [this, hunit' ⟨(r : F), h01 r.2⟩ (algebraMap ↥𝒩₀ ↥D r) 1
      (fun h => h𝔮prime.ne_top ((Ideal.eq_top_iff_one _).mpr h)) (by push_cast; rw [mul_one]; rfl)]
    intro hnot
    exact hnot (hJ𝔮 (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hr)))

  have hgen' : ∀ hϖ : algebraMap L F ((ϖ' : ↥C') : L) ∈ 𝒩₀',
      maximalIdeal ↥𝒩₀' ≤ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h01) ⊔ Ideal.span {⟨_, hϖ⟩} := by
    intro hϖN g hg
    obtain ⟨a, b, hb, hgb⟩ := g.2
    have ha : a ∈ 𝔮 := by
      by_contra ha
      exact ((mem_maximalIdeal _).mp hg) ((hunit' g a b hb hgb).mpr ha)
    obtain ⟨α, hαC', hαD, hαJ⟩ := hQ a a.2
    have hαres : IsLocalRing.residue ↥A ⟨α, hC' α hαC'⟩ = 0 := (h𝔮_dec a α hαC' hαD hαJ).mp ha
    obtain ⟨α', hα'⟩ := (hϖ' ⟨α, hαC'⟩).mp hαres
    have hαeq : α = ((ϖ' : ↥C') : L) * (α' : L) := congrArg Subtype.val hα'

    have hbinv : ((b : F))⁻¹ ∈ 𝒩₀' := ⟨1, b, hb, by rw [inv_mul_cancel₀ (coe_ne_zero_of_notMem D 𝔮 hb)]; push_cast; ring⟩
    have hb0 : (b : F) ≠ 0 := coe_ne_zero_of_notMem D 𝔮 hb

    have hsplit : g = ⟨algebraMap L F ((ϖ' : ↥C') : L), hϖN⟩ *
        ⟨algebraMap L F (α' : L) * ((b : F))⁻¹, mul_mem (hC'mem' _ α'.2) hbinv⟩ +
        ⟨((a - ⟨algebraMap L F α, hαD⟩ : ↥D) : F) * ((b : F))⁻¹,
          mul_mem (hD0' _ (a - ⟨algebraMap L F α, hαD⟩).2) hbinv⟩ := by
      ext
      change (g : F) = algebraMap L F ((ϖ' : ↥C') : L) * (algebraMap L F (α' : L) * ((b : F))⁻¹) +
        (((a : ↥D) : F) - algebraMap L F α) * ((b : F))⁻¹
      have hg' : (g : F) = (a : F) * ((b : F))⁻¹ := by rw [← hgb, mul_inv_cancel_right₀ hb0]
      rw [hg', hαeq, map_mul]
      ring
    rw [hsplit]
    refine add_mem (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left ?_)

    have hmapJ : J.map (toLoc D 𝔮) ≤ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h01) := by
      rw [hJdef, Ideal.map_map]
      have : (toLoc D 𝔮).comp (algebraMap ↥𝒩₀ ↥D) = Subring.inclusion h01 := RingHom.ext fun _ => rfl
      rw [this]
    have hmem : (toLoc D 𝔮 (a - ⟨algebraMap L F α, hαD⟩)) ∈ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h01) :=
      hmapJ (Ideal.mem_map_of_mem _ hαJ)
    have : (⟨((a - ⟨algebraMap L F α, hαD⟩ : ↥D) : F) * ((b : F))⁻¹,
        mul_mem (hD0' _ (a - ⟨algebraMap L F α, hαD⟩).2) hbinv⟩ : ↥𝒩₀') =
        toLoc D 𝔮 (a - ⟨algebraMap L F α, hαD⟩) * ⟨((b : F))⁻¹, hbinv⟩ := rfl
    rw [this]
    exact Ideal.mul_mem_right _ _ hmem

  have hreg₁' : ∀ (f : ↥𝒩₀') (h₁ : (f : F) ∈ R₁.integers), 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩) := by
    intro f h₁
    obtain ⟨a, b, hb, hfb⟩ := f.2
    apply ord_nonneg_of_mem

    have hmul : R₁.residue ⟨f, h₁⟩ * resD₁ b = resD₁ a := by
      rw [← hresD₁ b (h1N _ (hDN _ b.2)), ← hresD₁ a (h1N _ (hDN _ a.2)), ← map_mul]
      congr 1
      exact Subtype.ext hfb
    obtain ⟨w, hw⟩ := hunit_of_notMem₁ b hb
    have hwval : ((w : ↥x₁.toValuationSubring) : Fbar₁) = resD₁ b := by rw [hw]; rfl
    have : R₁.residue ⟨f, h₁⟩ = resD₁ a * ((↑w⁻¹ : ↥x₁.toValuationSubring) : Fbar₁) := by
      have hw1 : ((w : ↥x₁.toValuationSubring) : Fbar₁) * ((↑w⁻¹ : ↥x₁.toValuationSubring) : Fbar₁) = 1 := by
        have h := w.mul_inv
        have := congrArg (fun z : ↥x₁.toValuationSubring => (z : Fbar₁)) h
        simp only [OneMemClass.coe_one] at this
        exact this
      rw [← hmul, ← hwval, mul_assoc, hw1, mul_one]
    rw [this]
    exact mul_mem (hDreg₁ a) (↑w⁻¹ : ↥x₁.toValuationSubring).2
  have hreg₂' : ∀ (f : ↥𝒩₀') (h₂ : (f : F) ∈ R₂.integers), 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩) := by
    intro f h₂
    obtain ⟨a, b, hb, hfb⟩ := f.2
    apply ord_nonneg_of_mem
    have hmul : R₂.residue ⟨f, h₂⟩ * resD₂ b = resD₂ a := by
      rw [← hresD₂ b (h2N _ (hDN _ b.2)), ← hresD₂ a (h2N _ (hDN _ a.2)), ← map_mul]
      congr 1
      exact Subtype.ext hfb
    obtain ⟨w, hw⟩ := hunit_of_notMem₂ b hb
    have hwval : ((w : ↥x₂.toValuationSubring) : Fbar₂) = resD₂ b := by rw [hw]; rfl
    have : R₂.residue ⟨f, h₂⟩ = resD₂ a * ((↑w⁻¹ : ↥x₂.toValuationSubring) : Fbar₂) := by
      have hw1 : ((w : ↥x₂.toValuationSubring) : Fbar₂) * ((↑w⁻¹ : ↥x₂.toValuationSubring) : Fbar₂) = 1 := by
        have h := w.mul_inv
        have := congrArg (fun z : ↥x₂.toValuationSubring => (z : Fbar₂)) h
        simp only [OneMemClass.coe_one] at this
        exact this
      rw [← hmul, ← hwval, mul_assoc, hw1, mul_one]
    rw [this]
    exact mul_mem (hDreg₂ a) (↑w⁻¹ : ↥x₂.toValuationSubring).2

  have hdim : 2 ≤ ringKrullDim ↥𝒩₀' := by
    let res₁' : ↥𝒩₀' →+* Fbar₁ := resN₁.comp inclN'
    have hres₁' : ∀ f : ↥𝒩₀', res₁' f = R₁.residue ⟨(f : F), h1N _ (h0N f.2)⟩ := fun f => rfl
    let 𝔭₁ : Ideal ↥𝒩₀' := RingHom.ker res₁'
    haveI : 𝔭₁.IsPrime := RingHom.ker_isPrime _
    have hxN' : x ∈ 𝒩₀' := h01 hx
    have hyN' : y ∈ 𝒩₀' := h01 hy
    have hx𝔭 : (⟨x, hxN'⟩ : ↥𝒩₀') ∈ 𝔭₁ := by
      rw [RingHom.mem_ker, hres₁']; exact x_fst _
    have hx0 : (⟨x, hxN'⟩ : ↥𝒩₀') ≠ 0 := by
      intro h0
      apply x_snd (h2N x (h𝒩₀ hx))
      have : x = 0 := congrArg Subtype.val h0
      have h00 : (⟨x, h2N x (h𝒩₀ hx)⟩ : R₂.integers) = 0 := Subtype.ext this
      rw [h00, map_zero]
    have hy𝔭 : (⟨y, hyN'⟩ : ↥𝒩₀') ∉ 𝔭₁ := by
      rw [RingHom.mem_ker, hres₁']; exact y_fst _
    have hy𝔪 : (⟨y, hyN'⟩ : ↥𝒩₀') ∈ maximalIdeal ↥𝒩₀' := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
      have hyu : IsUnit (⟨y, h2N y (h𝒩₀ hy)⟩ : R₂.integers) := by
        refine isUnit_iff_exists_inv.mpr ⟨⟨(w : F), h2N _ (h0N w.2)⟩, ?_⟩
        ext; exact congrArg (fun t : ↥𝒩₀' => (t : F)) hw
      exact R₂.residue_ne_zero_of_isUnit hyu (y_snd _)
    have h𝔭𝔪 : 𝔭₁ ≤ maximalIdeal ↥𝒩₀' := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)

    let p0 : PrimeSpectrum ↥𝒩₀' := ⟨⊥, Ideal.isPrime_bot⟩
    let p1 : PrimeSpectrum ↥𝒩₀' := ⟨𝔭₁, inferInstance⟩
    let p2 : PrimeSpectrum ↥𝒩₀' := ⟨maximalIdeal ↥𝒩₀', (maximalIdeal.isMaximal _).isPrime⟩
    have h01' : p0 < p1 := by
      refine lt_of_le_of_ne (fun z hz => by
        have : z = 0 := hz
        rw [this]; exact zero_mem _) ?_
      intro h
      have : (⟨x, hxN'⟩ : ↥𝒩₀') ∈ (⊥ : Ideal ↥𝒩₀') := by
        have := congrArg PrimeSpectrum.asIdeal h
        change ⊥ = 𝔭₁ at this
        rw [this]; exact hx𝔭
      exact hx0 this
    have h12' : p1 < p2 := by
      refine lt_of_le_of_ne (fun z hz => h𝔭𝔪 hz) ?_
      intro h
      have : (⟨y, hyN'⟩ : ↥𝒩₀') ∈ 𝔭₁ := by
        have := congrArg PrimeSpectrum.asIdeal h
        change 𝔭₁ = maximalIdeal _ at this
        rw [this]; exact hy𝔪
      exact hy𝔭 this
    let l : LTSeries (PrimeSpectrum ↥𝒩₀') :=
      { length := 2
        toFun := ![p0, p1, p2]
        step := by
          intro i
          fin_cases i
          · exact h01'
          · exact h12' }
    exact Order.le_krullDim_iff.mpr ⟨l, rfl⟩

  let C'mod : Submodule ↥C L :=
    { carrier := C'
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      smul_mem' := fun c a ha => by
        change (c : L) • a ∈ C'
        rw [smul_eq_mul]
        exact mul_mem (hCC' _ c.2) ha }
  have hmemC'mod : ∀ z : L, z ∈ C'mod ↔ z ∈ C' := fun z => Iff.rfl

  have hexp : ∀ d : ↥D, ∃ (m : ℕ) (nn : Fin m → ↥𝒩₀) (ε : Fin m → L), (∀ j, ε j ∈ C') ∧
      (d : F) = ∑ j, ((nn j : ↥𝒩₀) : F) * algebraMap L F (ε j) := by
    intro d
    have hd : (d : F) ∈ Submodule.span ↥𝒩₀ (Submonoid.closure Gimg : Set F) := by
      rw [← Algebra.adjoin_eq_span]; exact d.2
    obtain ⟨m, nn, g, hg⟩ := Submodule.mem_span_set'.mp hd
    have hcl : (Submonoid.closure Gimg : Set F) ⊆ (algebraMap L F) '' (C' : Set L) := by
      intro z hz
      have hle : Submonoid.closure Gimg ≤ (C'.map (algebraMap L F)).toSubmonoid :=
        Submonoid.closure_le.mpr (by
          rintro _ ⟨g', hg', rfl⟩
          exact ⟨g', hGC' hg', rfl⟩)
      obtain ⟨w, hw, hwz⟩ := (Subring.mem_map.mp (hle hz))
      exact ⟨w, hw, hwz⟩
    choose ε hεC' hεeq using fun j => hcl (g j).2
    refine ⟨m, nn, ε, hεC', ?_⟩
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, hεeq j]
    rfl
  have hld' : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀'), LinearIndependent ↥C' c →
      ∑ i, c i • ((a i : ↥𝒩₀') : F) = 0 → ∀ i, a i = 0 := by
    intro n c a hc hsum

    choose num den hden hfrac using fun i => (a i).2
    set B : ↥D := ∏ i, den i with hBdef
    have hB : B ∉ 𝔮 := by
      rw [hBdef, Ideal.IsPrime.prod_mem_iff]
      rintro ⟨i, -, hi⟩
      exact hden i hi
    have hB0 : (B : F) ≠ 0 := coe_ne_zero_of_notMem D 𝔮 hB
    have hBval : ∀ i, (B : F) = (den i : F) * ∏ j ∈ Finset.univ.erase i, (den j : F) := by
      intro i
      rw [hBdef]
      push_cast
      rw [Finset.mul_prod_erase _ (fun j => ((den j : ↥D) : F)) (Finset.mem_univ i)]
    set α : Fin n → ↥D := fun i => num i * ∏ j ∈ Finset.univ.erase i, den j with hαdef
    have hαval : ∀ i, (α i : F) = ((a i : ↥𝒩₀') : F) * B := by
      intro i
      rw [hαdef]
      push_cast
      rw [← hfrac i, hBval i, mul_assoc]
    have hsumα : ∑ i, algebraMap L F (c i) * (α i : F) = 0 := by
      have : ∑ i, algebraMap L F (c i) * (α i : F) = (∑ i, c i • ((a i : ↥𝒩₀') : F)) * B := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hαval, Algebra.smul_def, mul_assoc]
      rw [this, hsum, zero_mul]

    suffices hα0 : ∀ i, α i = 0 by
      intro i
      have h1 := congrArg (fun d : ↥D => (d : F)) (hα0 i)
      simp only [hαval, ZeroMemClass.coe_zero, mul_eq_zero] at h1
      ext
      exact h1.resolve_right hB0

    choose m nn ε hεC' hαexp using fun i => hexp (α i)

    let T := Σ i : Fin n, Fin (m i)
    let εT : T → L := fun t => ε t.1 t.2
    set E : Submodule ↥C L := Submodule.span ↥C (Set.range εT) with hEdef
    haveI : Module.Finite ↥C ↥E := Module.Finite.span_of_finite ↥C (Set.finite_range εT)
    haveI : Module.Free ↥C ↥E := Module.free_of_finite_type_torsion_free'
    let bs := Module.Free.chooseBasis ↥C ↥E
    have hEC' : E ≤ C'mod := by
      rw [hEdef, Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact hεC' t.1 t.2
    have hbsC' : ∀ j, ((bs j : ↥E) : L) ∈ C' := fun j => hEC' (bs j).2
    have hεE : ∀ (i : Fin n) (jj : Fin (m i)), ε i jj ∈ E := fun i jj =>
      Submodule.subset_span ⟨⟨i, jj⟩, rfl⟩

    let r : ∀ i : Fin n, Fin (m i) → Module.Free.ChooseBasisIndex ↥C ↥E → ↥C :=
      fun i jj => bs.repr ⟨ε i jj, hεE i jj⟩
    have hεexp : ∀ (i : Fin n) (jj : Fin (m i)),
        ε i jj = ∑ l, ((r i jj l : ↥C) : L) * ((bs l : ↥E) : L) := by
      intro i jj
      have h1 := bs.sum_repr ⟨ε i jj, hεE i jj⟩
      have h2 := congrArg (fun z : ↥E => (z : L)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def]
      rfl

    let N : Fin n → Module.Free.ChooseBasisIndex ↥C ↥E → ↥𝒩₀ := fun i l =>
      ∑ jj, ⟨algebraMap L F ((r i jj l : ↥C) : L), hCmem _ (r i jj l).2⟩ * nn i jj
    have hNval : ∀ i l, ((N i l : ↥𝒩₀) : F) =
        ∑ jj, algebraMap L F ((r i jj l : ↥C) : L) * ((nn i jj : ↥𝒩₀) : F) := by
      intro i l
      simp only [N]
      push_cast
      rfl
    have hαN : ∀ i, (α i : F) = ∑ l, algebraMap L F ((bs l : ↥E) : L) * ((N i l : ↥𝒩₀) : F) := by
      intro i
      rw [hαexp i]
      simp_rw [hεexp i, map_sum, map_mul, Finset.mul_sum, hNval, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun jj _ => ?_
      ring

    have hli : LinearIndependent ↥C
        (fun q : Fin n × Module.Free.ChooseBasisIndex ↥C ↥E => c q.1 * ((bs q.2 : ↥E) : L)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg

      have hcoef : ∀ i, (∑ l, ((g (i, l) : ↥C) : L) * ((bs l : ↥E) : L)) ∈ C' :=
        fun i => sum_mem fun l _ => mul_mem (hCC' _ (g (i, l)).2) (hbsC' l)
      have hsumC' : ∑ i, (⟨_, hcoef i⟩ : ↥C') • c i = 0 := by
        rw [← hg, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        change (∑ l, ((g (i, l) : ↥C) : L) * ((bs l : ↥E) : L)) • c i = _
        rw [smul_eq_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        change _ = ((g (i, l) : ↥C) : L) • (c i * ((bs l : ↥E) : L))
        rw [smul_eq_mul]
        ring
      have hci := (Fintype.linearIndependent_iff.mp hc) (fun i => ⟨_, hcoef i⟩) hsumC'
      rintro ⟨i, l⟩
      have h1 : (∑ l, ((g (i, l) : ↥C) : L) * ((bs l : ↥E) : L)) = 0 := congrArg Subtype.val (hci i)

      have h2 : (∑ l, g (i, l) • bs l : ↥E) = 0 := by
        apply Subtype.ext
        simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero]
        rw [← h1]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Algebra.smul_def]
        rfl
      exact (Fintype.linearIndependent_iff.mp bs.linearIndependent) (fun l => g (i, l)) h2 l

    have hN0 := ld_fintype C 𝒩₀ hld
      (fun q : Fin n × Module.Free.ChooseBasisIndex ↥C ↥E => c q.1 * ((bs q.2 : ↥E) : L))
      (fun q => N q.1 q.2) hli (by
        rw [Fintype.sum_prod_type, ← hsumα]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hαN i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Algebra.smul_def, map_mul]
        ring)
    intro i
    apply Subtype.ext
    rw [hαN i, ZeroMemClass.coe_zero]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : N i l = 0 := hN0 (i, l)
    rw [this, ZeroMemClass.coe_zero, mul_zero]

  have hϖA : ((ϖ' : ↥C') : L) ∈ A := hC' _ ϖ'.2
  have hw1 : algebraMap L F ((ϖ' : ↥C') : L) ∈ 𝒩₀' := hC'mem' _ ϖ'.2
  have hwres₁ : ∀ h : algebraMap L F ((ϖ' : ↥C') : L) ∈ R₁.integers,
      R₁.residue ⟨algebraMap L F ((ϖ' : ↥C') : L), h⟩ = 0 := by
    intro h
    have := R₁.residue_algebraMap ⟨((ϖ' : ↥C') : L), hϖA⟩
    rw [hϖ'res, map_zero] at this
    exact this
  have hwres₂ : ∀ h : algebraMap L F ((ϖ' : ↥C') : L) ∈ R₂.integers,
      R₂.residue ⟨algebraMap L F ((ϖ' : ↥C') : L), h⟩ = 0 := by
    intro h
    have := R₂.residue_algebraMap ⟨((ϖ' : ↥C') : L), hϖA⟩
    rw [hϖ'res, map_zero] at this
    exact this
  have hN1' : ∀ f : F, f ∈ 𝒩₀' → f ∈ R₁.integers := fun f hf => h1N f (h0N hf)
  have hN2' : ∀ f : F, f ∈ 𝒩₀' → f ∈ R₂.integers := fun f hf => h2N f (h0N hf)
  have hpos₁ := AlgebraicCurve.RegularProlongation.forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span A R₁ x₁
    𝒩₀ 𝒩₀' h01 hN1' hreg₁ hreg₁' _ hw1 hwres₁ (hgen' hw1)
  have hpos₂ := AlgebraicCurve.RegularProlongation.forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span A R₂ x₂
    𝒩₀ 𝒩₀' h01 hN2' hreg₂ hreg₂' _ hw1 hwres₂ (hgen' hw1)

  have h1𝔮 : (1 : ↥D) ∉ 𝔮 := fun h1 => h𝔮prime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hunit01 : ∀ (H : F) (hH : H ∈ 𝒩₀), IsUnit (⟨H, hH⟩ : ↥𝒩₀) → IsUnit (⟨H, h01 hH⟩ : ↥𝒩₀') := by
    intro H hH hu
    have := hu.map (Subring.inclusion h01)
    exact this
  have hpres : ∀ B₀ : Subring F, B₀ ≤ 𝒩₀ →
      (∀ f : F, f ∈ 𝒩₀ ↔ ∃ g h : F, g ∈ B₀ ∧ h ∈ B₀ ∧ (∀ hh : h ∈ 𝒩₀, IsUnit (⟨h, hh⟩ : ↥𝒩₀)) ∧ f * h = g) →
      ∀ f : F, f ∈ 𝒩₀' ↔ ∃ g h : F,
        g ∈ Subring.closure ((B₀ : Set F) ∪ {x : F | ∃ c : L, c ∈ C' ∧ x = algebraMap L F c}) ∧
        h ∈ Subring.closure ((B₀ : Set F) ∪ {x : F | ∃ c : L, c ∈ C' ∧ x = algebraMap L F c}) ∧
        (∀ hh : h ∈ 𝒩₀', IsUnit (⟨h, hh⟩ : ↥𝒩₀')) ∧ f * h = g := by
    intro B₀ hB₀ hB f
    set E : Subring F := Subring.closure ((B₀ : Set F) ∪ {x : F | ∃ c : L, c ∈ C' ∧ x = algebraMap L F c})
      with hE
    have hBE : ∀ b : F, b ∈ B₀ → b ∈ E := fun b hb => Subring.subset_closure (Or.inl hb)
    have hCE : ∀ c : L, c ∈ C' → algebraMap L F c ∈ E := fun c hc =>
      Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)
    have hEN' : ∀ e : F, e ∈ E → e ∈ 𝒩₀' := by
      intro e he
      refine (Subring.closure_le.mpr ?_) he
      rintro z (hz | ⟨c, hc, rfl⟩)
      · exact h01 (hB₀ hz)
      · exact hC'mem' c hc
    constructor
    · intro hf

      let T : Subalgebra ↥𝒩₀ F :=
        { carrier := {d | ∃ H : F, H ∈ B₀ ∧ (∀ hh : H ∈ 𝒩₀, IsUnit (⟨H, hh⟩ : ↥𝒩₀)) ∧ H * d ∈ E}
          mul_mem' := by
            rintro d₁ d₂ ⟨H₁, hH₁B, hH₁u, hH₁E⟩ ⟨H₂, hH₂B, hH₂u, hH₂E⟩
            refine ⟨H₁ * H₂, mul_mem hH₁B hH₂B, fun hh => ?_, ?_⟩
            · have h12 : (⟨H₁ * H₂, hh⟩ : ↥𝒩₀) = ⟨H₁, hB₀ hH₁B⟩ * ⟨H₂, hB₀ hH₂B⟩ := Subtype.ext rfl
              rw [h12]
              exact (hH₁u _).mul (hH₂u _)
            · have : H₁ * H₂ * (d₁ * d₂) = (H₁ * d₁) * (H₂ * d₂) := by ring
              show H₁ * H₂ * (d₁ * d₂) ∈ E
              rw [this]
              exact mul_mem hH₁E hH₂E
          one_mem' := ⟨1, one_mem _, fun _ => isUnit_one, by rw [one_mul]; exact one_mem _⟩
          add_mem' := by
            rintro d₁ d₂ ⟨H₁, hH₁B, hH₁u, hH₁E⟩ ⟨H₂, hH₂B, hH₂u, hH₂E⟩
            refine ⟨H₁ * H₂, mul_mem hH₁B hH₂B, fun hh => ?_, ?_⟩
            · have h12 : (⟨H₁ * H₂, hh⟩ : ↥𝒩₀) = ⟨H₁, hB₀ hH₁B⟩ * ⟨H₂, hB₀ hH₂B⟩ := Subtype.ext rfl
              rw [h12]
              exact (hH₁u _).mul (hH₂u _)
            · have : H₁ * H₂ * (d₁ + d₂) = H₂ * (H₁ * d₁) + H₁ * (H₂ * d₂) := by ring
              show H₁ * H₂ * (d₁ + d₂) ∈ E
              rw [this]
              exact add_mem (mul_mem (hBE _ hH₂B) hH₁E) (mul_mem (hBE _ hH₁B) hH₂E)
          zero_mem' := ⟨1, one_mem _, fun _ => isUnit_one, by rw [mul_zero]; exact zero_mem _⟩
          algebraMap_mem' := by
            intro r
            obtain ⟨g, h, hg, hh, hu, hfh⟩ := (hB (r : F)).mp r.2
            refine ⟨h, hh, hu, ?_⟩
            change h * (r : F) ∈ E
            rw [mul_comm, hfh]
            exact hBE g hg }
      have hmemT : ∀ d : F, d ∈ T ↔
          ∃ H : F, H ∈ B₀ ∧ (∀ hh : H ∈ 𝒩₀, IsUnit (⟨H, hh⟩ : ↥𝒩₀)) ∧ H * d ∈ E := fun d => Iff.rfl
      have hDT : D ≤ T := by
        rw [hDdef]
        refine Algebra.adjoin_le ?_
        rintro _ ⟨g, hg, rfl⟩
        exact (hmemT _).mpr ⟨1, one_mem _, fun _ => isUnit_one, by rw [one_mul]; exact hCE g (hGC' hg)⟩
      obtain ⟨a, b, hb, hfab⟩ := (mem_locSubring_iff D 𝔮 f).mp hf
      obtain ⟨Ha, hHaB, hHau, hHaE⟩ := (hmemT _).mp (hDT a.2)
      obtain ⟨Hb, hHbB, hHbu, hHbE⟩ := (hmemT _).mp (hDT b.2)
      refine ⟨Hb * (Ha * (a : F)), Hb * (b : F) * Ha, mul_mem (hBE _ hHbB) hHaE, mul_mem hHbE (hBE _ hHaB),
        fun hh => ?_, ?_⟩
      · have hbu : IsUnit (⟨(b : F), hD0' _ b.2⟩ : ↥𝒩₀') :=
          (hunit' ⟨(b : F), hD0' _ b.2⟩ b 1 h1𝔮 (by rw [OneMemClass.coe_one, mul_one])).mpr hb
        have hsplit : (⟨Hb * (b : F) * Ha, hh⟩ : ↥𝒩₀') =
            ⟨Hb, h01 (hB₀ hHbB)⟩ * ⟨(b : F), hD0' _ b.2⟩ * ⟨Ha, h01 (hB₀ hHaB)⟩ := Subtype.ext rfl
        rw [hsplit]
        exact ((hunit01 Hb (hB₀ hHbB) (hHbu (hB₀ hHbB))).mul hbu).mul (hunit01 Ha (hB₀ hHaB) (hHau (hB₀ hHaB)))
      · calc f * (Hb * (b : F) * Ha) = Hb * (Ha * (f * (b : F))) := by ring
          _ = Hb * (Ha * (a : F)) := by rw [hfab]
    · rintro ⟨g, h, hg, hh, hu, hfh⟩
      have hh' : h ∈ 𝒩₀' := hEN' h hh
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp (hu hh')
      have hwF : h * ((w : ↥𝒩₀') : F) = 1 := congrArg Subtype.val hw
      have hfg : f = g * ((w : ↥𝒩₀') : F) := by
        calc f = f * (h * ((w : ↥𝒩₀') : F)) := by rw [hwF, mul_one]
          _ = (f * h) * ((w : ↥𝒩₀') : F) := by ring
          _ = g * ((w : ↥𝒩₀') : F) := by rw [hfh]
      rw [hfg]
      exact mul_mem (hEN' g hg) w.2

  exact ⟨𝒩₀', hloc', hnoe', h01, h0N, hS', hC'mem', hres'', hld', hincl_loc, hgen', hpos₁, hpos₂, hdim, hpres⟩

end S_AlgebraicCurve_NodeAnnulusEngine_exists_localizedBaseChange_of_layer_pos_localization
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_localizedBaseChange_of_layer_pos_localization (solution)
