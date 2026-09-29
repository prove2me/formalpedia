-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_forall_mem_iff_adjoin_sup_of_linearDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/33deca2a-0b3b-5010-a38b-cf7a1732437e

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_forall_mem_iff_adjoin_sup_of_linearDisjoint

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 3200000 in

theorem solution
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra k₀ F] [Algebra L F] [IsScalarTower k₀ L F]
    (F₀ : IntermediateField k₀ F) (K₁ : IntermediateField k₀ L)
    (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) →
      LinearIndependent ↥K₁ c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0)
    (hdvr : ∀ O : ValuationSubring F, (∀ x : L, algebraMap L F x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O)
    (V₁ : ValuationSubring ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))
    (hK₁V : ∀ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀),
      (⟨algebraMap L F (x : L), hx⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ∈ V₁)
    (hV₁ : V₁ ≠ ⊤) :
    ∃ P : Place L F, ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁ := by
  classical
  let ι₁ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) →+* F := algebraMap ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) F
  have hι₁ : ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), ι₁ f = (f : F) := fun f => rfl

  have hK₁mem : ∀ x : ↥K₁, algebraMap L F (x : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ := fun x =>
    (le_sup_left : IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ≤ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
      (IntermediateField.subset_adjoin k₀ _ ⟨(x : L), x.2, rfl⟩)
  let κ₁ : ↥K₁ → ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) := fun x => ⟨algebraMap L F (x : L), hK₁mem x⟩
  have hκ₁V : ∀ x : ↥K₁, κ₁ x ∈ V₁ := fun x => hK₁V x (hK₁mem x)
  have hκ₁coe : ∀ x : ↥K₁, ((κ₁ x : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) : F) = algebraMap L F (x : L) := fun x => rfl

  have hnu_iff : ∀ x : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), x ∈ V₁.nonunits ↔ V₁.valuation x < 1 := fun x => V₁.mem_nonunits_iff
  have hnu_mem : ∀ x : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), x ∈ V₁.nonunits → x ∈ V₁ := fun x hx => V₁.nonunits_subset hx
  have hnu_add : ∀ x y : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), x ∈ V₁.nonunits → y ∈ V₁.nonunits → x + y ∈ V₁.nonunits := by
    intro x y hx hy
    rw [hnu_iff] at hx hy ⊢
    exact lt_of_le_of_lt (V₁.valuation.map_add x y) (max_lt hx hy)
  have hnu_zero : (0 : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ∈ V₁.nonunits := by rw [hnu_iff, map_zero]; exact zero_lt_one
  have hnu_mul : ∀ x y : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), x ∈ V₁ → y ∈ V₁.nonunits → x * y ∈ V₁.nonunits := by
    intro x y hx hy
    rw [hnu_iff] at hy ⊢
    rw [map_mul]
    calc V₁.valuation x * V₁.valuation y ≤ 1 * V₁.valuation y := by
          gcongr; exact (V₁.valuation_le_one_iff x).mpr hx
      _ = V₁.valuation y := one_mul _
      _ < 1 := hy
  have hnu_sum : ∀ (n : ℕ) (g : Fin n → ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)), (∀ i, g i ∈ V₁.nonunits) → ∑ i, g i ∈ V₁.nonunits := by
    intro n g hg
    induction n with
    | zero => simp [hnu_zero]
    | succ n ih => rw [Fin.sum_univ_castSucc]; exact hnu_add _ _ (ih _ fun i => hg _) (hg _)
  have hnu_inv : ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), f ∉ V₁ → f⁻¹ ∈ V₁.nonunits := by
    intro f hf
    have hf0 : f ≠ 0 := fun h => hf (h ▸ V₁.zero_mem)
    rw [hnu_iff, map_inv₀, inv_lt_one₀ (lt_of_le_of_ne zero_le' ((map_ne_zero V₁.valuation).mpr hf0).symm)]
    exact lt_of_not_ge (fun h => hf ((V₁.valuation_le_one_iff f).mp h))

  have hK₁unit : ∀ x : ↥K₁, κ₁ x ∈ V₁.nonunits → x = 0 := by
    intro x hx
    by_contra h0
    rw [hnu_iff] at hx
    have hxL : (x : L) ≠ 0 := fun h => h0 (Subtype.ext h)
    have hxF : (κ₁ x : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ≠ 0 := fun h => hxL (by
      have h' := congrArg (fun z : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) => (z : F)) h
      exact (map_eq_zero_iff _ (algebraMap L F).injective).mp h')
    have hinv' : (κ₁ x)⁻¹ ∈ V₁ := by
      have : κ₁ x⁻¹ = (κ₁ x)⁻¹ := Subtype.ext (by
        show algebraMap L F ((x⁻¹ : ↥K₁) : L) = (algebraMap L F (x : L))⁻¹
        rw [← map_inv₀]; rfl)
      rw [← this]; exact hκ₁V x⁻¹
    have h1 : V₁.valuation ((κ₁ x)⁻¹) ≤ 1 := (V₁.valuation_le_one_iff _).mpr hinv'
    rw [map_inv₀, inv_le_one₀ (lt_of_le_of_ne zero_le' ((map_ne_zero V₁.valuation).mpr hxF).symm)] at h1
    exact (not_lt.mpr h1) hx

  let SV : Set F := ι₁ '' (V₁ : Set ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))
  let SM : Set F := ι₁ '' (V₁.nonunits : Set ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))
  let RL : Submodule L F := Submodule.span L SV
  let IL : Submodule L F := Submodule.span L SM
  have hSVmul : ∀ x ∈ SV, ∀ y ∈ SV, x * y ∈ SV := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩; exact ⟨a * b, mul_mem ha hb, map_mul _ _ _⟩
  have hSVSM : ∀ x ∈ SV, ∀ y ∈ SM, x * y ∈ SM := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩; exact ⟨a * b, hnu_mul a b ha hb, map_mul _ _ _⟩
  have hone_SV : (1 : F) ∈ SV := ⟨1, one_mem _, map_one _⟩
  have hRLmul : ∀ x ∈ RL, ∀ y ∈ RL, x * y ∈ RL := by
    intro x hx y hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro z ⟨a, ha, b, hb, rfl⟩; exact hSVmul a ha b hb
  have hRLIL : ∀ x ∈ RL, ∀ y ∈ IL, x * y ∈ IL := by
    intro x hx y hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro z ⟨a, ha, b, hb, rfl⟩; exact hSVSM a ha b hb
  let R₀ : Subring F :=
    { carrier := RL
      mul_mem' := fun {x y} hx hy => hRLmul x hx y hy
      one_mem' := Submodule.subset_span hone_SV
      add_mem' := fun {x y} hx hy => RL.add_mem hx hy
      zero_mem' := RL.zero_mem
      neg_mem' := fun {x} hx => RL.neg_mem hx }
  let I : Ideal ↥R₀ :=
    { carrier := {a | (a : F) ∈ IL}
      add_mem' := fun {a b} ha hb => IL.add_mem ha hb
      zero_mem' := IL.zero_mem
      smul_mem' := fun r a ha => hRLIL r r.2 a ha }
  have hImem : ∀ a : ↥R₀, a ∈ I ↔ (a : F) ∈ IL := fun a => Iff.rfl

  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : ((1 : ↥R₀) : F) ∈ IL := (hImem 1).mp (htop.symm ▸ Submodule.mem_top)
    rw [OneMemClass.coe_one, Submodule.mem_span_set'] at h1
    obtain ⟨n, c, g, hsum⟩ := h1
    have hg : ∀ i, ∃ a : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), a ∈ V₁.nonunits ∧ ι₁ a = (g i : F) := fun i => by
      obtain ⟨a, ha, hga⟩ := (g i).2; exact ⟨a, ha, hga⟩
    choose a ha using hg
    have hsum' : ∑ i, algebraMap L F (c i) * (a i : F) = 1 := by
      rw [← hsum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, ← hι₁, (ha i).2]

    let W : Submodule ↥K₁ L := Submodule.span ↥K₁ (Set.range c)
    haveI : Module.Finite ↥K₁ ↥W := Module.Finite.span_of_finite ↥K₁ (Set.finite_range _)
    haveI : Module.Free ↥K₁ ↥W := Module.Free.of_divisionRing ↥K₁ ↥W
    let b := Module.finBasis ↥K₁ ↥W
    set d := Module.finrank ↥K₁ ↥W with hd
    let ℓ : Fin d → L := fun j => ((b j : ↥W) : L)
    have hℓind : LinearIndependent ↥K₁ ℓ := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hcW : ∀ i, c i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
    let β : Fin n → Fin d → ↥K₁ := fun i j => b.repr ⟨c i, hcW i⟩ j
    have hcexp : ∀ i, c i = ∑ j, ((β i j : ↥K₁) : L) * ℓ j := by
      intro i
      have h := b.sum_repr ⟨c i, hcW i⟩
      have h' := congrArg (fun w : ↥W => (w : L)) h
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
      rw [← h']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, IntermediateField.algebraMap_apply]

    let A : Fin d → ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) := fun j => ∑ i, κ₁ (β i j) * a i
    have hA : ∀ j, A j ∈ V₁.nonunits := fun j =>
      hnu_sum n _ fun i => hnu_mul _ _ (hκ₁V _) (ha i).1
    have hsumA : ∑ j, algebraMap L F (ℓ j) * (A j : F) = 1 := by
      rw [← hsum']
      simp only [A, IntermediateField.coe_sum, IntermediateField.coe_mul, hκ₁coe]
      simp_rw [hcexp, map_sum, map_mul]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

    by_cases hone : (1 : L) ∈ Submodule.span ↥K₁ (Set.range ℓ)
    · obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ↥K₁).mp hone
      have hγ' : ∑ j, algebraMap L F ((γ j : ↥K₁) : L) * algebraMap L F (ℓ j) = 1 := by
        have h := congrArg (algebraMap L F) hγ
        rw [map_sum, map_one] at h
        rw [← h]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, map_mul]
      have hrel : ∑ j, algebraMap L F (ℓ j) * ((A j : F) - algebraMap L F ((γ j : ↥K₁) : L)) = 0 := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, hsumA]
        have : ∑ j, algebraMap L F (ℓ j) * algebraMap L F ((γ j : ↥K₁) : L) = 1 := by
          rw [← hγ']; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [this, sub_self]
      have hmemF₁ : ∀ j, (A j : F) - algebraMap L F ((γ j : ↥K₁) : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ := fun j =>
        sub_mem (A j).2 (hK₁mem (γ j))
      have hzero := hld d ℓ (fun j => (A j : F) - algebraMap L F ((γ j : ↥K₁) : L)) hmemF₁ hℓind hrel
      have hγ0 : ∀ j, γ j = 0 := by
        intro j
        apply hK₁unit
        have : κ₁ (γ j) = A j := Subtype.ext (by rw [hκ₁coe]; exact (sub_eq_zero.mp (hzero j)).symm)
        rw [this]; exact hA j
      have : (1 : F) = 0 := by
        rw [← hγ']; exact Finset.sum_eq_zero fun j _ => by rw [hγ0 j]; simp
      exact one_ne_zero this
    · let ℓ' : Fin (d + 1) → L := Fin.snoc (α := fun _ => L) ℓ 1
      let A' : Fin (d + 1) → F := Fin.snoc (α := fun _ => F) (fun j => (A j : F)) (-1)
      have hℓ'c : ∀ j : Fin d, ℓ' j.castSucc = ℓ j := fun j => Fin.snoc_castSucc (α := fun _ => L) _ _ j
      have hℓ'l : ℓ' (Fin.last d) = 1 := Fin.snoc_last (α := fun _ => L) _ _
      have hA'c : ∀ j : Fin d, A' j.castSucc = (A j : F) := fun j => Fin.snoc_castSucc (α := fun _ => F) _ _ j
      have hA'l : A' (Fin.last d) = -1 := Fin.snoc_last (α := fun _ => F) _ _
      have hind : LinearIndependent ↥K₁ ℓ' :=
        (linearIndependent_fin_snoc (K := ↥K₁) (x := (1 : L)) (v := ℓ)).mpr ⟨hℓind, hone⟩
      have hmemF₁ : ∀ i, A' i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [hA'l]; exact neg_mem (one_mem _)
        · rw [hA'c]; exact (A j).2
      have hrel : ∑ i, algebraMap L F (ℓ' i) * A' i = 0 := by
        rw [Fin.sum_univ_castSucc]
        simp only [hℓ'c, hℓ'l, hA'c, hA'l, map_one, one_mul]
        rw [hsumA, add_neg_cancel]
      have hzero := hld (d + 1) ℓ' A' hmemF₁ hind hrel (Fin.last d)
      rw [hA'l] at hzero
      exact one_ne_zero (neg_eq_zero.mp hzero)

  obtain ⟨O, hRO, hIO⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hLO : ∀ x : L, algebraMap L F x ∈ O := by
    intro x
    apply hRO
    show algebraMap L F x ∈ RL
    have : algebraMap L F x = x • (1 : F) := by rw [Algebra.smul_def, mul_one]
    rw [this]
    exact RL.smul_mem x (Submodule.subset_span hone_SV)
  have hVO : ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), f ∈ V₁ → (f : F) ∈ O := fun f hf =>
    hRO (show (f : F) ∈ RL from Submodule.subset_span ⟨f, hf, rfl⟩)
  have hMO : ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), f ∈ V₁.nonunits → (f : F) ∈ O.nonunits := by
    intro f hf
    have hfR : (f : F) ∈ R₀ := Submodule.subset_span ⟨f, hnu_mem f hf, rfl⟩
    have hfI : (⟨(f : F), hfR⟩ : ↥R₀) ∈ I := (hImem _).mpr (Submodule.subset_span ⟨f, hf, rfl⟩)
    exact hIO ⟨⟨(f : F), hfR⟩, hfI, rfl⟩
  have hnot : ∀ x : F, x ≠ 0 → x ∈ O → x⁻¹ ∈ O.nonunits → False := by
    intro x hx0 hx hxi
    rw [ValuationSubring.mem_nonunits_iff] at hxi
    have h2 : O.valuation (x * x⁻¹) < 1 := by
      rw [map_mul]
      calc O.valuation x * O.valuation x⁻¹ ≤ 1 * O.valuation x⁻¹ := by
            gcongr; exact (O.valuation_le_one_iff _).mpr hx
        _ = O.valuation x⁻¹ := one_mul _
        _ < 1 := hxi
    rw [mul_inv_cancel₀ hx0, map_one] at h2
    exact lt_irrefl _ h2
  obtain ⟨f₀, hf₀⟩ : ∃ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), f ∉ V₁ := by
    by_contra h
    push Not at h
    exact hV₁ (eq_top_iff.mpr fun x _ => h x)
  have hcoeinv : ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), ((f⁻¹ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) : F) = ((f : F))⁻¹ := fun f => by push_cast; rfl
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hf₀0 : (f₀ : F) ≠ 0 := fun h => hf₀ (by
      have : f₀ = 0 := Subtype.ext h
      rw [this]; exact V₁.zero_mem)
    refine hnot (f₀ : F) hf₀0 (htop.symm ▸ ValuationSubring.mem_top _) ?_
    rw [← hcoeinv]; exact hMO _ (hnu_inv f₀ hf₀)
  have hPIR : IsPrincipalIdealRing ↥O := hdvr O hLO hOtop
  refine ⟨⟨O, fun x => hLO x, hOtop, hPIR⟩, fun f => ⟨fun hfO => ?_, fun hf => hVO f hf⟩⟩
  by_contra hf
  have hf0 : (f : F) ≠ 0 := fun h => hf (by
    have : f = 0 := Subtype.ext h
    rw [this]; exact V₁.zero_mem)
  refine hnot (f : F) hf0 hfO ?_
  rw [← hcoeinv]; exact hMO _ (hnu_inv f hf)

end S_AlgebraicCurve_Place_exists_forall_mem_iff_adjoin_sup_of_linearDisjoint
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_forall_mem_iff_adjoin_sup_of_linearDisjoint (solution)
