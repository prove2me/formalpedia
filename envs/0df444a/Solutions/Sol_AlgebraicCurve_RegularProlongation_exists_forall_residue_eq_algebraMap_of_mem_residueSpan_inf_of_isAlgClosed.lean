-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4c7699de-7d9a-5aef-85fc-6bbeb26c0549

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_ringKrullDim_lt_top
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq
import Theorems.Thm_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg
import Theorems.Thm_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed
p2m_attr_erase "simp" "ValuationSubring.coe_toResidueValuationSubring"

open Polynomial

universe uL uF

namespace AbhDescSol

section SpanField

variable {L : Type uL} [Field L] {F : Type uF} [Field F] [Algebra L F]

theorem exists_map_eq_of_coeffs_subset {L₁ : Type*} [Field L₁] [Algebra L₁ L] (p : L[X])
    (hp : (↑p.coeffs : Set L) ⊆ Set.range (algebraMap L₁ L)) :
    ∃ q : L₁[X], q.map (algebraMap L₁ L) = p := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  by_cases h : p.coeff n = 0
  · exact ⟨0, by rw [h, map_zero]⟩
  · exact hp (Polynomial.coeff_mem_coeffs h)

theorem aeval_div_aeval_mem_adjoin {L₁ : Type*} [Field L₁] [Algebra L₁ L] [Algebra L₁ F]
    [IsScalarTower L₁ L F] (f : F) (r s : L[X])
    (hr : (↑r.coeffs : Set L) ⊆ Set.range (algebraMap L₁ L))
    (hs : (↑s.coeffs : Set L) ⊆ Set.range (algebraMap L₁ L)) :
    aeval f r / aeval f s ∈ IntermediateField.adjoin L₁ ({f} : Set F) := by
  obtain ⟨r₁, rfl⟩ := exists_map_eq_of_coeffs_subset r hr
  obtain ⟨s₁, rfl⟩ := exists_map_eq_of_coeffs_subset s hs
  rw [aeval_map_algebraMap, aeval_map_algebraMap]
  exact div_mem
    (IntermediateField.algebra_adjoin_le_adjoin L₁ _ (aeval_mem_adjoin_singleton L₁ f))
    (IntermediateField.algebra_adjoin_le_adjoin L₁ _ (aeval_mem_adjoin_singleton L₁ f))

theorem exists_finset_forall_exists_intermediateField (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F] (D : Finset F) :
    ∃ S : Finset L, ∀ (L₁ : Type uL) [Field L₁] [Algebra L₁ L] [Algebra L₁ F]
      [IsScalarTower L₁ L F], (↑S ⊆ Set.range (algebraMap L₁ L)) →
      ∃ (F₁ : IntermediateField L₁ F) (hf₁ : f ∈ F₁), (∀ d ∈ D, d ∈ F₁) ∧
        FiniteDimensional (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ∧
        Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ≤
          Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
  classical
  set K : IntermediateField L F := IntermediateField.adjoin L ({f} : Set F) with hKdef
  set n : ℕ := Module.finrank K F with hndef
  let e : Module.Basis (Fin n) K F := Module.finBasis K F

  have hK : ∀ x : K, ∃ r s : L[X], (x : F) = aeval f r / aeval f s := fun x =>
    (IntermediateField.mem_adjoin_simple_iff L (x : F)).1 x.2
  choose num den hnd using hK
  let cs : K → Finset L := fun x => (num x).coeffs ∪ (den x).coeffs
  let S₁ : Finset L :=
    Finset.univ.biUnion fun t : Fin n × Fin n × Fin n => cs (e.repr (e t.1 * e t.2.1) t.2.2)
  let S₂ : Finset L := Finset.univ.biUnion fun k : Fin n => cs (e.repr 1 k)
  let S₃ : Finset L := D.biUnion fun d => Finset.univ.biUnion fun k : Fin n => cs (e.repr d k)
  refine ⟨S₁ ∪ S₂ ∪ S₃, ?_⟩
  intro L₁ _ _ _ _ hS
  let K₁ : IntermediateField L₁ F := IntermediateField.adjoin L₁ ({f} : Set F)

  have hmemK₁ : ∀ x : K, (↑(cs x) : Set L) ⊆ Set.range (algebraMap L₁ L) → (x : F) ∈ K₁ := by
    intro x hx
    rw [hnd x]
    refine aeval_div_aeval_mem_adjoin f (num x) (den x) (fun a ha => hx ?_) (fun a ha => hx ?_)
    · exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha))
    · exact Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 ha))
  let M : Submodule K₁ F := Submodule.span K₁ (Set.range e)

  have hM_of : ∀ y : F, (∀ k, (↑(cs (e.repr y k)) : Set L) ⊆ Set.range (algebraMap L₁ L)) →
      y ∈ M := by
    intro y hy
    rw [← e.sum_repr y]
    refine Submodule.sum_mem _ fun k _ => ?_
    have : (e.repr y k) • e k = (⟨(e.repr y k : F), hmemK₁ _ (hy k)⟩ : K₁) • e k := by
      rw [IntermediateField.smul_def, IntermediateField.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hS₁ : ∀ a b k, (↑(cs (e.repr (e a * e b) k)) : Set L) ⊆ Set.range (algebraMap L₁ L) := by
    intro a b k x hx
    refine hS (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _ ?_)))
    exact Finset.mem_biUnion.2 ⟨(a, b, k), Finset.mem_univ _, Finset.mem_coe.1 hx⟩
  have hS₂ : ∀ k, (↑(cs (e.repr 1 k)) : Set L) ⊆ Set.range (algebraMap L₁ L) := by
    intro k x hx
    refine hS (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_right _ ?_)))
    exact Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_coe.1 hx⟩
  have hS₃ : ∀ d ∈ D, ∀ k, (↑(cs (e.repr d k)) : Set L) ⊆ Set.range (algebraMap L₁ L) := by
    intro d hd k x hx
    refine hS (Finset.mem_coe.2 (Finset.mem_union_right _ ?_))
    exact Finset.mem_biUnion.2 ⟨d, hd,
      Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_coe.1 hx⟩⟩
  have hmul_e : ∀ a b, e a * e b ∈ M := fun a b => hM_of _ (hS₁ a b)
  have hone : (1 : F) ∈ M := hM_of 1 hS₂
  have hD : ∀ d ∈ D, d ∈ M := fun d hd => hM_of d (hS₃ d hd)

  have hmul_right : ∀ b, ∀ x ∈ M, x * e b ∈ M := by
    intro b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hmul_e a b
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  have hmul : ∀ x y, x ∈ M → y ∈ M → x * y ∈ M := by
    intro x y hx hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact hmul_right b x hx
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  let Malg : Subalgebra K₁ F := M.toSubalgebra hone hmul
  have hfg : (Subalgebra.toSubmodule Malg).FG := by
    rw [Submodule.toSubalgebra_toSubmodule]
    exact Submodule.fg_span (Set.finite_range e)
  have hint : ∀ x ∈ Malg, IsIntegral K₁ x := fun x hx => IsIntegral.of_mem_of_fg Malg hfg x hx
  let F₁' : IntermediateField K₁ F := Malg.toIntermediateField fun x hx =>
    Malg.inv_mem_of_algebraic (x := ⟨x, hx⟩) (hint x hx).isAlgebraic
  let F₁ : IntermediateField L₁ F := F₁'.restrictScalars L₁
  have hmemF₁ : ∀ x, x ∈ F₁ ↔ x ∈ M := fun x => Iff.rfl
  have hK₁F₁ : ∀ c : K₁, (c : F) ∈ F₁ := fun c => by
    have h := Submodule.smul_mem M c hone
    rw [IntermediateField.smul_def, smul_eq_mul, mul_one] at h
    exact (hmemF₁ _).2 h
  have hf₁ : f ∈ F₁ := hK₁F₁ ⟨f, IntermediateField.mem_adjoin_simple_self L₁ f⟩
  refine ⟨F₁, hf₁, fun d hd => (hmemF₁ d).2 (hD d hd), ?_⟩

  set f₁ : F₁ := ⟨f, hf₁⟩ with hf₁def
  set E : IntermediateField L₁ F₁ := IntermediateField.adjoin L₁ ({f₁} : Set F₁) with hEdef
  let e₁ : Fin n → F₁ := fun k => ⟨e k, (hmemF₁ _).2 (Submodule.subset_span ⟨k, rfl⟩)⟩
  have hspan : Submodule.span E (Set.range e₁) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K₁).1 ((hmemF₁ x).1 x.2)
    have hcE : ∀ k, ∃ z : E, ((z : F₁) : F) = c k := by
      intro k
      have h1 : (c k : F) ∈ IntermediateField.lift E := by
        rw [hEdef, IntermediateField.lift_adjoin_simple]; exact (c k).2
      have h2 : (⟨(c k : F), hK₁F₁ (c k)⟩ : F₁) ∈ E := (IntermediateField.mem_lift _).1 h1
      exact ⟨⟨_, h2⟩, rfl⟩
    choose z hz using hcE
    have hx : x = ∑ k, z k • e₁ k := by
      apply Subtype.val_injective
      change (x : F) = ((∑ k, z k • e₁ k : F₁) : F)
      rw [← hc, IntermediateField.coe_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : ((z k • e₁ k : F₁) : F) = (c k : F) * e k := by
        rw [IntermediateField.smul_def, smul_eq_mul, IntermediateField.coe_mul, hz k]
      rw [h1, IntermediateField.smul_def, smul_eq_mul]
    rw [hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨Module.finite_def.2 (hspan ▸ Submodule.fg_span (Set.finite_range e₁)), ?_⟩
  calc Module.finrank E F₁ ≤ Fintype.card (Fin n) := finrank_le_of_span_eq_top hspan
    _ = n := Fintype.card_fin n

end SpanField

section TDesc

variable {L : Type uL} [Field L] {F : Type uF} [Field F] [Algebra L F]

theorem exists_monic_relation (g u : F)
    (hu : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) :
    ∃ (m : ℕ) (q : Fin m → L[X]), u ^ m + ∑ k : Fin m, aeval g (q k) * u ^ (k : ℕ) = 0 := by
  classical
  set s : Set F := Set.range (algebraMap L F) ∪ {g} with hs
  have hmem : u ∈ (⨅ V : {V : ValuationSubring F // s ⊆ V.toSubring}, V.1.toSubring) := by
    refine Subring.mem_iInf.2 fun V => ?_
    have hV : ∀ a : L, algebraMap L F a ∈ V.1 := fun a => V.2 (Set.mem_union_left _ ⟨a, rfl⟩)
    exact hu V.1 hV (V.2 (Set.mem_union_right _ (Set.mem_singleton g)))
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral (Subring.closure s) u := hmem
  obtain ⟨p, hp, hpu⟩ := hint
  have hcl : Subring.closure s = (Algebra.adjoin L ({g} : Set F)).toSubring := by
    rw [Algebra.adjoin_eq_ring_closure]
  have hcoef : ∀ k, ∃ q : L[X], ((p.coeff k : Subring.closure s) : F) = aeval g q := by
    intro k
    have h1 : ((p.coeff k : Subring.closure s) : F) ∈
        (Algebra.adjoin L ({g} : Set F)).toSubring := by
      rw [← hcl]; exact (p.coeff k).2
    rw [Subalgebra.mem_toSubring, Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨q, hq⟩ := h1
    exact ⟨q, hq.symm⟩
  choose q hq using hcoef
  refine ⟨p.natDegree, fun k => q k, ?_⟩
  have hsum : ∑ k : Fin p.natDegree, aeval g (q k) * u ^ (k : ℕ)
      = ∑ k ∈ Finset.range p.natDegree,
          (algebraMap (Subring.closure s) F) (p.coeff k) * u ^ k := by
    rw [← Finset.sum_range fun k => aeval g (q k) * u ^ k]
    exact Finset.sum_congr rfl fun k _ => by rw [← hq k]; rfl
  rw [hsum, add_comm]
  have h := hpu
  rwa [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at h

theorem mem_of_monic_relation {K : Type*} [Field K] (V : ValuationSubring K) (u : K) (m : ℕ)
    (c : Fin m → K) (hc : ∀ k, c k ∈ V)
    (h : u ^ m + ∑ k : Fin m, c k * u ^ (k : ℕ) = 0) : u ∈ V := by
  by_contra hu
  have hu0 : u ≠ 0 := by rintro rfl; exact hu V.zero_mem
  have hlt : V.valuation u⁻¹ < 1 := by
    have hgt : 1 < V.valuation u := lt_of_not_ge fun h' => hu ((V.valuation_le_one_iff u).1 h')
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hgt

  have hpow : ∀ a b : ℕ, u ^ a * u⁻¹ ^ (a + b) = u⁻¹ ^ b := fun a b => by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, one_mul]
  have key : (1 : K) + ∑ k : Fin m, c k * (u⁻¹) ^ (m - k) = 0 := by
    have h2 := congrArg (fun x => x * (u⁻¹) ^ m) h
    simp only [zero_mul, add_mul, Finset.sum_mul] at h2
    rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow] at h2
    rw [← h2]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (k : ℕ) + (m - k) = m := Nat.add_sub_cancel' k.2.le
    rw [mul_assoc]
    congr 1
    have h3 := hpow k (m - k)
    rw [hk] at h3
    exact h3.symm
  have hval : V.valuation (∑ k : Fin m, c k * (u⁻¹) ^ (m - k)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    rw [map_mul, map_pow]
    have hpos : 0 < m - k := Nat.sub_pos_of_lt k.2
    calc V.valuation (c k) * V.valuation u⁻¹ ^ (m - (k : ℕ))
        ≤ 1 * V.valuation u⁻¹ ^ (m - (k : ℕ)) := by
          gcongr
          exact (V.valuation_le_one_iff _).2 (hc k)
      _ < 1 := by
          rw [one_mul]
          exact pow_lt_one₀ zero_le' hlt hpos.ne'
  have hone : V.valuation (1 : K) < 1 := by
    have h1 : (1 : K) = -∑ k : Fin m, c k * (u⁻¹) ^ (m - k) := eq_neg_of_add_eq_zero_left key
    rw [h1, Valuation.map_neg]
    exact hval
  rw [map_one] at hone
  exact lt_irrefl _ hone

theorem exists_finset_forall_mem_valuationSubring (g u : F)
    (hu : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) :
    ∃ S : Finset L, ∀ (L₁ : Type uL) [Field L₁] [Algebra L₁ L] [Algebra L₁ F]
      [IsScalarTower L₁ L F], (↑S ⊆ Set.range (algebraMap L₁ L)) →
      ∀ (F₁ : IntermediateField L₁ F) (hg₁ : g ∈ F₁) (hu₁ : u ∈ F₁) (V : ValuationSubring F₁),
        (∀ a : L₁, algebraMap L₁ F₁ a ∈ V) → (⟨g, hg₁⟩ : F₁) ∈ V → (⟨u, hu₁⟩ : F₁) ∈ V := by
  classical
  obtain ⟨m, q, hrel⟩ := exists_monic_relation g u hu
  refine ⟨Finset.univ.biUnion fun k => (q k).coeffs, ?_⟩
  intro L₁ _ _ _ _ hS F₁ hg₁ hu₁ V hVL hVg
  have hq : ∀ k, ∃ q₁ : L₁[X], q₁.map (algebraMap L₁ L) = q k := fun k =>
    exists_map_eq_of_coeffs_subset (q k) fun x hx => hS (Finset.mem_coe.2
      (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_coe.1 hx⟩))
  choose q₁ hq₁ using hq
  set g₁ : F₁ := ⟨g, hg₁⟩ with hg₁def
  set u₁ : F₁ := ⟨u, hu₁⟩ with hu₁def

  let c : Fin m → F₁ := fun k => aeval g₁ (q₁ k)
  have hc : ∀ k, c k ∈ V := by
    intro k
    let V' : Subalgebra L₁ F₁ :=
      { V.toSubring with
        algebraMap_mem' := hVL }
    have hle : Algebra.adjoin L₁ ({g₁} : Set F₁) ≤ V' :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hVg)
    exact hle (aeval_mem_adjoin_singleton L₁ g₁)
  have hcoe : ∀ k, ((c k : F₁) : F) = aeval g (q k) := by
    intro k
    change ((aeval g₁ (q₁ k) : F₁) : F) = aeval g (q k)
    rw [← IntermediateField.aeval_coe, ← hq₁ k, aeval_map_algebraMap]
  have hrel₁ : u₁ ^ m + ∑ k : Fin m, c k * u₁ ^ (k : ℕ) = 0 := by
    apply Subtype.val_injective
    change ((u₁ ^ m + ∑ k : Fin m, c k * u₁ ^ (k : ℕ) : F₁) : F) = ((0 : F₁) : F)
    rw [IntermediateField.coe_add, IntermediateField.coe_pow, IntermediateField.coe_sum,
      ZeroMemClass.coe_zero, ← hrel]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, hcoe k]
  exact mem_of_monic_relation V u₁ m c hc hrel₁

end TDesc

section Constants

variable {L : Type uL} [Field L]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem trdeg_adjoin_lt_aleph0 (P : Type*) [Field P] [Algebra P L] (S : Finset L) :
    Algebra.trdeg P (IntermediateField.adjoin P (↑S : Set L)) < Cardinal.aleph0 := by
  haveI : Algebra.FiniteType P (Algebra.adjoin P (↑S : Set L)) :=
    Algebra.FiniteType.adjoin_of_finite S.finite_toSet
  haveI : FaithfulSMul P (Algebra.adjoin P (↑S : Set L)) :=
    (faithfulSMul_iff_algebraMap_injective P _).2 (algebraMap P _).injective
  have h := trdeg_add_eq P (Algebra.adjoin P (↑S : Set L))
    (A := IntermediateField.adjoin P (↑S : Set L))
  rw [trdeg_eq_zero (R := Algebra.adjoin P (↑S : Set L)), add_zero] at h
  rw [← h]
  exact trdeg_lt_aleph0_of_finiteType

theorem ringKrullDim_le_one_of_finite (P : Type*) [Field P] [Finite P] (B : ValuationSubring P) :
    ringKrullDim B ≤ 1 := by
  haveI : Finite B := Finite.of_injective (fun b : B => (b : P)) Subtype.val_injective
  haveI : IsArtinianRing B := isArtinian_of_finite
  haveI : Ring.KrullDimLE 0 B := Ring.KrullDimLE.mk₀ fun I hI => by
    haveI := hI
    infer_instance
  have h := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 B)
  exact_mod_cast h

theorem ringKrullDim_le_one_rat (B : ValuationSubring ℚ) : ringKrullDim B ≤ 1 := by
  have h := ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one B
  rwa [trdeg_eq_zero (R := ℚ) (A := ℚ), map_zero, WithBot.coe_zero, zero_add] at h

theorem ringKrullDim_comap_lt_top (P : Type*) [Field P] [Algebra P L]
    (hP : ∀ B : ValuationSubring P, ringKrullDim B ≤ 1)
    (K₀ : IntermediateField P L)
    (hK₀ : Algebra.trdeg P K₀ < Cardinal.aleph0)
    (E : IntermediateField K₀ L) [Algebra.IsAlgebraic K₀ E] (A : ValuationSubring L) :
    ringKrullDim (A.comap (algebraMap E L)) < ⊤ := by
  set A₁ := A.comap (algebraMap E L) with hA₁
  have h1 := ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg (K := K₀) A₁
  rw [trdeg_eq_zero (R := K₀) (A := E), map_zero, WithBot.coe_zero, add_zero] at h1
  have h2' := ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg (K := P)
    (A₁.comap (algebraMap K₀ E))
  have h3 := hP ((A₁.comap (algebraMap K₀ E)).comap (algebraMap P K₀))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Cardinal.toENat (Algebra.trdeg P K₀) = n := by
    have : Cardinal.toENat (Algebra.trdeg P K₀) ≠ ⊤ := by
      rw [Ne, Cardinal.toENat_eq_top]; exact not_le.2 hK₀
    exact ENat.ne_top_iff_exists.1 this |>.imp fun n h => h.symm
  rw [hn] at h2'
  have h2 : ringKrullDim (A₁.comap (algebraMap K₀ E)) ≤ ((n + 1 : ℕ) : ℕ∞) := by
    refine h2'.trans ?_
    calc ringKrullDim ((A₁.comap (algebraMap K₀ E)).comap (algebraMap P K₀)) + ((n : ℕ∞) : WithBot ℕ∞)
        ≤ (1 : WithBot ℕ∞) + ((n : ℕ∞) : WithBot ℕ∞) := add_le_add h3 le_rfl
      _ = ((n + 1 : ℕ) : ℕ∞) := by
          rw [add_comm]; push_cast; rfl
  refine lt_of_le_of_lt (h1.trans h2) ?_
  exact WithBot.coe_lt_coe.2 (ENat.coe_lt_top _)

end Constants

section Assembly

open AlgebraicCurve IsLocalRing

variable {L : Type uL} [Field L] {A : ValuationSubring L}
variable {F : Type uF} [Field F] [Algebra L F]

theorem exists_of_mem_span {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)] (R : ∀ i, RegularProlongation A F (Fb i))
    (P : F → Prop) (hP0 : P 0) (hPadd : ∀ x y, P x → P y → P (x + y))
    (hPmul : ∀ (a : L) (x : F), P x → P (algebraMap L F a * x))
    (g : ∀ i, Fb i) (hg : g ∈ Submodule.span (ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        P u ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers, P u ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = g i := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, fun i => zero_mem _, hP0, fun i => by
      rw [show (⟨(0 : F), zero_mem _⟩ : (R i).integers) = 0 from rfl, map_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, hPu, hru⟩ := hx
    obtain ⟨u', hu', hPu', hru'⟩ := hy
    exact ⟨u + u', fun i => add_mem (hu i) (hu' i), hPadd _ _ hPu hPu', fun i => by
      rw [Pi.add_apply, ← hru i, ← hru' i, ← map_add]; rfl⟩
  | smul a x _ hx =>
    obtain ⟨u, hu, hPu, hru⟩ := hx
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    refine ⟨algebraMap L F b * u,
      fun i => mul_mem (((R i).algebraMap_mem_iff b).2 b.2) (hu i), hPmul b u hPu, fun i => ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← hru i, ← (R i).residue_algebraMap b, ← map_mul]
    rfl

theorem exists_not_mem_iff {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)] (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers) {i j : ι} (hij : i ≠ j) :
    ∃ x : F, ¬ (x ∈ (R i).integers ↔ x ∈ (R j).integers) := by
  by_contra h
  exact hij (hR (SetLike.ext fun x => not_not.mp (not_exists.mp h x)))

theorem exists_residue_linearIndependent {Fbar : Type*} [Field Fbar]
    [Algebra (ResidueField A) Fbar] (R : RegularProlongation A F Fbar) (x : R.integers) :
    ∃ (b : Fin (Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({R.residue x} : Set Fbar)) Fbar) → F) (hb : ∀ l, b l ∈ R.integers),
      LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
        (fun l => R.residue ⟨b l, hb l⟩) := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
    (le_refl (Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({R.residue x} : Set Fbar)) Fbar))
  choose w hw using fun l => R.residue_surjective (v l)
  refine ⟨fun l => (w l : F), fun l => (w l).2, ?_⟩
  convert hv using 1
  funext l
  rw [← hw l]

variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

theorem main [IsAlgClosed L] (P : Type*) [Field P] [Algebra P L]
    (hP : ∀ B : ValuationSubring P, ringKrullDim B ≤ 1)
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (h : ∀ i, Fb i)
    (hT : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i})
    (hT' : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    ∃ c : IsLocalRing.ResidueField A,
      ∀ i, h i = algebraMap (IsLocalRing.ResidueField A) (Fb i) c := by
  classical

  obtain ⟨u, hu, hTu, hru⟩ := exists_of_mem_span R
    (fun u => ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V)
    (fun V _ _ => zero_mem V) (fun x y hx hy V hV hfV => add_mem (hx V hV hfV) (hy V hV hfV))
    (fun a x hx V hV hfV => mul_mem (hV a) (hx V hV hfV)) h hT
  obtain ⟨u', hu', hTu', hru'⟩ := exists_of_mem_span R
    (fun u => ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V)
    (fun V _ _ => zero_mem V) (fun x y hx hy V hV hfV => add_mem (hx V hV hfV) (hy V hV hfV))
    (fun a x hx V hV hfV => mul_mem (hV a) (hx V hV hfV)) h hT'

  have hsep0 : ∀ p : {p : ι × ι // p.1 ≠ p.2},
      ∃ x : F, ¬ (x ∈ (R p.1.1).integers ↔ x ∈ (R p.1.2).integers) := fun p =>
    exists_not_mem_iff R hR p.2
  choose sep hsep using hsep0
  have hbas0 := fun i => exists_residue_linearIndependent (R i) ⟨f, hf i⟩
  choose b hb hbli using hbas0
  let D : Finset F := insert u (insert u'
    ((Finset.univ.image sep) ∪ Finset.univ.biUnion fun i => Finset.univ.image (b i)))
  have huD : u ∈ D := Finset.mem_insert_self _ _
  have hu'D : u' ∈ D := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hsepD : ∀ p, sep p ∈ D := fun p =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ p))))
  have hbD : ∀ i l, b i l ∈ D := fun i l =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩)))

  haveI := hfd
  obtain ⟨S₁, hS₁⟩ := exists_finset_forall_exists_intermediateField (L := L) f D
  obtain ⟨S₂, hS₂⟩ := exists_finset_forall_mem_valuationSubring (L := L) f u hTu
  obtain ⟨S₃, hS₃⟩ := exists_finset_forall_mem_valuationSubring (L := L) f⁻¹ u' hTu'

  set K₀ : IntermediateField P L := IntermediateField.adjoin P (↑(S₁ ∪ S₂ ∪ S₃) : Set L)
    with hK₀
  set E₁ : IntermediateField K₀ L := algebraicClosure K₀ L with hE₁
  haveI : IsAlgClosed E₁ := IsAlgClosure.isAlgClosed K₀
  have hrange : (↑(S₁ ∪ S₂ ∪ S₃) : Set L) ⊆ Set.range (algebraMap E₁ L) := by
    intro s hs
    have h1 : s ∈ K₀ := IntermediateField.subset_adjoin P _ hs
    exact ⟨⟨s, E₁.algebraMap_mem ⟨s, h1⟩⟩, rfl⟩
  have hr₁ : (↑S₁ : Set L) ⊆ Set.range (algebraMap E₁ L) := fun s hs =>
    hrange (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_coe.1 hs))))
  have hr₂ : (↑S₂ : Set L) ⊆ Set.range (algebraMap E₁ L) := fun s hs =>
    hrange (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_coe.1 hs))))
  have hr₃ : (↑S₃ : Set L) ⊆ Set.range (algebraMap E₁ L) := fun s hs =>
    hrange (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hs)))

  obtain ⟨F₁, hf₁, hDF₁, hfd₁, hdeg⟩ := hS₁ E₁ hr₁
  have huF₁ : u ∈ F₁ := hDF₁ u huD
  have hu'F₁ : u' ∈ F₁ := hDF₁ u' hu'D

  obtain ⟨Fb₁, _instF, _instA, R₁, φ, hO, hR₁, hφres, hφalg, htrL₁, htr₁, heq₁, -⟩ :=
    AlgebraicCurve.RegularProlongation.exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq
      A Fb R f hf htr heq F₁ hf₁ hfd₁ hdeg
      (fun i j hij => ⟨sep ⟨(i, j), hij⟩, hDF₁ _ (hsepD _), hsep ⟨(i, j), hij⟩⟩)
      (fun i => ⟨b i, hb i, fun l => hDF₁ _ (hbD i l), hbli i⟩)

  have hA₁ : ringKrullDim (A.comap (algebraMap E₁ L)) < ⊤ :=
    ringKrullDim_comap_lt_top P hP K₀ (trdeg_adjoin_lt_aleph0 P _) E₁ A

  set f₁ : F₁ := ⟨f, hf₁⟩ with hf₁def
  have hf₁' : ∀ i, f₁ ∈ (R₁ i).integers := fun i => (hO i _).mpr (hf i)
  set u₁ : F₁ := ⟨u, huF₁⟩ with hu₁def
  set u₁' : F₁ := ⟨u', hu'F₁⟩ with hu₁'def
  have hu₁ : ∀ i, u₁ ∈ (R₁ i).integers := fun i => (hO i _).mpr (hu i)
  have hu₁' : ∀ i, u₁' ∈ (R₁ i).integers := fun i => (hO i _).mpr (hu' i)
  let h₁ : ∀ i, Fb₁ i := fun i => (R₁ i).residue ⟨u₁, hu₁ i⟩
  have hφh : ∀ i, φ i (h₁ i) = h i := fun i => by
    rw [← hru i]
    exact hφres i u₁ (hu i)
  have hφh' : ∀ i, (R₁ i).residue ⟨u₁', hu₁' i⟩ = h₁ i := fun i => by
    apply (φ i).injective
    rw [hφh i, hφres i u₁' (hu' i), ← hru' i]
  have hT₁ : h₁ ∈ Submodule.span (ResidueField (A.comap (algebraMap E₁ L)))
      {h : ∀ i, Fb₁ i | ∃ v : F₁, ∃ hv : ∀ i, v ∈ (R₁ i).integers,
        (∀ V : ValuationSubring F₁, (∀ a : E₁, algebraMap E₁ F₁ a ∈ V) → f₁ ∈ V → v ∈ V) ∧
        ∀ i, (R₁ i).residue ⟨v, hv i⟩ = h i} :=
    Submodule.subset_span ⟨u₁, hu₁,
      fun V hV hfV => hS₂ E₁ hr₂ F₁ hf₁ huF₁ V hV hfV, fun i => rfl⟩
  have hinvf₁ : f₁⁻¹ = ⟨f⁻¹, inv_mem hf₁⟩ := rfl
  have hT₁' : h₁ ∈ Submodule.span (ResidueField (A.comap (algebraMap E₁ L)))
      {h : ∀ i, Fb₁ i | ∃ v : F₁, ∃ hv : ∀ i, v ∈ (R₁ i).integers,
        (∀ V : ValuationSubring F₁, (∀ a : E₁, algebraMap E₁ F₁ a ∈ V) → f₁⁻¹ ∈ V → v ∈ V) ∧
        ∀ i, (R₁ i).residue ⟨v, hv i⟩ = h i} :=
    Submodule.subset_span ⟨u₁', hu₁',
      fun V hV hfV => hS₃ E₁ hr₃ F₁ (inv_mem hf₁) hu'F₁ V hV (hinvf₁ ▸ hfV), fun i => hφh' i⟩

  obtain ⟨c₁, hc₁⟩ :=
    AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_ringKrullDim_lt_top
      (A.comap (algebraMap E₁ L)) hA₁ Fb₁ R₁ hR₁ f₁ hf₁' htrL₁ hfd₁ htr₁ heq₁ h₁ hT₁ hT₁'

  obtain ⟨a₁, rfl⟩ := IsLocalRing.residue_surjective c₁
  refine ⟨IsLocalRing.residue A ⟨algebraMap E₁ L a₁, ValuationSubring.mem_comap.mp a₁.2⟩,
    fun i => ?_⟩
  rw [← hφh i, hc₁ i, hφalg i a₁]

end Assembly

end AbhDescSol

open AlgebraicCurve

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (h : ∀ i, Fb i)
    (hT : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i})
    (hT' : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    ∃ c : IsLocalRing.ResidueField A, ∀ i, h i = algebraMap (IsLocalRing.ResidueField A) (Fb i) c := by
  have _ := htrL

  obtain ⟨p, hp⟩ := CharP.exists L
  rcases CharP.char_is_prime_or_zero L p with hprime | h0
  · haveI : Fact p.Prime := ⟨hprime⟩
    letI : Algebra (ZMod p) L := ZMod.algebra L p
    exact AbhDescSol.main (ZMod p) (AbhDescSol.ringKrullDim_le_one_of_finite (ZMod p))
      R hR f hf hfd htr heq h hT hT'
  · subst h0
    haveI : CharZero L := CharP.charP_to_charZero L
    exact AbhDescSol.main ℚ AbhDescSol.ringKrullDim_le_one_rat R hR f hf hfd htr heq h hT hT'

end S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed (solution)
