-- Prove2me | solution 1 for AlgebraicCurve.Place.existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/df6f41e0-d94c-5823-9535-a040a481b8c2

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem

set_option autoImplicit false
open IsLocalRing AlgebraicCurve

namespace KFRatLayer

theorem isUnit_iff_inv_mem {L : Type*} [Field L] (B : ValuationSubring L) (x : B)
    (hx0 : (x : L) ≠ 0) : IsUnit x ↔ (x : L)⁻¹ ∈ B := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hx.exists_left_inv
    have hyx : (y : L) * (x : L) = 1 := by
      have := congrArg (Subtype.val) hy
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left hyx]
    exact y.2
  · exact isUnit_iff_exists_inv.mpr ⟨⟨_, hx⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem mem_maximalIdeal_iff_inv_not_mem {L : Type*} [Field L] (B : ValuationSubring L) (x : B)
    (hx0 : (x : L) ≠ 0) : x ∈ maximalIdeal B ↔ (x : L)⁻¹ ∉ B := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, isUnit_iff_inv_mem B x hx0]

end KFRatLayer

namespace BDescRatExt

noncomputable def algOver {K E : Type} [Field K] [Field E] [Algebra K E] (V : ValuationSubring K)
    (W : ValuationSubring E) (hW : ∀ x : K, algebraMap K E x ∈ W ↔ x ∈ V) : Algebra ↥V ↥W :=
  (((algebraMap K E).comp V.subtype).codRestrict W fun a => (hW a).mpr a.2).toAlgebra

theorem layer_count {K E : Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] [CharZero K]
    (V : ValuationSubring K) [IsDiscreteValuationRing ↥V]
    {n : ℕ} (hn : Module.finrank K E ≤ n)
    (hf : ∀ (W : ValuationSubring E) (hW : ∀ x : K, algebraMap K E x ∈ W ↔ x ∈ V), IsDiscreteValuationRing ↥W →
      letI : Algebra ↥V ↥W := algOver V W hW
      n ≤ (maximalIdeal ↥V).inertiaDeg' (maximalIdeal ↥W)) :
    ∃ W : ValuationSubring E, ∃ hW : (∀ x : K, algebraMap K E x ∈ W ↔ x ∈ V),
      (∀ W' : ValuationSubring E, (∀ x : K, algebraMap K E x ∈ W' ↔ x ∈ V) → W' = W) ∧
      IsDiscreteValuationRing ↥W ∧
      (letI : Algebra ↥V ↥W := algOver V W hW
       (maximalIdeal ↥V).ramificationIdx' (maximalIdeal ↥W) = 1 ∧ (maximalIdeal ↥V).inertiaDeg' (maximalIdeal ↥W) = n) ∧
      Module.finrank K E = n := by
  classical
  haveI : IsScalarTower ↥V K E := IsScalarTower.of_algebraMap_eq (fun (x : ↥V) => rfl)
  haveI : Module.Finite ↥V ↥(integralClosure ↥V E) := IsIntegralClosure.finite ↥V K E ↥(integralClosure ↥V E)
  obtain ⟨hfin, hdvr, hsum⟩ := ValuationSubring.finsum_ramificationIdx_mul_inertiaDeg_eq_finrank (K := K) (F := E) V

  set T : Type := {B : ValuationSubring E // ∀ x : K, algebraMap K E x ∈ B ↔ x ∈ V} with hT
  haveI : Finite T := hfin.to_subtype
  haveI : Fintype T := Fintype.ofFinite T
  let ef : T → ℕ := fun B =>
    letI : Algebra ↥V ↥B.1 := algOver V B.1 B.2
    (maximalIdeal ↥V).ramificationIdx' (maximalIdeal ↥B.1) * (maximalIdeal ↥V).inertiaDeg' (maximalIdeal ↥B.1)
  have hsum' : ∑ B : T, ef B = Module.finrank K E := by
    rw [← hsum, finsum_eq_sum_of_fintype]
    rfl
  have hpos : 0 < Module.finrank K E := Module.finrank_pos

  have he : ∀ B : T, letI : Algebra ↥V ↥B.1 := algOver V B.1 B.2
      1 ≤ (maximalIdeal ↥V).ramificationIdx' (maximalIdeal ↥B.1) := by
    intro B
    letI alg : Algebra ↥V ↥B.1 := algOver V B.1 B.2
    haveI := hdvr B.1 B.2
    have halg : ∀ a : ↥V, ((algebraMap ↥V ↥B.1 a : ↥B.1) : E) = algebraMap K E (a : K) := fun a => rfl
    haveI : Module.IsTorsionFree ↥V ↥B.1 := by
      rw [Module.isTorsionFree_iff_smul_eq_zero]
      intro r m h
      rw [Algebra.smul_def, mul_eq_zero] at h
      rcases h with h | h
      · left
        have : ((algebraMap ↥V ↥B.1 r : ↥B.1) : E) = 0 := by rw [h]; rfl
        rw [halg, map_eq_zero] at this
        exact Subtype.ext this
      · exact Or.inr h
    have hunder : (maximalIdeal ↥B.1).under ↥V = maximalIdeal ↥V := by
      ext a
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
      constructor
      · intro h hu; exact h (hu.map _)
      · intro h hu
        apply h

        have ha0 : (a : K) ≠ 0 := by
          intro h0
          have : a = 0 := Subtype.ext h0
          rw [this, map_zero] at hu; exact not_isUnit_zero hu
        have hinvW : algebraMap K E ((a : K)⁻¹) ∈ B.1 := by
          rw [map_inv₀, ← halg]
          obtain ⟨u, hu'⟩ := hu
          have h1 : (((u⁻¹ : (↥B.1)ˣ) : ↥B.1) : E) * ((u : ↥B.1) : E) = 1 :=
            congrArg Subtype.val u.inv_mul
          have h2 : (((u⁻¹ : (↥B.1)ˣ) : ↥B.1) : E) = (((u : ↥B.1)) : E)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [← hu', ← h2]; exact SetLike.coe_mem _
        have hinvV : (a : K)⁻¹ ∈ V := (B.2 _).mp hinvW
        exact ⟨⟨a, ⟨_, hinvV⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩
    haveI : (maximalIdeal ↥B.1).LiesOver (maximalIdeal ↥V) := ⟨hunder.symm⟩
    exact Nat.one_le_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (maximalIdeal ↥B.1)
        (IsDiscreteValuationRing.not_a_field ↥V))
  have hterm : ∀ B : T, n ≤ ef B := by
    intro B
    have h1 := he B
    have h2 := hf B.1 B.2 (hdvr B.1 B.2)
    show n ≤ _ * _
    calc n ≤ 1 * n := by omega
      _ ≤ _ := Nat.mul_le_mul h1 h2

  have hcard : Fintype.card T = 1 := by
    have hle : Fintype.card T * n ≤ Module.finrank K E := by
      rw [← hsum']
      have : ∑ _B : T, n = Fintype.card T * n := by simp
      rw [← this]
      exact Finset.sum_le_sum fun B _ => hterm B
    have hn1 : 1 ≤ n := le_trans hpos hn
    rcases Nat.lt_or_ge (Fintype.card T) 2 with hlt | hge
    · rcases Nat.lt_or_ge (Fintype.card T) 1 with h0 | h1
      · exfalso
        have : Fintype.card T = 0 := by omega
        rw [Fintype.card_eq_zero_iff] at this
        rw [Finset.sum_eq_zero (fun B _ => (this.elim B : ef B = 0))] at hsum'
        omega
      · omega
    · exfalso
      have : 2 * n ≤ Module.finrank K E := le_trans (Nat.mul_le_mul_right n hge) hle
      omega
  obtain ⟨B₀, hB₀⟩ := Fintype.card_eq_one_iff.mp hcard
  have hsum1 : ef B₀ = Module.finrank K E := by
    rw [← hsum', Finset.sum_eq_single_of_mem B₀ (Finset.mem_univ _) (fun B _ hB => absurd (hB₀ B) hB)]
  refine ⟨B₀.1, B₀.2, fun W' hW' => ?_, hdvr B₀.1 B₀.2, ?_, ?_⟩
  · have := hB₀ ⟨W', hW'⟩
    exact congrArg Subtype.val this
  · have h1 := he B₀
    have h2 := hf B₀.1 B₀.2 (hdvr B₀.1 B₀.2)
    have h3 : ef B₀ ≤ n := by rw [hsum1]; exact hn
    change _ * _ ≤ n at h3
    constructor
    · nlinarith
    · nlinarith
  · have h3 : ef B₀ ≤ n := by rw [hsum1]; exact hn
    have h4 := hterm B₀
    omega

theorem le_inertiaDeg {k₀ K E : Type} [Field k₀] [Field K] [Field E] [Algebra k₀ K] [Algebra k₀ E] [Algebra K E]
    [IsScalarTower k₀ K E] [FiniteDimensional K E]
    (W : ValuationSubring E) [IsDiscreteValuationRing ↥W] (hk₀W : ∀ a : k₀, algebraMap k₀ E a ∈ W)
    [IsDiscreteValuationRing ↥(W.comap (algebraMap K E))]
    {n : ℕ} (b : Fin n → E) (hbW : ∀ i, b i ∈ W)
    (hind : ∀ c : Fin n → ↥(W.comap (algebraMap K E)),
      (⟨∑ i, algebraMap K E (c i : K) * b i, sum_mem fun i _ => mul_mem ((ValuationSubring.mem_comap).mp (c i).2) (hbW i)⟩ : ↥W)
        ∈ maximalIdeal ↥W → ∀ i, c i ∈ maximalIdeal ↥(W.comap (algebraMap K E))) :
    letI : Algebra ↥(W.comap (algebraMap K E)) ↥W := algOver (W.comap (algebraMap K E)) W (fun x => (ValuationSubring.mem_comap).symm)
    n ≤ (maximalIdeal ↥(W.comap (algebraMap K E))).inertiaDeg' (maximalIdeal ↥W) := by
  classical
  set V := W.comap (algebraMap K E) with hV
  letI alg : Algebra ↥V ↥W := algOver V W (fun x => (ValuationSubring.mem_comap).symm)

  have hWtop : W ≠ ⊤ := by
    intro h
    apply IsDiscreteValuationRing.not_a_field ↥W

    rw [eq_bot_iff]
    intro x hx
    by_contra hx0
    have hx0' : (x : E) ≠ 0 := fun h0 => hx0 (by exact_mod_cast h0)
    have hinv : (x : E)⁻¹ ∈ W := by
      have : ((x : E)⁻¹) ∈ (⊤ : ValuationSubring E) := trivial
      exact h.symm ▸ this
    exact (IsLocalRing.mem_maximalIdeal _).mp hx ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0'), Subtype.ext (inv_mul_cancel₀ hx0')⟩, rfl⟩
  obtain ⟨w, hwW⟩ : ∃ w : Place k₀ E, w.toValuationSubring = W :=
    ⟨{ toValuationSubring := W, algebraMap_mem' := hk₀W, ne_top' := hWtop, isPrincipalIdealRing' := inferInstance }, rfl⟩
  subst hwW
  have hwr : (w.restrict K).toValuationSubring = V := rfl
  haveI : Algebra.IsIntegral K E := inferInstance
  have hpos := AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional (F := K) w
  have hfin' : Module.Finite (w.restrict K).ResidueField w.ResidueField := FiniteDimensional.of_finrank_pos hpos

  have hunder : (maximalIdeal ↥w.toValuationSubring).under ↥V = maximalIdeal ↥V := by
    ext a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    have halg : ((algebraMap ↥V ↥w.toValuationSubring a : ↥w.toValuationSubring) : E) = algebraMap K E (a : K) := rfl
    constructor
    · intro h hu; exact h (hu.map _)
    · intro h hu
      apply h
      have ha0 : (a : K) ≠ 0 := by
        intro h0
        have : a = 0 := Subtype.ext h0
        rw [this, map_zero] at hu; exact not_isUnit_zero hu
      have hinvW : algebraMap K E ((a : K)⁻¹) ∈ w.toValuationSubring := by
        rw [map_inv₀, ← halg]
        obtain ⟨u, hu'⟩ := hu
        have h1 : (((u⁻¹ : (↥w.toValuationSubring)ˣ) : ↥w.toValuationSubring) : E) * ((u : ↥w.toValuationSubring) : E) = 1 := congrArg Subtype.val u.inv_mul
        have h2 : (((u⁻¹ : (↥w.toValuationSubring)ˣ) : ↥w.toValuationSubring) : E) = (((u : ↥w.toValuationSubring)) : E)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [← hu', ← h2]; exact SetLike.coe_mem _
      have hinvV : (a : K)⁻¹ ∈ V := (ValuationSubring.mem_comap).mpr hinvW
      exact ⟨⟨a, ⟨_, hinvV⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩
  haveI hlies : (maximalIdeal ↥w.toValuationSubring).LiesOver (maximalIdeal ↥V) := ⟨hunder.symm⟩
  rw [Ideal.inertiaDeg_algebraMap]

  let instT : Algebra (↥V ⧸ maximalIdeal ↥V) (↥w.toValuationSubring ⧸ maximalIdeal ↥w.toValuationSubring) :=
    AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward (F := K) (w := w)
  let instO : Algebra (↥V ⧸ maximalIdeal ↥V) (↥w.toValuationSubring ⧸ maximalIdeal ↥w.toValuationSubring) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hunder.symm)
  have hinst : instO = instT := by
    refine Algebra.algebra_ext _ _ (fun r => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    show (letI := instO; algebraMap (↥V ⧸ maximalIdeal ↥V) (↥w.toValuationSubring ⧸ maximalIdeal ↥w.toValuationSubring) (Ideal.Quotient.mk _ a)) =
      AlgebraicCurve.Place.restrictResidueMap K w (IsLocalRing.residue _ a)
    rw [AlgebraicCurve.Place.restrictResidueMap_residue]
    rfl
  haveI hfinO : @Module.Finite (↥V ⧸ maximalIdeal ↥V) (↥w.toValuationSubring ⧸ maximalIdeal ↥w.toValuationSubring) _ _ instO.toModule := by
    rw [hinst]; exact hfin'

  letI : Algebra (↥V ⧸ maximalIdeal ↥V) (↥w.toValuationSubring ⧸ maximalIdeal ↥w.toValuationSubring) := instO
  let rb : Fin n → ↥w.toValuationSubring ⧸ maximalIdeal ↥w.toValuationSubring := fun i => Ideal.Quotient.mk _ ⟨b i, hbW i⟩
  have hli : LinearIndependent (↥V ⧸ maximalIdeal ↥V) rb := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i

    choose c hc using fun i => Ideal.Quotient.mk_surjective (g i)
    have hsum : Ideal.Quotient.mk (maximalIdeal ↥w.toValuationSubring) (∑ j, algebraMap ↥V ↥w.toValuationSubring (c j) * ⟨b j, hbW j⟩) = 0 := by
      rw [map_sum]
      rw [← hg]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← hc j, map_mul, Algebra.smul_def]
      rfl
    rw [Ideal.Quotient.eq_zero_iff_mem] at hsum
    have hmem : (⟨∑ j, algebraMap K E (c j : K) * b j, sum_mem fun i _ => mul_mem ((ValuationSubring.mem_comap).mp (c i).2) (hbW i)⟩ : ↥w.toValuationSubring) ∈ maximalIdeal ↥w.toValuationSubring := by
      convert hsum using 1
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
      rfl
    have := hind c hmem i
    rw [← hc i, Ideal.Quotient.eq_zero_iff_mem]
    exact this
  have := hli.fintype_card_le_finrank
  simpa using this

theorem post {K E : Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    (V : ValuationSubring K) [IsDiscreteValuationRing ↥V]
    (W : ValuationSubring E) (hW : ∀ y : K, algebraMap K E y ∈ W ↔ y ∈ V)
    (hdvrW : IsDiscreteValuationRing ↥W)
    (ϖ : ↥V) (hϖ : maximalIdeal ↥V = Ideal.span {ϖ})
    {n : ℕ} (hn : 0 < n) (b : Fin n → E) (hbW : ∀ i, b i ∈ W)
    (hind : ∀ c : Fin n → ↥V, (∑ i, algebraMap K E (c i : K) * b i) ∈ W.nonunits → ∀ i, c i ∈ maximalIdeal ↥V)
    (he1 : letI : Algebra ↥V ↥W := BDescRatExt.algOver V W hW; (maximalIdeal ↥V).ramificationIdx' (maximalIdeal ↥W) = 1)
    (hfn : letI : Algebra ↥V ↥W := BDescRatExt.algOver V W hW; (maximalIdeal ↥V).inertiaDeg' (maximalIdeal ↥W) = n) :
    maximalIdeal ↥W = Ideal.span {(⟨algebraMap K E (ϖ : K), (hW _).mpr ϖ.2⟩ : ↥W)} ∧
    ∀ w : ↥W, ∃ c : Fin n → ↥V, ((w : E) - ∑ i, algebraMap K E (c i : K) * b i) ∈ W.nonunits := by
  classical
  letI alg : Algebra ↥V ↥W := BDescRatExt.algOver V W hW
  haveI := hdvrW
  have halg : ∀ v : ↥V, ((algebraMap ↥V ↥W v : ↥W) : E) = algebraMap K E (v : K) := fun v => rfl

  have hunder : (maximalIdeal ↥W).comap (algebraMap ↥V ↥W) = maximalIdeal ↥V := by
    ext v
    rw [Ideal.mem_comap]
    by_cases hv0 : (v : K) = 0
    · have : v = 0 := Subtype.ext hv0
      subst this
      simp
    have hv0' : ((algebraMap ↥V ↥W v : ↥W) : E) ≠ 0 := by
      rw [halg]; exact (map_ne_zero _).mpr hv0
    rw [KFRatLayer.mem_maximalIdeal_iff_inv_not_mem W _ hv0', KFRatLayer.mem_maximalIdeal_iff_inv_not_mem V _ hv0, halg,
      ← map_inv₀, hW]
  haveI hLO : (maximalIdeal ↥W).LiesOver (maximalIdeal ↥V) := ⟨hunder.symm⟩

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥W
  have hπmax : maximalIdeal ↥W = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  set ϖ' : ↥W := algebraMap ↥V ↥W ϖ with hϖ'
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h0
    have hϖ0 : ϖ ≠ 0 := ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ).ne_zero
    apply hϖ0
    have : ((ϖ' : ↥W) : E) = 0 := by rw [h0]; rfl
    rw [hϖ', halg, map_eq_zero] at this
    exact Subtype.ext this
  obtain ⟨m, u, hum⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ'0 hπ
  have hmap : Ideal.map (algebraMap ↥V ↥W) (maximalIdeal ↥V) = maximalIdeal ↥W ^ m := by
    rw [hϖ, Ideal.map_span, Set.image_singleton, ← hϖ', hum, hπmax, Ideal.span_singleton_pow,
      Ideal.span_singleton_mul_left_unit u.isUnit]
  have hπ0 : maximalIdeal ↥W ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hem : (maximalIdeal ↥V).ramificationIdx' (maximalIdeal ↥W) = m :=
    Ideal.ramificationIdx_spec (by rw [hmap]) (by
      rw [hmap]
      exact not_le_of_gt (Ideal.pow_succ_lt_pow hπ0 m))
  have hm1 : m = 1 := hem ▸ he1 |>.symm.symm
  have hunifW : maximalIdeal ↥W = Ideal.span {ϖ'} := by
    rw [hum, hm1, pow_one, Ideal.span_singleton_mul_left_unit u.isUnit, hπmax]
  refine ⟨?_, ?_⟩
  · rw [hunifW, hϖ']
    rfl

  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    letI : Field (↥V ⧸ maximalIdeal ↥V) := Ideal.Quotient.field _
    have hfin : Module.finrank (↥V ⧸ maximalIdeal ↥V) (↥W ⧸ maximalIdeal ↥W) = n := by
      rw [← Ideal.inertiaDeg_algebraMap]; exact hfn
    let bW : Fin n → ↥W := fun i => ⟨b i, hbW i⟩
    let rb : Fin n → ↥W ⧸ maximalIdeal ↥W := fun i => Ideal.Quotient.mk _ (bW i)
    have hsmul : ∀ (c : Fin n → ↥V),
        (∑ i, (Ideal.Quotient.mk (maximalIdeal ↥V) (c i)) • rb i) =
          Ideal.Quotient.mk (maximalIdeal ↥W) (∑ i, algebraMap ↥V ↥W (c i) * bW i) := by
      intro c
      simp only [map_sum, map_mul, rb, Algebra.smul_def, Ideal.Quotient.algebraMap_mk_of_liesOver]
    have hcoe : ∀ (c : Fin n → ↥V),
        ((∑ i, algebraMap ↥V ↥W (c i) * bW i : ↥W) : E) = ∑ i, algebraMap K E (c i : K) * b i := by
      intro c
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, halg]
      exact Finset.sum_congr rfl fun i _ => rfl
    have hli : LinearIndependent (↥V ⧸ maximalIdeal ↥V) rb := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      choose c hc using fun i => Ideal.Quotient.mk_surjective (g i)
      have hg' : Ideal.Quotient.mk (maximalIdeal ↥W) (∑ i, algebraMap ↥V ↥W (c i) * bW i) = 0 := by
        rw [← hsmul]
        simpa only [hc] using hg
      rw [Ideal.Quotient.eq_zero_iff_mem, ← ValuationSubring.coe_mem_nonunits_iff, hcoe] at hg'
      rw [← hc i, Ideal.Quotient.eq_zero_iff_mem]
      exact hind c hg' i
    have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [hfin, Fintype.card_fin])
    intro w
    have hw : Ideal.Quotient.mk (maximalIdeal ↥W) w ∈ Submodule.span (↥V ⧸ maximalIdeal ↥V) (Set.range rb) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hw
    choose c hc using fun i => Ideal.Quotient.mk_surjective (g i)
    refine ⟨c, ?_⟩
    have : Ideal.Quotient.mk (maximalIdeal ↥W) (∑ i, algebraMap ↥V ↥W (c i) * bW i) =
        Ideal.Quotient.mk (maximalIdeal ↥W) w := by
      rw [← hsmul, ← hg]
      simp only [hc]
    rw [Ideal.Quotient.eq, ← Ideal.neg_mem_iff, neg_sub] at this
    rw [← hcoe c, show (w : E) - ((∑ i, algebraMap ↥V ↥W (c i) * bW i : ↥W) : E) =
      ((w - ∑ i, algebraMap ↥V ↥W (c i) * bW i : ↥W) : E) from rfl,
      ValuationSubring.coe_mem_nonunits_iff]
    exact this

theorem layer {k₀ K E : Type} [Field k₀] [Field K] [Field E] [Algebra k₀ K] [Algebra k₀ E] [Algebra K E]
    [IsScalarTower k₀ K E] [FiniteDimensional K E] [CharZero K]
    (V : ValuationSubring K) [IsDiscreteValuationRing ↥V] (hk₀V : ∀ a : k₀, algebraMap k₀ K a ∈ V)
    (ϖ : ↥V) (hϖ : maximalIdeal ↥V = Ideal.span {ϖ})
    {n : ℕ} (b : Fin n → E)
    (hbW : ∀ (W : ValuationSubring E) (hW : ∀ y : K, algebraMap K E y ∈ W ↔ y ∈ V), ∀ i, b i ∈ W)
    (hind : ∀ (W : ValuationSubring E) (hW : ∀ y : K, algebraMap K E y ∈ W ↔ y ∈ V) (c : Fin n → ↥V),
      (∑ i, algebraMap K E (c i : K) * b i) ∈ W.nonunits → ∀ i, c i ∈ maximalIdeal ↥V)
    (hn : Module.finrank K E ≤ n) :
    ∃ (W : ValuationSubring E) (hW : ∀ y : K, algebraMap K E y ∈ W ↔ y ∈ V),
      (∀ W' : ValuationSubring E, (∀ y : K, algebraMap K E y ∈ W' ↔ y ∈ V) → W' = W) ∧
      IsDiscreteValuationRing ↥W ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap K E (ϖ : K), (hW _).mpr ϖ.2⟩ : ↥W)} ∧
      ∀ w : ↥W, ∃ c : Fin n → ↥V, ((w : E) - ∑ i, algebraMap K E (c i : K) * b i) ∈ W.nonunits := by
  classical

  have hf : ∀ (W : ValuationSubring E) (hW : ∀ x : K, algebraMap K E x ∈ W ↔ x ∈ V), IsDiscreteValuationRing ↥W →
      letI : Algebra ↥V ↥W := algOver V W hW
      n ≤ (maximalIdeal ↥V).inertiaDeg' (maximalIdeal ↥W) := by
    intro W hW hdvrW
    haveI := hdvrW
    have hVeq : W.comap (algebraMap K E) = V := by
      ext y; rw [ValuationSubring.mem_comap]; exact hW y
    subst hVeq
    have hk₀W : ∀ a : k₀, algebraMap k₀ E a ∈ W := by
      intro a
      rw [IsScalarTower.algebraMap_apply k₀ K E]
      exact (hW _).mpr (hk₀V a)
    have hind' : ∀ c : Fin n → ↥(W.comap (algebraMap K E)),
        (⟨∑ i, algebraMap K E (c i : K) * b i,
          sum_mem fun i _ => mul_mem ((ValuationSubring.mem_comap).mp (c i).2) (hbW W hW i)⟩ : ↥W) ∈ maximalIdeal ↥W →
        ∀ i, c i ∈ maximalIdeal ↥(W.comap (algebraMap K E)) := by
      intro c hc
      apply hind W hW c
      rw [ValuationSubring.mem_nonunits_iff]
      exact (ValuationSubring.valuation_lt_one_iff W _).mp hc
    have := le_inertiaDeg (k₀ := k₀) (K := K) W hk₀W b (hbW W hW) hind'
    convert this using 2
  obtain ⟨W, hW, huniq, hdvrW, ⟨he1, hfn⟩, hfin⟩ := layer_count V hn hf
  have hn0 : 0 < n := by rw [← hfin]; exact Module.finrank_pos
  obtain ⟨hmax, hspan⟩ := post V W hW hdvrW ϖ hϖ hn0 b (hbW W hW) (hind W hW) he1 hfn
  exact ⟨W, hW, huniq, hdvrW, hmax, hspan⟩

end BDescRatExt

namespace KFRatExt

theorem exists_of_directed_layers
    {F : Type*} [Field F] {ι : Type*} [Nonempty ι]
    (E : ι → Subfield F) (V : ι → Set F)

    (hVE : ∀ i, V i ⊆ E i)
    (hV1 : ∀ i, (1 : F) ∈ V i)
    (hVadd : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, x + y ∈ V i)
    (hVneg : ∀ i, ∀ x ∈ V i, -x ∈ V i)
    (hVmul : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, x * y ∈ V i)
    (hVval : ∀ i, ∀ x ∈ E i, x ∈ V i ∨ x⁻¹ ∈ V i)

    (hdir : ∀ i j, ∃ l, E i ≤ E l ∧ E j ≤ E l)
    (hcov : ∀ x : F, ∃ i, x ∈ E i)
    (hcompat : ∀ i j, E i ≤ E j → ∀ x ∈ E i, (x ∈ V i ↔ x ∈ V j)) :
    ∃ W : ValuationSubring F,

      (∀ (x : F) (i : ι), x ∈ E i → (x ∈ W ↔ x ∈ V i)) ∧

      (∀ (x : ↥W) (i : ι), (x : F) ∈ E i → (x ∈ maximalIdeal ↥W ↔ (x : F) = 0 ∨ (x : F)⁻¹ ∉ V i)) := by
  classical

  have htrans : ∀ (i j : ι) (x : F), x ∈ E i → x ∈ E j → (x ∈ V i ↔ x ∈ V j) := by
    intro i j x hi hj
    obtain ⟨l, hil, hjl⟩ := hdir i j
    rw [hcompat i l hil x hi, hcompat j l hjl x hj]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hV0 : ∀ i, (0 : F) ∈ V i := by
    intro i
    have h := hVadd i 1 (hV1 i) (-1) (hVneg i 1 (hV1 i))
    rwa [add_neg_cancel] at h
  let W : ValuationSubring F :=
    { carrier := {x | ∃ i, x ∈ E i ∧ x ∈ V i}
      mul_mem' := by
        rintro x y ⟨i, hxi, hxV⟩ ⟨j, hyj, hyV⟩
        obtain ⟨l, hil, hjl⟩ := hdir i j
        exact ⟨l, (E l).mul_mem (hil hxi) (hjl hyj),
          hVmul l x ((hcompat i l hil x hxi).1 hxV) y ((hcompat j l hjl y hyj).1 hyV)⟩
      one_mem' := ⟨i₀, (E i₀).one_mem, hV1 i₀⟩
      add_mem' := by
        rintro x y ⟨i, hxi, hxV⟩ ⟨j, hyj, hyV⟩
        obtain ⟨l, hil, hjl⟩ := hdir i j
        exact ⟨l, (E l).add_mem (hil hxi) (hjl hyj),
          hVadd l x ((hcompat i l hil x hxi).1 hxV) y ((hcompat j l hjl y hyj).1 hyV)⟩
      zero_mem' := ⟨i₀, (E i₀).zero_mem, hV0 i₀⟩
      neg_mem' := by
        rintro x ⟨i, hxi, hxV⟩
        exact ⟨i, (E i).neg_mem hxi, hVneg i x hxV⟩
      mem_or_inv_mem' := by
        intro x
        obtain ⟨i, hxi⟩ := hcov x
        rcases hVval i x hxi with h | h
        · exact Or.inl ⟨i, hxi, h⟩
        · exact Or.inr ⟨i, (E i).inv_mem hxi, h⟩ }
  have hmemW : ∀ x : F, x ∈ W ↔ ∃ i, x ∈ E i ∧ x ∈ V i := fun _ => Iff.rfl
  have h1 : ∀ (x : F) (i : ι), x ∈ E i → (x ∈ W ↔ x ∈ V i) := by
    intro x i hxi
    rw [hmemW]
    constructor
    · rintro ⟨j, hxj, hxV⟩
      exact (htrans j i x hxj hxi).1 hxV
    · intro h
      exact ⟨i, hxi, h⟩
  refine ⟨W, h1, ?_⟩
  intro x i hxi
  have hunit : IsUnit x ↔ ((x : F) ≠ 0 ∧ (x : F)⁻¹ ∈ W) := by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hx.exists_right_inv
      have hF : (x : F) * (y : F) = 1 := by
        have := congrArg (fun z : ↥W => (z : F)) hy
        simpa using this
      refine ⟨left_ne_zero_of_mul_eq_one hF, ?_⟩
      rw [inv_eq_of_mul_eq_one_right hF]
      exact y.2
    · rintro ⟨hne, hinv⟩
      have hxy : x * ⟨(x : F)⁻¹, hinv⟩ = 1 := by
        apply Subtype.ext
        show (x : F) * (x : F)⁻¹ = 1
        exact mul_inv_cancel₀ hne
      have hyx : (⟨(x : F)⁻¹, hinv⟩ : ↥W) * x = 1 := by
        rw [mul_comm]; exact hxy
      exact ⟨⟨x, ⟨(x : F)⁻¹, hinv⟩, hxy, hyx⟩, rfl⟩
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, hunit, not_and_or, not_not,
    h1 _ i ((E i).inv_mem hxi)]

theorem isUnit_iff_inv_mem {L : Type*} [Field L] (B : ValuationSubring L) (x : B)
    (hx0 : (x : L) ≠ 0) : IsUnit x ↔ (x : L)⁻¹ ∈ B := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hx.exists_left_inv
    have hyx : (y : L) * (x : L) = 1 := by
      have := congrArg (Subtype.val) hy
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left hyx]
    exact y.2
  · exact isUnit_iff_exists_inv.mpr ⟨⟨_, hx⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

private theorem _root_.KFRatExt.mem_maximalIdeal_iff_inv_not_mem {L : Type*} [Field L] (B : ValuationSubring L) (x : B)
    (hx0 : (x : L) ≠ 0) : x ∈ maximalIdeal B ↔ (x : L)⁻¹ ∉ B := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, isUnit_iff_inv_mem B x hx0]

p2m_export "KFRatExt" "mem_maximalIdeal_iff_inv_not_mem"
theorem mem_nonunits_iff_eq_zero_or {L : Type*} [Field L] (B : ValuationSubring L) (x : L) :
    x ∈ B.nonunits ↔ x ∈ B ∧ (x = 0 ∨ x⁻¹ ∉ B) := by
  constructor
  · intro hx
    have hxB : x ∈ B := B.nonunits_le hx
    refine ⟨hxB, ?_⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have : (⟨x, hxB⟩ : B) ∈ maximalIdeal B :=
        (ValuationSubring.coe_mem_nonunits_iff (a := ⟨x, hxB⟩)).mp hx
      exact (mem_maximalIdeal_iff_inv_not_mem B ⟨x, hxB⟩ hx0).mp this
  · rintro ⟨hxB, h⟩
    rw [show x = ((⟨x, hxB⟩ : B) : L) from rfl, ValuationSubring.coe_mem_nonunits_iff]
    rcases h with h | h
    · have : (⟨x, hxB⟩ : B) = 0 := Subtype.ext h
      rw [this]; exact Ideal.zero_mem _
    · exact (mem_maximalIdeal_iff_inv_not_mem B ⟨x, hxB⟩
        (fun h0 => h (by rw [show x = 0 from h0, inv_zero]; exact B.zero_mem))).mpr h

theorem mem_iff_of_le_of_unique {K F : Type*} [Field K] [Field F] [Algebra K F]
    (V : ValuationSubring K) (E₁ E₂ : IntermediateField K F) (hle : E₁ ≤ E₂)
    (W₁ : ValuationSubring ↥E₁) (W₂ : ValuationSubring ↥E₂)
    (hU₁ : ∀ W' : ValuationSubring ↥E₁, (∀ x : K, algebraMap K ↥E₁ x ∈ W' ↔ x ∈ V) → W' = W₁)
    (htr₂ : ∀ x : K, algebraMap K ↥E₂ x ∈ W₂ ↔ x ∈ V)
    (f : F) (h₁ : f ∈ E₁) : (⟨f, h₁⟩ : ↥E₁) ∈ W₁ ↔ (⟨f, hle h₁⟩ : ↥E₂) ∈ W₂ := by
  let ι : ↥E₁ →+* ↥E₂ := (IntermediateField.inclusion hle).toRingHom
  have hV : W₂.comap ι = W₁ := hU₁ _ (fun x => by rw [ValuationSubring.mem_comap]; exact htr₂ x)
  rw [← hV, ValuationSubring.mem_comap]
  exact Iff.rfl

theorem exists_common_generator {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F]
    (K₁ L : IntermediateField k F) (hK₁L : K₁ ≤ L) (halg : ∀ x : ↥L, IsAlgebraic ↥K₁ (x : F))
    (x y : ↥L) : ∃ z : ↥L, (x : F) ∈ IntermediateField.adjoin ↥K₁ {(z : F)} ∧
      (y : F) ∈ IntermediateField.adjoin ↥K₁ {(z : F)} := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  haveI : CharZero ↥K₁ := charZero_of_injective_algebraMap (algebraMap k ↥K₁).injective
  set M : IntermediateField ↥K₁ F := IntermediateField.adjoin ↥K₁ {(x : F), (y : F)} with hM
  haveI : FiniteDimensional ↥K₁ ↥M := by
    refine IntermediateField.finiteDimensional_adjoin (fun t ht => ?_)
    rcases ht with rfl | ht
    · exact (halg x).isIntegral
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact (halg y).isIntegral
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ↥K₁ ↥M
  have hML : M ≤ IntermediateField.extendScalars hK₁L := by
    rw [hM, IntermediateField.adjoin_le_iff]
    intro t ht
    show t ∈ IntermediateField.extendScalars hK₁L
    rw [IntermediateField.mem_extendScalars]
    rcases ht with rfl | ht
    · exact x.2
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact y.2
  have hαL : (α : F) ∈ L := (IntermediateField.mem_extendScalars hK₁L).mp (hML α.2)

  have key : ∀ t : F, t ∈ M → t ∈ IntermediateField.adjoin ↥K₁ {(α : F)} := by
    intro t ht
    have h1 : (⟨t, ht⟩ : ↥M) ∈ IntermediateField.adjoin ↥K₁ {α} := by rw [hα]; trivial
    have h2 : (IntermediateField.adjoin ↥K₁ {α}).map M.val = IntermediateField.adjoin ↥K₁ {(α : F)} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
    rw [← h2]
    exact ⟨⟨t, ht⟩, h1, rfl⟩
  refine ⟨⟨α, hαL⟩, key _ ?_, key _ ?_⟩
  · exact IntermediateField.subset_adjoin ↥K₁ _ (Set.mem_insert _ _)
  · exact IntermediateField.subset_adjoin ↥K₁ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem val_mul_pow {E : Type*} [Field E] (B : ValuationSubring E) (u v : ↥B) (n : ℕ) :
    ((u * v ^ n : ↥B) : E) = (u : E) * (v : E) ^ n := by simp

theorem val_pow_mul {E : Type*} [Field E] (B : ValuationSubring E) (u v : ↥B) (n : ℕ) :
    ((v ^ n * u : ↥B) : E) = (v : E) ^ n * (u : E) := by simp

theorem ifval_mul_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (E : IntermediateField K F)
    (u v : ↥E) (n : ℕ) : ((u * v ^ n : ↥E) : F) = (u : F) * (v : F) ^ n := by simp

noncomputable abbrev Lay {k F : Type} [Field k] [Field F] [Algebra k F]
    (K₁ F₀ : IntermediateField k F) (x : F) : IntermediateField ↥(K₁ ⊔ F₀) F :=
  IntermediateField.adjoin ↥(K₁ ⊔ F₀) ({x} : Set F)

def LayerSpec {k F : Type} [Field k] [Field F] [Algebra k F]
    (K₁ L F₀ : IntermediateField k F) (V₁ : ValuationSubring ↥(K₁ ⊔ F₀)) (ϖ : ↥V₁) (x : ↥L) : Prop :=
  ∃ W : ValuationSubring ↥(Lay K₁ F₀ (x : F)),
    (∀ f : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) f ∈ W ↔ f ∈ V₁) ∧
    (∀ W' : ValuationSubring ↥(Lay K₁ F₀ (x : F)),
      (∀ f : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) f ∈ W' ↔ f ∈ V₁) → W' = W) ∧
    IsDiscreteValuationRing ↥W ∧
    (∃ h : algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) (ϖ : ↥(K₁ ⊔ F₀)) ∈ W,
      maximalIdeal ↥W = Ideal.span {(⟨_, h⟩ : ↥W)}) ∧
    (⟨(x : F), IntermediateField.mem_adjoin_simple_self _ _⟩ : ↥(Lay K₁ F₀ (x : F))) ∈ W ∧
    (∀ w : ↥W, ∃ (y : ↥L) (hy : (y : F) ∈ Lay K₁ F₀ (x : F)),
      ((w : ↥(Lay K₁ F₀ (x : F))) - ⟨(y : F), hy⟩ : ↥(Lay K₁ F₀ (x : F))) ∈ W.nonunits)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem main_of_layers
    {k F : Type} [Field k] [CharZero k] [Field F] [Algebra k F]
    (K₁ L F₀ : IntermediateField k F) (hK₁L : K₁ ≤ L) (hgen : L ⊔ F₀ = ⊤)
    (halg : ∀ x : ↥L, IsAlgebraic ↥K₁ (x : F))
    (V₁ : ValuationSubring ↥(K₁ ⊔ F₀)) [IsDiscreteValuationRing ↥V₁]
    (ϖ : ↥V₁) (hϖ : maximalIdeal ↥V₁ = Ideal.span {ϖ})
    (hlayer : ∀ x : ↥L, LayerSpec K₁ L F₀ V₁ ϖ x) :
    (∃! P : Place ↥L F, ∀ f : ↥(K₁ ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) ∧
    (∀ P : Place ↥L F, (∀ f : ↥(K₁ ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) →
      P.IsRational) := by
  classical
  let E : ↥L → IntermediateField ↥(K₁ ⊔ F₀) F := fun x => Lay K₁ F₀ (x : F)
  choose Wx hW using hlayer
  have htr : ∀ x (f : ↥(K₁ ⊔ F₀)), algebraMap ↥(K₁ ⊔ F₀) ↥(E x) f ∈ Wx x ↔ f ∈ V₁ :=
    fun x => (hW x).1
  have huniq : ∀ x (W' : ValuationSubring ↥(E x)),
      (∀ f : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥(E x) f ∈ W' ↔ f ∈ V₁) → W' = Wx x :=
    fun x => (hW x).2.1
  have hdvr : ∀ x, IsDiscreteValuationRing ↥(Wx x) := fun x => (hW x).2.2.1
  have hunif := fun x => (hW x).2.2.2.1
  have hxW := fun x => (hW x).2.2.2.2.1
  have hres := fun x => (hW x).2.2.2.2.2

  have hF₁E : ∀ x (f : ↥(K₁ ⊔ F₀)), (f : F) ∈ E x := fun x f => (E x).algebraMap_mem f
  have hLE : ∀ x : ↥L, (x : F) ∈ E x := fun x => IntermediateField.mem_adjoin_simple_self _ _
  have halgmap : ∀ x (f : ↥(K₁ ⊔ F₀)),
      algebraMap ↥(K₁ ⊔ F₀) ↥(E x) f = ⟨(f : F), hF₁E x f⟩ := fun x f => rfl

  have hdir : ∀ x y : ↥L, ∃ z : ↥L, E x ≤ E z ∧ E y ≤ E z := by
    intro x y
    obtain ⟨z, hxz, hyz⟩ := exists_common_generator K₁ L hK₁L halg x y
    have hsub : ∀ t : F, t ∈ IntermediateField.adjoin ↥K₁ {(z : F)} → t ∈ E z := by
      intro t ht
      have h1 : (IntermediateField.adjoin ↥K₁ {(z : F)}).toSubfield ≤ (E z).toSubfield := by
        rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield]
        apply Subfield.closure_mono
        apply Set.union_subset_union_left
        rintro _ ⟨c, rfl⟩
        exact ⟨⟨(c : F), (le_sup_left : K₁ ≤ K₁ ⊔ F₀) c.2⟩, rfl⟩
      exact h1 ht
    refine ⟨z, ?_, ?_⟩
    · exact IntermediateField.adjoin_simple_le_iff.mpr (hsub _ hxz)
    · exact IntermediateField.adjoin_simple_le_iff.mpr (hsub _ hyz)

  have hcov : ∀ f : F, ∃ x : ↥L, f ∈ E x := by
    let U : IntermediateField k F :=
      { carrier := {f | ∃ x : ↥L, f ∈ E x}
        mul_mem' := by
          rintro a b ⟨x, ha⟩ ⟨y, hb⟩
          obtain ⟨z, hxz, hyz⟩ := hdir x y
          exact ⟨z, (E z).mul_mem (hxz ha) (hyz hb)⟩
        one_mem' := ⟨0, (E 0).one_mem⟩
        add_mem' := by
          rintro a b ⟨x, ha⟩ ⟨y, hb⟩
          obtain ⟨z, hxz, hyz⟩ := hdir x y
          exact ⟨z, (E z).add_mem (hxz ha) (hyz hb)⟩
        zero_mem' := ⟨0, (E 0).zero_mem⟩
        algebraMap_mem' := fun r =>
          ⟨0, hF₁E 0 ⟨algebraMap k F r, (K₁ ⊔ F₀).algebraMap_mem r⟩⟩
        inv_mem' := by
          rintro a ⟨x, ha⟩
          exact ⟨x, (E x).inv_mem ha⟩ }
    have hU : ∀ f : F, f ∈ U ↔ ∃ x : ↥L, f ∈ E x := fun _ => Iff.rfl
    have htop : (⊤ : IntermediateField k F) ≤ U := by
      rw [← hgen]
      refine sup_le ?_ ?_
      · intro f hf; exact (hU f).mpr ⟨⟨f, hf⟩, hLE ⟨f, hf⟩⟩
      · intro f hf; exact (hU f).mpr ⟨0, hF₁E 0 ⟨f, (le_sup_right : F₀ ≤ K₁ ⊔ F₀) hf⟩⟩
    intro f
    exact (hU f).mp (htop IntermediateField.mem_top)

  let Es : ↥L → Subfield F := fun x => (E x).toSubfield
  let V : ↥L → Set F := fun x => {f | ∃ h : f ∈ E x, (⟨f, h⟩ : ↥(E x)) ∈ Wx x}
  have hVmem : ∀ x (f : F) (h : f ∈ E x), f ∈ V x ↔ (⟨f, h⟩ : ↥(E x)) ∈ Wx x :=
    fun x f h => ⟨fun ⟨_, h'⟩ => h', fun h' => ⟨h, h'⟩⟩
  have hVE : ∀ x, V x ⊆ (Es x : Set F) := fun x f ⟨h, _⟩ => h
  have hcompat : ∀ x z, Es x ≤ Es z → ∀ f ∈ Es x, (f ∈ V x ↔ f ∈ V z) := by
    intro x z hle f hf
    have hle' : E x ≤ E z := hle
    rw [hVmem x f hf, hVmem z f (hle' hf)]
    exact mem_iff_of_le_of_unique V₁ (E x) (E z) hle' (Wx x) (Wx z) (huniq x) (htr z) f hf
  have hV1 : ∀ x, (1 : F) ∈ V x := fun x => ⟨(E x).one_mem, (Wx x).one_mem⟩
  have hVadd : ∀ x, ∀ a ∈ V x, ∀ b ∈ V x, a + b ∈ V x :=
    fun x a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ => ⟨(E x).add_mem ha hb, (Wx x).add_mem _ _ ha' hb'⟩
  have hVneg : ∀ x, ∀ a ∈ V x, -a ∈ V x := fun x a ⟨ha, ha'⟩ => ⟨(E x).neg_mem ha, (Wx x).neg_mem _ ha'⟩
  have hVmul : ∀ x, ∀ a ∈ V x, ∀ b ∈ V x, a * b ∈ V x :=
    fun x a ⟨ha, ha'⟩ b ⟨hb, hb'⟩ => ⟨(E x).mul_mem ha hb, (Wx x).mul_mem _ _ ha' hb'⟩
  have hVval : ∀ x, ∀ a ∈ Es x, a ∈ V x ∨ a⁻¹ ∈ V x := by
    intro x a ha
    rcases (Wx x).mem_or_inv_mem ⟨a, ha⟩ with h | h
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr ⟨(E x).inv_mem ha, h⟩
  haveI : Nonempty ↥L := ⟨0⟩
  have hdir' : ∀ x y : ↥L, ∃ z, Es x ≤ Es z ∧ Es y ≤ Es z := hdir
  have hcov' : ∀ f : F, ∃ x, f ∈ Es x := hcov
  obtain ⟨W, hWmem, hWmax⟩ :=
    exists_of_directed_layers Es V hVE hV1 hVadd hVneg hVmul hVval hdir' hcov' hcompat

  have hWlayer : ∀ x (f : F) (h : f ∈ E x), f ∈ W ↔ (⟨f, h⟩ : ↥(E x)) ∈ Wx x := by
    intro x f h; rw [hWmem f x h, hVmem x f h]

  let p : F := ((ϖ : ↥(K₁ ⊔ F₀)) : F)
  have hpE : ∀ x, p ∈ E x := fun x => hF₁E x ϖ
  have hpWx : ∀ x, (⟨p, hpE x⟩ : ↥(E x)) ∈ Wx x := by
    intro x; rw [← halgmap]; exact (htr x _).mpr ϖ.2
  have hunif' : ∀ x, maximalIdeal ↥(Wx x) = Ideal.span {(⟨⟨p, hpE x⟩, hpWx x⟩ : ↥(Wx x))} := by
    intro x
    obtain ⟨h, hh⟩ := hunif x
    rw [hh, show (⟨_, h⟩ : ↥(Wx x)) = ⟨⟨p, hpE x⟩, hpWx x⟩ from Subtype.ext rfl]
  have hirrx : ∀ x, Irreducible (⟨⟨p, hpE x⟩, hpWx x⟩ : ↥(Wx x)) := by
    intro x
    haveI := hdvr x
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (hunif' x)
  have hpW : p ∈ W := (hWlayer 0 p (hpE 0)).mpr (hpWx 0)

  have hunitW : ∀ x (u : ↥(Wx x)), IsUnit u → ∃ hu : ((u : ↥(E x)) : F) ∈ W, IsUnit (⟨_, hu⟩ : ↥W) := by
    intro x u hu
    have huW : ((u : ↥(E x)) : F) ∈ W := (hWlayer x _ (u : ↥(E x)).2).mpr (by simpa using u.2)
    refine ⟨huW, ?_⟩
    by_cases hu0 : ((u : ↥(E x)) : F) = 0
    · exfalso
      have : u = 0 := Subtype.ext (Subtype.ext hu0)
      rw [this] at hu
      haveI := hdvr x
      exact not_isUnit_zero hu
    · rw [isUnit_iff_inv_mem W ⟨_, huW⟩ hu0]
      have h1 : ((u : ↥(E x)) : ↥(E x))⁻¹ ∈ Wx x :=
        (isUnit_iff_inv_mem (Wx x) u (fun h => hu0 (congrArg Subtype.val h))).mp hu
      have h2 : (((u : ↥(E x)))⁻¹ : F) = (((u : ↥(E x)) : F))⁻¹ := by simp
      exact (hWlayer x _ ((E x).inv_mem (u : ↥(E x)).2)).mpr (by exact h1)

  have hWel : ∀ w : ↥W, ∃ (x : ↥L) (h : (w : F) ∈ E x), (⟨(w : F), h⟩ : ↥(E x)) ∈ Wx x := by
    intro w
    obtain ⟨x, hx⟩ := hcov (w : F)
    exact ⟨x, hx, (hWlayer x _ hx).mp w.2⟩

  haveI hWdvr : IsDiscreteValuationRing ↥W := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨⟨p, hpW⟩, ?_, ?_⟩
    ·
      refine ⟨?_, ?_⟩
      ·
        have hp0 : p ≠ 0 := by
          intro h0
          haveI := hdvr 0
          apply (hirrx 0).ne_zero
          exact Subtype.ext (Subtype.ext h0)
        rw [isUnit_iff_inv_mem W ⟨p, hpW⟩ hp0]
        intro hinv
        have h1 : (⟨p, hpE 0⟩ : ↥(E 0))⁻¹ ∈ Wx 0 := by
          rw [show (⟨p, hpE 0⟩ : ↥(E 0))⁻¹ = ⟨p⁻¹, (E 0).inv_mem (hpE 0)⟩ from Subtype.ext rfl]
          exact (hWlayer 0 p⁻¹ ((E 0).inv_mem (hpE 0))).mp hinv
        haveI := hdvr 0
        have hp0' : (((⟨⟨p, hpE 0⟩, hpWx 0⟩ : ↥(Wx 0)) : ↥(E 0)) : ↥(E 0)) ≠ 0 :=
          fun h => hp0 (congrArg Subtype.val h)
        exact (hirrx 0).not_isUnit ((isUnit_iff_inv_mem (Wx 0) _ hp0').mpr h1)
      · intro a b hab

        obtain ⟨xa, ha, haW⟩ := hWel a
        obtain ⟨xb, hb, hbW⟩ := hWel b
        obtain ⟨z, haz, hbz⟩ := hdir xa xb
        have haz' : (⟨(a : F), haz ha⟩ : ↥(E z)) ∈ Wx z := (hWlayer z _ (haz ha)).mp a.2
        have hbz' : (⟨(b : F), hbz hb⟩ : ↥(E z)) ∈ Wx z := (hWlayer z _ (hbz hb)).mp b.2
        haveI := hdvr z
        have hprod : (⟨⟨p, hpE z⟩, hpWx z⟩ : ↥(Wx z)) = ⟨_, haz'⟩ * ⟨_, hbz'⟩ := by
          apply Subtype.ext; apply Subtype.ext
          show p = (a : F) * (b : F)
          exact congrArg (fun w : ↥W => (w : F)) hab
        rcases (hirrx z).isUnit_or_isUnit hprod with hu | hu
        · left
          obtain ⟨hu', hunit⟩ := hunitW z _ hu
          exact hunit
        · right
          obtain ⟨hu', hunit⟩ := hunitW z _ hu
          exact hunit
    ·
      intro w hw0
      obtain ⟨x, hx, hwx⟩ := hWel w
      haveI := hdvr x
      have hw0' : (⟨⟨(w : F), hx⟩, hwx⟩ : ↥(Wx x)) ≠ 0 := by
        intro h
        apply hw0
        exact Subtype.ext (congrArg (fun v : ↥(Wx x) => ((v : ↥(E x)) : F)) h)
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0' (hirrx x)
      obtain ⟨huW, hunit⟩ := hunitW x (u : ↥(Wx x)) u.isUnit
      refine ⟨n, ?_⟩

      refine ⟨hunit.unit, Subtype.ext ?_⟩

      have hu1 := congrArg (Subtype.val : ↥(Wx x) → ↥(E x)) hu
      rw [val_mul_pow (Wx x)] at hu1
      have hu2 := congrArg (Subtype.val : ↥(E x) → F) hu1
      rw [ifval_mul_pow (E x)] at hu2

      have e1 := val_pow_mul W (hunit.unit : ↥W) ⟨p, hpW⟩ n
      rw [IsUnit.unit_spec] at e1
      refine e1.trans ?_
      rw [mul_comm]
      exact hu2.symm

  have hWne : W ≠ ⊤ := by
    intro htop
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.exists_irreducible ↥W
    have hm0 : (m : F) ≠ 0 := fun h => hm.ne_zero (Subtype.ext h)
    apply hm.not_isUnit
    have h' : ((m : ↥W) : F)⁻¹ ∈ (⊤ : ValuationSubring F) := ValuationSubring.mem_top _
    rw [← htop] at h'
    exact (isUnit_iff_inv_mem W m hm0).mpr h'
  have hPIR : IsPrincipalIdealRing ↥W := IsDiscreteValuationRing.toIsPrincipalIdealRing
  have hLW : ∀ a : ↥L, algebraMap ↥L F a ∈ W := fun a => (hWlayer a (a : F) (hLE a)).mpr (hxW a)
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Place ↥L F, P₀.toValuationSubring = W :=
    ⟨Place.mk W hLW hWne hPIR, rfl⟩
  have htrace : ∀ f : ↥(K₁ ⊔ F₀), (f : F) ∈ P₀.toValuationSubring ↔ f ∈ V₁ := by
    intro f
    rw [hP₀, hWlayer 0 (f : F) (hF₁E 0 f), ← halgmap, htr]

  have huniqP : ∀ P : Place ↥L F,
      (∀ f : ↥(K₁ ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) → P = P₀ := by
    intro P hP
    apply Place.ext
    ext f
    obtain ⟨x, hx⟩ := hcov f
    let W' : ValuationSubring ↥(E x) := P.toValuationSubring.comap (algebraMap ↥(E x) F)
    have hW' : ∀ g : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥(E x) g ∈ W' ↔ g ∈ V₁ := by
      intro g
      rw [ValuationSubring.mem_comap, halgmap]
      exact hP g
    have hW'eq : W' = Wx x := huniq x W' hW'
    rw [hP₀, hWlayer x f hx, ← hW'eq, ValuationSubring.mem_comap]
    exact Iff.rfl
  refine ⟨⟨P₀, htrace, huniqP⟩, ?_⟩

  intro P hP
  rw [huniqP P hP]
  subst hP₀
  intro r
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨x, hx, hwx⟩ := hWel w
  obtain ⟨y, hy, hnu⟩ := hres x ⟨_, hwx⟩
  refine ⟨y, ?_⟩
  rw [IsScalarTower.algebraMap_apply ↥L ↥P₀.toValuationSubring (IsLocalRing.ResidueField ↥P₀.toValuationSubring)]
  show Ideal.Quotient.mk (maximalIdeal ↥P₀.toValuationSubring) (algebraMap ↥L ↥P₀.toValuationSubring y) =
    Ideal.Quotient.mk (maximalIdeal ↥P₀.toValuationSubring) w
  symm
  rw [Ideal.Quotient.eq]

  have hdE : ((w : F) - (y : F)) ∈ E x := (E x).sub_mem hx hy
  have hval : ((w - algebraMap ↥L ↥P₀.toValuationSubring y : ↥P₀.toValuationSubring) : F) =
      (w : F) - (y : F) := rfl
  rw [hWmax _ x (by rw [hval]; exact hdE), hval]
  rcases ((mem_nonunits_iff_eq_zero_or (Wx x) _).mp hnu).2 with h0 | hinv
  · left
    exact congrArg Subtype.val h0
  · right
    intro hV
    apply hinv
    rw [show ((⟨(w : F), hx⟩ : ↥(E x)) - ⟨(y : F), hy⟩ : ↥(E x))⁻¹ =
      ⟨((w : F) - (y : F))⁻¹, (E x).inv_mem hdE⟩ from Subtype.ext rfl]
    exact (hVmem x _ _).mp hV

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem layerSpec_of
    {k F : Type} [Field k] [CharZero k] [Field F] [Algebra k F]
    (K₁ L F₀ : IntermediateField k F) (hK₁L : K₁ ≤ L)
    (halg : ∀ x : ↥L, IsAlgebraic ↥K₁ (x : F))
    (V₁ : ValuationSubring ↥(K₁ ⊔ F₀))
    (hK₁V : ∀ x : ↥K₁, (⟨(x : F), (le_sup_left : K₁ ≤ K₁ ⊔ F₀) x.2⟩ : ↥(K₁ ⊔ F₀)) ∈ V₁)
    [IsDiscreteValuationRing ↥V₁]
    (hrat : ∀ v : ↥V₁, ∃ x : ↥K₁,
      v - ⟨⟨(x : F), (le_sup_left : K₁ ≤ K₁ ⊔ F₀) x.2⟩, hK₁V x⟩ ∈ maximalIdeal ↥V₁)
    (ϖ : ↥V₁) (x : ↥L)
    (h_layer : ∀ {n : ℕ} (b : Fin n → ↥(Lay K₁ F₀ (x : F))),
      (∀ (W : ValuationSubring ↥(Lay K₁ F₀ (x : F)))
        (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) y ∈ W ↔ y ∈ V₁),
        ∀ i, b i ∈ W) →
      (∀ (W : ValuationSubring ↥(Lay K₁ F₀ (x : F)))
        (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) y ∈ W ↔ y ∈ V₁)
        (c : Fin n → ↥V₁),
        (∑ i, algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) (c i : ↥(K₁ ⊔ F₀)) * b i) ∈ W.nonunits →
        ∀ i, c i ∈ maximalIdeal ↥V₁) →
      Module.finrank ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) ≤ n →
      ∃ (W : ValuationSubring ↥(Lay K₁ F₀ (x : F)))
        (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) y ∈ W ↔ y ∈ V₁),
        (∀ W' : ValuationSubring ↥(Lay K₁ F₀ (x : F)),
          (∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) y ∈ W' ↔ y ∈ V₁) → W' = W) ∧
        IsDiscreteValuationRing ↥W ∧
        maximalIdeal ↥W = Ideal.span {(⟨algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) (ϖ : ↥(K₁ ⊔ F₀)),
          (hW _).mpr ϖ.2⟩ : ↥W)} ∧
        ∀ w : ↥W, ∃ c : Fin n → ↥V₁,
          ((w : ↥(Lay K₁ F₀ (x : F))) -
            ∑ i, algebraMap ↥(K₁ ⊔ F₀) ↥(Lay K₁ F₀ (x : F)) (c i : ↥(K₁ ⊔ F₀)) * b i) ∈ W.nonunits) :
    LayerSpec K₁ L F₀ V₁ ϖ x := by
  classical

  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  haveI : CharZero ↥(K₁ ⊔ F₀) := charZero_of_injective_algebraMap (algebraMap k ↥(K₁ ⊔ F₀)).injective
  let ι₁ : ↥K₁ →+* ↥(K₁ ⊔ F₀) := (IntermediateField.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ F₀)).toRingHom
  have hι₁ : ∀ c : ↥K₁, (ι₁ c : F) = (c : F) := fun c => rfl
  letI algK₁F₁ : Algebra ↥K₁ ↥(K₁ ⊔ F₀) := ι₁.toAlgebra
  haveI : IsScalarTower ↥K₁ ↥(K₁ ⊔ F₀) F := IsScalarTower.of_algebraMap_eq fun c => rfl
  set E : IntermediateField ↥(K₁ ⊔ F₀) F := Lay K₁ F₀ (x : F) with hE
  letI algK₁E : Algebra ↥K₁ ↥E := ((algebraMap ↥(K₁ ⊔ F₀) ↥E).comp ι₁).toAlgebra
  haveI : IsScalarTower ↥K₁ ↥(K₁ ⊔ F₀) ↥E := IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI : IsScalarTower ↥K₁ ↥E F := IsScalarTower.of_algebraMap_eq fun c => rfl
  have hxK₁ : IsIntegral ↥K₁ (x : F) := (halg x).isIntegral
  have hxF₁ : IsIntegral ↥(K₁ ⊔ F₀) (x : F) := hxK₁.tower_top
  haveI : FiniteDimensional ↥(K₁ ⊔ F₀) ↥E := IntermediateField.adjoin.finiteDimensional hxF₁
  let ξ : ↥E := ⟨(x : F), IntermediateField.mem_adjoin_simple_self _ _⟩
  have hξK₁ : IsIntegral ↥K₁ ξ :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥K₁ ↥E F) Subtype.val_injective).mp
      (show IsIntegral ↥K₁ ((IsScalarTower.toAlgHom ↥K₁ ↥E F) ξ) from hxK₁)
  set n : ℕ := (minpoly ↥K₁ (x : F)).natDegree with hn
  let b : Fin n → ↥E := fun i => ξ ^ (i : ℕ)

  have hdeg : Module.finrank ↥(K₁ ⊔ F₀) ↥E ≤ n := by
    rw [hE, show Lay K₁ F₀ (x : F) = IntermediateField.adjoin ↥(K₁ ⊔ F₀) {(x : F)} from rfl,
      IntermediateField.adjoin.finrank hxF₁, hn]
    have hdvd := minpoly.dvd_map_of_isScalarTower ↥K₁ ↥(K₁ ⊔ F₀) (x : F)
    have hne : (minpoly ↥K₁ (x : F)).map (algebraMap ↥K₁ ↥(K₁ ⊔ F₀)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ↥K₁ ↥(K₁ ⊔ F₀)).injective).mpr (minpoly.ne_zero hxK₁)
    calc (minpoly ↥(K₁ ⊔ F₀) (x : F)).natDegree
        ≤ ((minpoly ↥K₁ (x : F)).map (algebraMap ↥K₁ ↥(K₁ ⊔ F₀))).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hne
      _ = (minpoly ↥K₁ (x : F)).natDegree := Polynomial.natDegree_map_eq_of_injective
          (algebraMap ↥K₁ ↥(K₁ ⊔ F₀)).injective _

  have hξW : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁), ξ ∈ W := by
    intro W hW
    letI algK₁W : Algebra ↥K₁ ↥W :=
      ((algebraMap ↥K₁ ↥E).codRestrict W.toSubring (fun c => (hW (ι₁ c)).mpr (hK₁V c))).toAlgebra
    haveI : IsScalarTower ↥K₁ ↥W ↥E := IsScalarTower.of_algebraMap_eq fun c => rfl
    have h1 : IsIntegral ↥W ξ := hξK₁.tower_top
    obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W) (K := ↥E)).mp h1
    rw [← hw]
    exact w.2
  have hbW : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁), ∀ i, b i ∈ W :=
    fun W hW i => W.pow_mem (hξW W hW) _

  have hadjW : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁),
      ∀ e : ↥E, e ∈ IntermediateField.adjoin ↥K₁ {ξ} → e ∈ W := by
    intro W hW e he
    let S : Subalgebra ↥K₁ ↥E :=
      { carrier := W
        mul_mem' := fun ha hb => W.mul_mem _ _ ha hb
        one_mem' := W.one_mem
        add_mem' := fun ha hb => W.add_mem _ _ ha hb
        zero_mem' := W.zero_mem
        algebraMap_mem' := fun c => (hW (ι₁ c)).mpr (hK₁V c) }
    have hle : Algebra.adjoin ↥K₁ {ξ} ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr (hξW W hW))
    have heq : (IntermediateField.adjoin ↥K₁ {ξ}).toSubalgebra = Algebra.adjoin ↥K₁ {ξ} :=
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hξK₁.isAlgebraic
    have he' : e ∈ (IntermediateField.adjoin ↥K₁ {ξ}).toSubalgebra := he
    rw [heq] at he'
    exact hle he'

  have hmaxW : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁)
      (m : ↥V₁), m ∈ maximalIdeal ↥V₁ → algebraMap ↥(K₁ ⊔ F₀) ↥E (m : ↥(K₁ ⊔ F₀)) ∈ W.nonunits := by
    intro W hW m hm
    rw [mem_nonunits_iff_eq_zero_or]
    refine ⟨(hW _).mpr m.2, ?_⟩
    by_cases hm0 : ((m : ↥(K₁ ⊔ F₀))) = 0
    · left; rw [hm0, map_zero]
    · right
      intro hinv
      rw [← map_inv₀, hW] at hinv
      exact (mem_maximalIdeal_iff_inv_not_mem V₁ m hm0).mp hm hinv

  have heval : ∀ a : Fin n → ↥K₁,
      Polynomial.aeval ξ (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) =
        ∑ i, algebraMap ↥K₁ ↥E (a i) * b i := by
    intro a
    simp only [map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, b]
  have hcoeff : ∀ (a : Fin n → ↥K₁),
      (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) = 0 → ∀ i, a i = 0 := by
    intro a h0 i
    have := congrArg (fun q : Polynomial ↥K₁ => q.coeff i) h0
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i (fun j _ hj => if_neg (fun h => hj (Fin.ext h).symm))
      (fun h => absurd (Finset.mem_univ i) h)] at this
    simpa using this

  let φ : (W : ValuationSubring ↥E) →
      (∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁) → ↥V₁ → ↥W :=
    fun W hW v => ⟨algebraMap ↥(K₁ ⊔ F₀) ↥E (v : ↥(K₁ ⊔ F₀)), (hW _).mpr v.2⟩
  let ξW : (W : ValuationSubring ↥E) →
      (∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁) → ↥W :=
    fun W hW => ⟨ξ, hξW W hW⟩
  have hφsub : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁) (u v : ↥V₁), φ W hW (u - v) = φ W hW u - φ W hW v := by
    intro W hW u v; apply Subtype.ext
    show algebraMap ↥(K₁ ⊔ F₀) ↥E ((u - v : ↥V₁) : ↥(K₁ ⊔ F₀)) = _
    rw [show ((u - v : ↥V₁) : ↥(K₁ ⊔ F₀)) = (u : ↥(K₁ ⊔ F₀)) - (v : ↥(K₁ ⊔ F₀)) from rfl, map_sub]
    rfl
  have hcoeS : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁) (v : Fin n → ↥V₁),
      ((∑ i, φ W hW (v i) * ξW W hW ^ (i : ℕ) : ↥W) : ↥E) =
        ∑ i, algebraMap ↥(K₁ ⊔ F₀) ↥E (v i : ↥(K₁ ⊔ F₀)) * b i := by
    intro W hW v
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rfl
  have hmaxS : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁) (v : Fin n → ↥V₁), (∀ i, v i ∈ maximalIdeal ↥V₁) →
      (∑ i, φ W hW (v i) * ξW W hW ^ (i : ℕ) : ↥W) ∈ maximalIdeal ↥W := by
    intro W hW v hv
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact hmaxW W hW _ (hv i)

  have hconst : ∀ c : Fin n → ↥V₁, ∃ a : Fin n → ↥K₁,
      ∀ i, c i - ⟨ι₁ (a i), hK₁V (a i)⟩ ∈ maximalIdeal ↥V₁ := by
    intro c
    choose a ha using fun i => hrat (c i)
    exact ⟨a, ha⟩
  have hφa : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁) (a : ↥K₁), ((φ W hW ⟨ι₁ a, hK₁V a⟩ : ↥W) : ↥E) = algebraMap ↥K₁ ↥E a :=
    fun W hW a => rfl

  have hind : ∀ (W : ValuationSubring ↥E)
      (hW : ∀ y : ↥(K₁ ⊔ F₀), algebraMap ↥(K₁ ⊔ F₀) ↥E y ∈ W ↔ y ∈ V₁) (c : Fin n → ↥V₁),
      (∑ i, algebraMap ↥(K₁ ⊔ F₀) ↥E (c i : ↥(K₁ ⊔ F₀)) * b i) ∈ W.nonunits →
      ∀ i, c i ∈ maximalIdeal ↥V₁ := by
    intro W hW c hs
    obtain ⟨a, ha⟩ := hconst c
    let a' : Fin n → ↥V₁ := fun i => ⟨ι₁ (a i), hK₁V (a i)⟩
    have hsW : (∑ i, φ W hW (c i) * ξW W hW ^ (i : ℕ) : ↥W) ∈ maximalIdeal ↥W := by
      rw [← ValuationSubring.coe_mem_nonunits_iff, hcoeS W hW]; exact hs
    have htW : (∑ i, φ W hW (a' i) * ξW W hW ^ (i : ℕ) : ↥W) ∈ maximalIdeal ↥W := by
      have : (∑ i, φ W hW (a' i) * ξW W hW ^ (i : ℕ) : ↥W) =
          (∑ i, φ W hW (c i) * ξW W hW ^ (i : ℕ)) - ∑ i, φ W hW (c i - a' i) * ξW W hW ^ (i : ℕ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hφsub W hW]; ring
      rw [this]
      exact Ideal.sub_mem _ hsW (hmaxS W hW _ ha)

    have htE : ((∑ i, φ W hW (a' i) * ξW W hW ^ (i : ℕ) : ↥W) : ↥E) =
        Polynomial.aeval ξ (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) := by
      rw [heval, hcoeS W hW]
      exact Finset.sum_congr rfl fun i _ => rfl
    have ht0 : Polynomial.aeval ξ (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) = 0 := by
      by_contra hne
      have hmem : Polynomial.aeval ξ (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) ∈
          IntermediateField.adjoin ↥K₁ {ξ} := by
        have h1 := Polynomial.aeval_mem_adjoin_singleton ↥K₁ ξ
          (p := ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ))
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hξK₁.isAlgebraic] at h1
        exact h1
      have hinv := hadjW W hW _ ((IntermediateField.adjoin ↥K₁ {ξ}).inv_mem hmem)
      have hne' : ((∑ i, φ W hW (a' i) * ξW W hW ^ (i : ℕ) : ↥W) : ↥E) ≠ 0 := by rw [htE]; exact hne
      have hunit : IsUnit (∑ i, φ W hW (a' i) * ξW W hW ^ (i : ℕ) : ↥W) := by
        rw [isUnit_iff_inv_mem W _ hne', htE]; exact hinv
      exact (IsLocalRing.mem_maximalIdeal _).mp htW hunit
    have hP0 : (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) = 0 := by
      by_contra hPne
      have hPx : Polynomial.aeval (x : F) (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) = 0 := by
        have := congrArg (IsScalarTower.toAlgHom ↥K₁ ↥E F) ht0
        rw [← Polynomial.aeval_algHom_apply, map_zero] at this
        exact this
      have h2 := minpoly.degree_le_of_ne_zero ↥K₁ (x : F) hPne hPx
      have h3 := Polynomial.degree_sum_fin_lt a
      have h4 : (minpoly ↥K₁ (x : F)).degree = n := by
        rw [hn]; exact Polynomial.degree_eq_natDegree (minpoly.ne_zero hxK₁)
      rw [h4] at h2
      exact absurd (lt_of_le_of_lt h2 h3) (lt_irrefl _)
    have ha0 : ∀ i, a i = 0 := hcoeff a hP0
    intro i
    have e2 : (⟨ι₁ (a i), hK₁V (a i)⟩ : ↥V₁) = 0 := by
      apply Subtype.ext
      show ι₁ (a i) = 0
      rw [ha0 i, map_zero]
    have := ha i
    rw [e2, sub_zero] at this
    exact this

  obtain ⟨W, hW, huniqW, hdvrW, hunifW, hresW⟩ := h_layer b hbW hind hdeg
  refine ⟨W, hW, huniqW, hdvrW, ⟨(hW _).mpr ϖ.2, hunifW⟩, hξW W hW, ?_⟩
  intro w
  obtain ⟨c, hc⟩ := hresW w
  obtain ⟨a, ha⟩ := hconst c
  let a' : Fin n → ↥V₁ := fun i => ⟨ι₁ (a i), hK₁V (a i)⟩
  let yW : ↥W := ∑ i, φ W hW (a' i) * ξW W hW ^ (i : ℕ)
  have hyF : ((yW : ↥E) : F) = ∑ i, ((a i : ↥K₁) : F) * (x : F) ^ (i : ℕ) := by
    show (((∑ i, φ W hW (a' i) * ξW W hW ^ (i : ℕ) : ↥W) : ↥E) : F) = _
    rw [hcoeS W hW]
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rfl
  have hyL : ((yW : ↥E) : F) ∈ L := by
    rw [hyF]
    refine L.sum_mem fun i _ => ?_
    exact L.mul_mem (hK₁L (a i).2) (pow_mem x.2 _)
  refine ⟨⟨_, hyL⟩, (yW : ↥E).2, ?_⟩

  have hdW : w - (∑ i, φ W hW (c i) * ξW W hW ^ (i : ℕ)) ∈ maximalIdeal ↥W := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    have : ((w - ∑ i, φ W hW (c i) * ξW W hW ^ (i : ℕ) : ↥W) : ↥E) =
        (w : ↥E) - ∑ i, algebraMap ↥(K₁ ⊔ F₀) ↥E (c i : ↥(K₁ ⊔ F₀)) * b i := by
      rw [← hcoeS W hW c]; rfl
    rw [this]; exact hc
  have hsum : w - yW = (w - ∑ i, φ W hW (c i) * ξW W hW ^ (i : ℕ)) +
      ∑ i, φ W hW (c i - a' i) * ξW W hW ^ (i : ℕ) := by
    show w - (∑ i, φ W hW (a' i) * ξW W hW ^ (i : ℕ)) = _
    have : ∀ i, φ W hW (c i - a' i) = φ W hW (c i) - φ W hW (a' i) := fun i => hφsub W hW _ _
    simp only [this, sub_mul, Finset.sum_sub_distrib]
    ring
  have hmem : w - yW ∈ maximalIdeal ↥W := by
    rw [hsum]; exact Ideal.add_mem _ hdW (hmaxS W hW _ ha)
  have := (ValuationSubring.coe_mem_nonunits_iff).mpr hmem

  have e : ((w - yW : ↥W) : ↥E) = (w : ↥E) - ⟨((yW : ↥E) : F), (yW : ↥E).2⟩ := rfl
  rw [e] at this
  exact this

end KFRatExt

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem KFRatExt.ratext_subfield
    {k F : Type} [Field k] [CharZero k] [Field F] [Algebra k F]
    (K₁ L F₀ : IntermediateField k F) (hK₁L : K₁ ≤ L) (hgen : L ⊔ F₀ = ⊤)
    (halg : ∀ x : ↥L, IsAlgebraic ↥K₁ (x : F))
    (V₁ : ValuationSubring ↥(K₁ ⊔ F₀))
    (hK₁V : ∀ x : ↥K₁, (⟨(x : F), (le_sup_left : K₁ ≤ K₁ ⊔ F₀) x.2⟩ : ↥(K₁ ⊔ F₀)) ∈ V₁)
    [IsDiscreteValuationRing ↥V₁]
    (hrat : ∀ v : ↥V₁, ∃ x : ↥K₁,
      v - ⟨⟨(x : F), (le_sup_left : K₁ ≤ K₁ ⊔ F₀) x.2⟩, hK₁V x⟩ ∈ maximalIdeal ↥V₁) :
    (∃! P : Place ↥L F, ∀ f : ↥(K₁ ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) ∧
    (∀ P : Place ↥L F, (∀ f : ↥(K₁ ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) → P.IsRational) := by
  classical
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible ↥V₁
  have hϖ : maximalIdeal ↥V₁ = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  refine KFRatExt.main_of_layers K₁ L F₀ hK₁L hgen halg V₁ ϖ hϖ (fun x => ?_)
  refine KFRatExt.layerSpec_of K₁ L F₀ hK₁L halg V₁ hK₁V hrat ϖ x ?_
  intro n b hbW hind hn
  haveI : CharZero ↥(K₁ ⊔ F₀) := charZero_of_injective_algebraMap (algebraMap k ↥(K₁ ⊔ F₀)).injective
  letI algK₁F₁ : Algebra ↥K₁ ↥(K₁ ⊔ F₀) :=
    (IntermediateField.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ F₀)).toRingHom.toAlgebra
  letI algK₁E : Algebra ↥K₁ ↥(KFRatExt.Lay K₁ F₀ (x : F)) :=
    ((algebraMap ↥(K₁ ⊔ F₀) ↥(KFRatExt.Lay K₁ F₀ (x : F))).comp (algebraMap ↥K₁ ↥(K₁ ⊔ F₀))).toAlgebra
  haveI : IsScalarTower ↥K₁ ↥(K₁ ⊔ F₀) ↥(KFRatExt.Lay K₁ F₀ (x : F)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥K₁ ↥(K₁ ⊔ F₀) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxF₁ : IsIntegral ↥(K₁ ⊔ F₀) (x : F) := ((halg x).isIntegral).tower_top
  haveI : FiniteDimensional ↥(K₁ ⊔ F₀) ↥(KFRatExt.Lay K₁ F₀ (x : F)) :=
    IntermediateField.adjoin.finiteDimensional hxF₁
  exact BDescRatExt.layer (k₀ := ↥K₁) V₁ (fun a => hK₁V a) ϖ hϖ b hbW hind hn

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    {k₀ L F : Type} [Field k₀] [Field L] [CharZero L] [Field F] [Algebra k₀ L] [Algebra k₀ F] [Algebra L F]
    [IsScalarTower k₀ L F]
    (F₀ : IntermediateField k₀ F) (K₁ : IntermediateField k₀ L)
    (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
    (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (V₁ : ValuationSubring ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀))
    (hK₁V : ∀ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀),
      (⟨algebraMap L F (x : L), hx⟩ : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ∈ V₁)
    [IsDiscreteValuationRing ↥V₁]
    (hrat : ∀ v : ↥V₁, ∃ (x : ↥K₁) (hx : algebraMap L F (x : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀),
      v - ⟨⟨algebraMap L F (x : L), hx⟩, hK₁V x hx⟩ ∈ maximalIdeal ↥V₁) :
    (∃! P : Place L F, ∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) ∧
    (∀ P : Place L F, (∀ f : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀), (f : F) ∈ P.toValuationSubring ↔ f ∈ V₁) → P.IsRational) := by
  classical

  let φ : L →ₐ[k₀] F := IsScalarTower.toAlgHom k₀ L F
  have hφ : ∀ y : L, φ y = algebraMap L F y := fun _ => rfl
  let L' : IntermediateField k₀ F := IntermediateField.adjoin k₀ (Set.range (algebraMap L F))
  have hL'1 : ∀ y : L, algebraMap L F y ∈ L' := fun y => IntermediateField.subset_adjoin k₀ _ ⟨y, rfl⟩
  have hL'le : L' ≤ φ.fieldRange := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have hL'2 : ∀ z : F, z ∈ L' → ∃ y : L, algebraMap L F y = z := by
    intro z hz
    obtain ⟨y, hy⟩ := (AlgHom.mem_fieldRange).mp (hL'le hz)
    exact ⟨y, hy⟩
  have hK₁'le : IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ≤ K₁.map φ := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  have hK₁'2 : ∀ z : F, z ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) → ∃ y : ↥K₁, algebraMap L F y = z := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := (IntermediateField.mem_map _).mp (hK₁'le hz)
    exact ⟨⟨y, hy⟩, hyz⟩
  have hK₁'1 : ∀ y : ↥K₁, algebraMap L F (y : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) :=
    fun y => IntermediateField.subset_adjoin k₀ _ ⟨y, y.2, rfl⟩
  have hK₁L : IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ≤ L' := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨y, _, rfl⟩
    exact hL'1 y

  have hle : IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ≤ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ := le_sup_left
  have halg' : ∀ x : ↥L', IsAlgebraic ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L))) (x : F) := by
    intro x
    obtain ⟨y, hy⟩ := hL'2 x x.2
    obtain ⟨p, hp0, hp⟩ := halg y
    let ψ : ↥K₁ →+* ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L))) :=
      { toFun := fun c => ⟨algebraMap L F (c : L), hK₁'1 c⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp) }
    have hψ : ∀ c : ↥K₁, ((ψ c : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)))) : F) = algebraMap L F (c : L) := fun c => rfl
    have hψinj : Function.Injective ψ := by
      intro a b hab
      have h' : algebraMap L F (a : L) = algebraMap L F (b : L) :=
        congrArg (fun z : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L))) => (z : F)) hab
      exact Subtype.ext ((algebraMap L F).injective h')
    refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff hψinj).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hy]
    have hcomp : (algebraMap ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L))) F).comp ψ = (algebraMap L F).comp (algebraMap ↥K₁ L) :=
      RingHom.ext fun c => rfl
    rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]
  have hK₁V' : ∀ x : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L))),
      (⟨(x : F), hle x.2⟩ :
        ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)) ∈ V₁ := by
    intro x
    obtain ⟨y, hy⟩ := hK₁'2 x x.2
    have hx : algebraMap L F (y : L) ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ := by rw [hy]; exact hle x.2
    have := hK₁V y hx
    convert this using 2
    exact hy.symm
  have hrat' : ∀ v : ↥V₁, ∃ x : ↥(IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L))),
      v - ⟨⟨(x : F), hle x.2⟩, hK₁V' x⟩ ∈
        maximalIdeal ↥V₁ := by
    intro v
    obtain ⟨y, hy, h⟩ := hrat v
    refine ⟨⟨algebraMap L F (y : L), hK₁'1 y⟩, ?_⟩
    convert h using 3

  haveI : CharZero k₀ := RingHom.charZero (algebraMap k₀ L)
  obtain ⟨⟨P', hP', huniq'⟩, hrat₀⟩ :=
    KFRatExt.ratext_subfield (IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L))) L' F₀ hK₁L hgen halg' V₁ hK₁V' hrat'

  let toL' : Place L F → Place ↥L' F := fun P =>
    ⟨P.toValuationSubring, fun x => by
      obtain ⟨y, hy⟩ := hL'2 x x.2
      have : algebraMap ↥L' F x = algebraMap L F y := hy.symm
      rw [this]; exact P.algebraMap_mem' y, P.ne_top', P.isPrincipalIdealRing'⟩
  have htoL' : ∀ P : Place L F, (toL' P).toValuationSubring = P.toValuationSubring := fun _ => rfl
  let P₀ : Place L F :=
    ⟨P'.toValuationSubring, fun a => P'.algebraMap_mem' ⟨algebraMap L F a, hL'1 a⟩, P'.ne_top',
      P'.isPrincipalIdealRing'⟩
  refine ⟨⟨P₀, hP', fun P hP => ?_⟩, fun P hP => ?_⟩
  · have hQ' : toL' P = P' := huniq' (toL' P) hP
    exact Place.ext ((htoL' P).symm.trans (congrArg Place.toValuationSubring hQ'))
  · have hQrat : (toL' P).IsRational := hrat₀ (toL' P) hP
    intro r
    obtain ⟨x, hx⟩ := hQrat r
    obtain ⟨y, hy⟩ := hL'2 x x.2
    refine ⟨y, ?_⟩
    rw [← hx, IsScalarTower.algebraMap_apply L ↥P.toValuationSubring P.ResidueField,
      IsScalarTower.algebraMap_apply ↥L' ↥(toL' P).toValuationSubring (toL' P).ResidueField]
    show IsLocalRing.residue ↥P.toValuationSubring (algebraMap L ↥P.toValuationSubring y) =
      IsLocalRing.residue ↥P.toValuationSubring (algebraMap ↥L' ↥(toL' P).toValuationSubring x)
    congr 1
    exact Subtype.ext hy

end S_AlgebraicCurve_Place_existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem
end P2MW
export P2MW.S_AlgebraicCurve_Place_existsUnique_forall_mem_iff_adjoin_sup_of_isAlgebraic_of_forall_exists_sub_mem (solution)
