-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.finiteDimensional_fractionRing_quotient_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ec696204-e688-5978-b89b-2522a6ca35c8

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finiteDimensional_fractionRing_quotient_of_not_mem

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace KappaFin

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

abbrev KC (C : Subring L) : Subfield L := Subfield.closure (C : Set L)

abbrev FN (N : Subring F) : Subfield F := Subfield.closure (N : Set F)

variable (C : Subring L) (N : Subring F)

@[reducible] def algCK : Algebra C (KC C) :=
  RingHom.toAlgebra ((C.subtype).codRestrict (KC C) (fun c => Subfield.subset_closure c.2))

theorem isScalarTower_CKL : letI := algCK C; IsScalarTower C (KC C) L :=
  letI := algCK C
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_CK_injective : letI := algCK C; Function.Injective (algebraMap C (KC C)) := by
  letI := algCK C
  intro a b h
  have h' : ((algebraMap C (KC C) a : KC C) : L) = ((algebraMap C (KC C) b : KC C) : L) := by rw [h]
  exact Subtype.ext h'

theorem algebraMap_mem_FN (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) (k : KC C) :
    algebraMap L F (k : L) ∈ FN N := by
  have hle : KC C ≤ (FN N).comap (algebraMap L F) := by
    rw [Subfield.closure_le]
    intro c hc
    exact Subfield.subset_closure (hCmem c hc)
  exact hle k.2

@[reducible] def algKFN (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) : Algebra (KC C) (FN N) :=
  RingHom.toAlgebra (((algebraMap L F).comp (algebraMap (KC C) L)).codRestrict (FN N)
    (algebraMap_mem_FN C N hCmem))

theorem isScalarTower_KFN (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N) :
    letI := algKFN C N hCmem; IsScalarTower (KC C) (FN N) F :=
  letI := algKFN C N hCmem
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem exists_fraction_of_mem_FN (x : F) (hx : x ∈ FN N) : ∃ r₀ s₀ : N, s₀ ≠ 0 ∧ x * s₀ = r₀ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hy hz
  by_cases hz0 : z = 0
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    simp [hz0]
  · refine ⟨⟨y, hy⟩, ⟨z, hz⟩, fun h => hz0 (congrArg Subtype.val h), ?_⟩
    show y / z * z = y
    rw [div_mul_cancel₀ y hz0]

theorem exists_fraction_of_mem_KC (x : L) (hx : x ∈ KC C) : ∃ r₀ s₀ : C, s₀ ≠ 0 ∧ x * s₀ = r₀ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hy hz
  by_cases hz0 : z = 0
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    simp [hz0]
  · refine ⟨⟨y, hy⟩, ⟨z, hz⟩, fun h => hz0 (congrArg Subtype.val h), ?_⟩
    show y / z * z = y
    rw [div_mul_cancel₀ y hz0]

theorem sum_smul_eq_zero_imp
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    {ι : Type*} [Fintype ι] (c : ι → L) (hc : LinearIndependent (KC C) c)
    (x : ι → F) (hx : ∀ i, x i ∈ FN N) (hrel : ∑ i, c i • x i = 0) : ∀ i, x i = 0 := by
  classical

  choose r s hs hxs using fun i => exists_fraction_of_mem_FN N (x i) (hx i)
  set D : N := ∏ i, s i with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs i

  have hxD : ∀ i, x i * (D : F) = ((r i * ∏ j ∈ Finset.univ.erase i, s j : N) : F) := by
    intro i
    have : (D : F) = (s i : F) * ((∏ j ∈ Finset.univ.erase i, s j : N) : F) := by
      rw [hD, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)]
      push_cast
      rfl
    rw [this, ← mul_assoc, hxs i]
    push_cast
    rfl

  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  have hcC : LinearIndependent C c := by
    letI := algCK C
    haveI := isScalarTower_CKL C
    haveI : FaithfulSMul C (KC C) := (faithfulSMul_iff_algebraMap_injective C (KC C)).mpr
      (fun a b h => Subtype.ext (congrArg Subtype.val h :))
    exact hc.restrict_scalars' C
  have hcC' : LinearIndependent C (c ∘ e.symm) := hcC.comp _ e.symm.injective
  have hrel' : ∑ k, (c ∘ e.symm) k • (((fun k => r (e.symm k) * ∏ j ∈ Finset.univ.erase (e.symm k), s j) k : N) : F) = 0 := by
    have h1 : ∑ i, c i • (x i * (D : F)) = 0 := by
      simp_rw [← smul_mul_assoc, ← Finset.sum_mul, hrel, zero_mul]
    rw [← e.symm.sum_comp] at h1
    simpa only [Function.comp, hxD] using h1
  have hall := hld _ (c ∘ e.symm) (fun k => r (e.symm k) * ∏ j ∈ Finset.univ.erase (e.symm k), s j) hcC' hrel'
  intro i
  have hi := hall (e i)
  simp only [Equiv.symm_apply_apply] at hi
  have hprod : (∏ j ∈ Finset.univ.erase i, s j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hs j
  have hri : r i = 0 := by
    rcases mul_eq_zero.mp hi with h | h
    · exact h
    · exact absurd h hprod
  have : x i * (s i : F) = 0 := by rw [hxs i, hri]; rfl
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd (Subtype.ext h : s i = 0) (hs i)

section LinDisj

variable (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N)

def subalgFN : Subalgebra (KC C) F :=
  { (FN N).toSubring with
    algebraMap_mem' := fun k => algebraMap_mem_FN C N hCmem k }

@[scoped simp] theorem mem_subalgFN (x : F) : x ∈ subalgFN C N hCmem ↔ x ∈ FN N := Iff.rfl

def subalgL : Subalgebra (KC C) F := (IsScalarTower.toAlgHom (KC C) L F).range

def equivL : L ≃ₐ[KC C] subalgL (F := F) C :=
  AlgEquiv.ofInjective (IsScalarTower.toAlgHom (KC C) L F) (algebraMap L F).injective

@[scoped simp] theorem coe_equivL (l : L) : ((equivL (F := F) C l : subalgL (F := F) C) : F) = algebraMap L F l := rfl

theorem linearDisjoint
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0) :
    (subalgL (F := F) C).LinearDisjoint (subalgFN C N hCmem) := by
  classical
  let b := Module.Basis.ofVectorSpace (KC C) L
  let a : Module.Basis _ (KC C) (subalgL (F := F) C) := b.map (equivL (F := F) C).toLinearEquiv
  refine Subalgebra.LinearDisjoint.of_basis_left _ _ a ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi

  have hrel : ∑ j : s, (b j : L) • ((g j : subalgFN C N hCmem) : F) = 0 := by
    have : ∑ j ∈ s, g j • ((subalgL (F := F) C).val ∘ a) j = ∑ j ∈ s, (b j : L) • ((g j : subalgFN C N hCmem) : F) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      show ((g j : subalgFN C N hCmem) : F) * (((a j) : subalgL (F := F) C) : F) = _
      simp only [a, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, coe_equivL]
      rw [Algebra.smul_def, mul_comm]
    rw [this] at hsum
    rw [← hsum, ← Finset.sum_coe_sort s]
  have hb : LinearIndependent (KC C) (fun j : s => b j) := b.linearIndependent.comp _ Subtype.val_injective
  have := sum_smul_eq_zero_imp C N hld (fun j : s => b j) hb (fun j => ((g j : subalgFN C N hCmem) : F))
    (fun j => (g j).2) hrel ⟨i, hi⟩
  exact Subtype.ext this

theorem linearIndependent_L
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    {ι : Type*} (v : ι → FN N) (hv : letI := algKFN C N hCmem; LinearIndependent (KC C) v) :
    LinearIndependent L (fun i => (v i : F)) := by
  classical
  letI := algKFN C N hCmem
  have H := (linearDisjoint C N hCmem hld).symm

  let v' : ι → subalgFN C N hCmem := fun i => ⟨v i, (v i).2⟩
  have hv' : LinearIndependent (KC C) v' := by
    rw [linearIndependent_iff'] at hv ⊢
    intro s g hsum
    apply hv s g
    apply Subtype.ext
    have := congrArg (fun z : subalgFN C N hCmem => (z : F)) hsum
    simp only [Subalgebra.coe_zero] at this
    rw [ZeroMemClass.coe_zero, ← this]
    simp only [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ((g j • v j : FN N) : F) = ((g j • v' j : subalgFN C N hCmem) : F)
    rw [Subalgebra.coe_smul, Algebra.smul_def, Algebra.smul_def]
    rfl
  have key : LinearIndependent (subalgL (F := F) C) ((subalgFN C N hCmem).val ∘ v') :=
    H.linearIndependent_left_of_flat hv'
  rw [linearIndependent_iff'] at key ⊢
  intro s l hsum i hi
  have h := key s (fun j => equivL (F := F) C (l j)) ?_ i hi
  · exact (equivL (F := F) C).injective (by rw [map_zero]; exact h)
  · rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ((equivL (F := F) C (l j) : subalgL (F := F) C) : F) * (v j : F) = l j • (v j : F)
    rw [coe_equivL, Algebra.smul_def]

end LinDisj

section Descent

variable (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N)

def φC : C →+* N :=
  ((algebraMap L F).comp C.subtype).codRestrict N (fun c => hCmem c c.2)

@[scoped simp] theorem coe_φC (c : C) : ((φC C N hCmem c : N) : F) = algebraMap L F c := rfl

theorem mem_KC_of_algebraMap_mem_FN
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    (c : L) (hc : algebraMap L F c ∈ FN N) : c ∈ KC C := by
  obtain ⟨a, b, hb, hab⟩ := exists_fraction_of_mem_FN N (algebraMap L F c) hc
  have hrel : ∑ i, (![c, -1] : Fin 2 → L) i • (((![b, a] : Fin 2 → N) i : N) : F) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Algebra.smul_def, hab, neg_one_smul, add_neg_cancel]
  have hnotli : ¬ LinearIndependent C (![c, -1] : Fin 2 → L) := by
    intro hli
    have := hld 2 ![c, -1] ![b, a] hli hrel 0
    exact hb (by simpa using this)
  rw [LinearIndependent.pair_iff] at hnotli
  push Not at hnotli
  obtain ⟨s, t, hst, hst0⟩ := hnotli
  have hs0 : (s : L) ≠ 0 := by
    intro hs
    have hsz : s = 0 := Subtype.ext hs
    apply hst0 hsz
    rw [hsz, zero_smul, zero_add, smul_neg, neg_eq_zero, Subring.smul_def, smul_eq_mul, mul_one] at hst
    exact Subtype.ext hst
  have hct : c = (t : L) / (s : L) := by
    rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, mul_neg, mul_one] at hst
    field_simp
    linear_combination hst
  rw [hct]
  exact div_mem (Subfield.subset_closure t.2) (Subfield.subset_closure s.2)

open Polynomial IntermediateField in

theorem finiteDimensional_adjoin_FN
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    (t : FN N) (htL : Transcendental L (t : F))
    [FiniteDimensional L⟮(t : F)⟯ F] :
    letI := algKFN C N hCmem
    Transcendental (KC C) t → FiniteDimensional (KC C)⟮t⟯ (FN N) := by
  letI := algKFN C N hCmem
  haveI := isScalarTower_KFN C N hCmem
  intro htK
  classical
  set n := Module.finrank L⟮(t : F)⟯ F with hn
  have hrank : Module.rank (KC C)⟮t⟯ (FN N) ≤ n := by
    apply rank_le
    intro s hs

    suffices hsL : LinearIndependent L⟮(t : F)⟯ (fun i : s => ((i : FN N) : F)) by
      have := hsL.fintype_card_le_finrank
      simpa using this
    rw [Fintype.linearIndependent_iff]
    intro g hsum

    have hfrac : ∀ j : s, ∃ p q : L[X], q ≠ 0 ∧ ((g j : L⟮(t : F)⟯) : F) * aeval (t : F) q = aeval (t : F) p := by
      intro j
      obtain ⟨r, q, hrq⟩ := (mem_adjoin_simple_iff L ((g j : L⟮(t : F)⟯) : F)).mp (g j).2
      by_cases hq : q = 0
      · refine ⟨0, 1, one_ne_zero, ?_⟩
        simp [hrq, hq]
      · refine ⟨r, q, hq, ?_⟩
        have hq0 : aeval (t : F) q ≠ 0 := fun h => hq ((transcendental_iff.mp htL) q h)
        rw [hrq, div_mul_cancel₀ _ hq0]
    choose p q hq hpq using hfrac
    have haq : ∀ j, aeval (t : F) (q j) ≠ 0 := fun j h => hq j ((transcendental_iff.mp htL) _ h)

    set Q : L[X] := ∏ j, q j with hQ
    have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hq j
    let P : s → L[X] := fun j => p j * ∏ k ∈ Finset.univ.erase j, q k
    have hgP : ∀ j, ((g j : L⟮(t : F)⟯) : F) * aeval (t : F) Q = aeval (t : F) (P j) := by
      intro j
      have : Q = q j * ∏ k ∈ Finset.univ.erase j, q k := by
        rw [hQ, Finset.mul_prod_erase Finset.univ q (Finset.mem_univ j)]
      rw [this, map_mul, ← mul_assoc, hpq j, ← map_mul]

    have hrelP : ∑ j, aeval (t : F) (P j) * ((j : FN N) : F) = 0 := by
      have : (∑ j, (g j) • ((j : FN N) : F)) * aeval (t : F) Q = 0 := by rw [hsum, zero_mul]
      rw [Finset.sum_mul] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hgP j]
      show _ = ((g j : L⟮(t : F)⟯) : F) * ((j : FN N) : F) * _
      ring

    set D : ℕ := (Finset.univ.sup fun j => (P j).natDegree) + 1 with hD
    have hdeg : ∀ j, (P j).natDegree < D := fun j =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (P j).natDegree) (Finset.mem_univ j))
    have hexp : ∀ j, aeval (t : F) (P j) = ∑ m : Fin D, (P j).coeff m • (t : F) ^ (m : ℕ) := by
      intro j
      rw [aeval_eq_sum_range' (hdeg j), ← Fin.sum_univ_eq_sum_range]

    let w : s × Fin D → FN N := fun jm => t ^ (jm.2 : ℕ) * (jm.1 : FN N)
    have hw : LinearIndependent (KC C) w := by
      rw [Fintype.linearIndependent_iff]
      intro k hk jm

      have hk' : ∑ j : s, (∑ m : Fin D, k (j, m) • t ^ (m : ℕ)) * (j : FN N) = 0 := by
        rw [← hk, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_mul_assoc]
      have hmem : ∀ j : s, (∑ m : Fin D, k (j, m) • t ^ (m : ℕ)) ∈ (KC C)⟮t⟯ := fun j =>
        sum_mem fun m _ => IntermediateField.smul_mem _ (pow_mem (mem_adjoin_simple_self _ t) _)
      let e : s → (KC C)⟮t⟯ := fun j => ⟨_, hmem j⟩
      have he : ∀ j, e j = 0 := by
        rw [Fintype.linearIndependent_iff] at hs
        apply hs e
        rw [← hk']
        rfl

      have hpoly : ∀ j : s, (∑ m : Fin D, monomial (m : ℕ) (k (j, m)) : (KC C)[X]) = 0 := by
        intro j
        apply (transcendental_iff.mp htK)
        rw [map_sum]
        have := congrArg (fun z : (KC C)⟮t⟯ => (z : FN N)) (he j)
        simp only [e, ZeroMemClass.coe_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [aeval_monomial, Algebra.smul_def]
      have := congrArg (fun z : (KC C)[X] => z.coeff (jm.2 : ℕ)) (hpoly jm.1)
      simp only [finsetSum_coeff, coeff_monomial, coeff_zero] at this
      rw [Finset.sum_eq_single jm.2] at this
      · simpa using this
      · intro m _ hm
        rw [if_neg]
        exact fun h => hm (Fin.ext h)
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hwL := linearIndependent_L C N hCmem hld w hw
    rw [Fintype.linearIndependent_iff] at hwL
    have hcoeff : ∀ jm : s × Fin D, (P jm.1).coeff (jm.2 : ℕ) = 0 := by
      apply hwL
      rw [Fintype.sum_prod_type, ← hrelP]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hexp j, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      show (P j).coeff (m : ℕ) • (((t ^ (m : ℕ) * (j : FN N) : FN N)) : F) =
        (P j).coeff (m : ℕ) • (t : F) ^ (m : ℕ) * ((j : FN N) : F)
      push_cast
      rw [smul_mul_assoc]
    have hP0 : ∀ j, P j = 0 := by
      intro j
      ext m
      rw [coeff_zero]
      by_cases hm : m < D
      · exact hcoeff (j, ⟨m, hm⟩)
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg j) (not_lt.mp hm))
    intro j
    have hp0 : p j = 0 := by
      have := hP0 j
      simp only [P] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => hq k)
    have : ((g j : L⟮(t : F)⟯) : F) = 0 := by
      have h := hpq j
      rw [hp0, map_zero] at h
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h (haq j)
    exact Subtype.ext this
  have hlt : Module.rank (KC C)⟮t⟯ (FN N) < Cardinal.aleph0 :=
    lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := n))
  haveI : Module.Free (KC C)⟮t⟯ (FN N) := Module.Free.of_divisionRing _ _
  exact Module.rank_lt_aleph0_iff.mp hlt

end Descent

section Poly

variable (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N)

def toFN : N →+* FN N := (N.subtype).codRestrict (FN N) (fun x => Subfield.subset_closure x.2)

@[scoped simp] theorem coe_toFN (x : N) : ((toFN N x : FN N) : F) = (x : F) := rfl

theorem toFN_injective : Function.Injective (toFN N) := fun a b h =>
  Subtype.ext (congrArg (fun z : FN N => (z : F)) h)

open Polynomial in

theorem exists_C_mul_eq_map (P : (KC C)[X]) :
    letI := algCK C
    ∃ (Z : C) (Q : C[X]), Z ≠ 0 ∧
      Polynomial.C (algebraMap C (KC C) Z) * P = Q.map (algebraMap C (KC C)) := by
  letI := algCK C
  classical
  set n := P.natDegree + 1 with hn
  choose y z hz hyz using fun j : Fin n => exists_fraction_of_mem_KC C (P.coeff j : L) (P.coeff j).2
  refine ⟨∏ j, z j, ∑ j : Fin n, monomial (j : ℕ) (y j * ∏ k ∈ Finset.univ.erase j, z k),
    Finset.prod_ne_zero_iff.mpr fun j _ => hz j, ?_⟩
  refine Polynomial.ext fun m => ?_
  rw [coeff_C_mul, coeff_map, finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases hm : m < n
  · rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]
    · rw [if_pos rfl]
      apply Subtype.ext
      show ((∏ j, z j : C) : L) * (P.coeff m : L) = ((y ⟨m, hm⟩ * ∏ k ∈ Finset.univ.erase ⟨m, hm⟩, z k : C) : L)
      rw [← Finset.mul_prod_erase Finset.univ z (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
      push_cast
      rw [← hyz ⟨m, hm⟩]
      ring
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hPm : P.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hPm, mul_zero, Finset.sum_eq_zero, map_zero]
    intro j _
    rw [if_neg]
    intro h
    apply hm
    rw [← h]
    exact j.2

open Polynomial in

theorem aeval_map_eq (Q : (C : Type _)[X]) (x : N) :
    letI := algKFN C N hCmem
    letI := algCK C
    aeval (toFN N x) (Q.map (algebraMap C (KC C))) = toFN N (Q.eval₂ (φC C N hCmem) x) := by
  letI := algKFN C N hCmem
  letI := algCK C
  rw [aeval_def, eval₂_map, hom_eval₂]
  congr 1

open Polynomial in

theorem eval₂_sub_mem (𝔭 : Ideal N) (t : N) (ht : t ∈ 𝔭) (Q : (C : Type _)[X]) :
    Q.eval₂ (φC C N hCmem) t - φC C N hCmem (Q.coeff 0) ∈ 𝔭 := by
  have h := congrArg (fun R => R.eval₂ (φC C N hCmem) t) (divX_mul_X_add Q)
  simp only [eval₂_add, eval₂_mul, eval₂_X, eval₂_C] at h
  rw [← h, add_sub_cancel_right]
  exact 𝔭.mul_mem_left _ ht

variable (𝔭 : Ideal N) (hC𝔭 : ∀ c : C, φC C N hCmem c ∈ 𝔭 → c = 0)

open Polynomial in
include hC𝔭 in

theorem transcendental_K [𝔭.IsPrime] (t : N) (ht : t ∈ 𝔭) (ht0 : t ≠ 0) :
    letI := algKFN C N hCmem
    Transcendental (KC C) (toFN N t) := by
  letI := algKFN C N hCmem
  letI := algCK C
  intro halg
  have hint : IsIntegral (KC C) (toFN N t) := halg.isIntegral
  have ht'0 : toFN N t ≠ 0 := fun h => ht0 (toFN_injective N (h.trans (map_zero _).symm))
  have hq0 : (minpoly (KC C) (toFN N t)).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint ht'0
  obtain ⟨Z, Q, hZ, hZQ⟩ := exists_C_mul_eq_map C (minpoly (KC C) (toFN N t))
  have heval : toFN N (Q.eval₂ (φC C N hCmem) t) = 0 := by
    rw [← aeval_map_eq C N hCmem Q t, ← hZQ, map_mul, minpoly.aeval, mul_zero]
  have hmem : φC C N hCmem (Q.coeff 0) ∈ 𝔭 := by
    have h1 : Q.eval₂ (φC C N hCmem) t = 0 := toFN_injective N (heval.trans (map_zero _).symm)
    have h2 := eval₂_sub_mem C N hCmem 𝔭 t ht Q
    rw [h1, zero_sub] at h2
    exact (Ideal.neg_mem_iff _).mp h2
  have hQ0 : Q.coeff 0 = 0 := hC𝔭 _ hmem
  have := congrArg (fun R : (KC C)[X] => R.coeff 0) hZQ
  simp only [coeff_C_mul, coeff_map, hQ0, map_zero] at this
  rcases mul_eq_zero.mp this with h | h
  · exact hZ ((map_eq_zero_iff _ (algebraMap_CK_injective C)).mp h)
  · exact hq0 h

open Polynomial in

theorem transcendental_L
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    (t : FN N) (htK : letI := algKFN C N hCmem; Transcendental (KC C) t) :
    Transcendental L (t : F) := by
  letI := algKFN C N hCmem
  classical
  rintro ⟨p, hp0, hp⟩
  set n := p.natDegree + 1 with hn

  have hw : LinearIndependent (KC C) (fun i : Fin n => t ^ (i : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro k hk i
    have hpoly : (∑ m : Fin n, monomial (m : ℕ) (k m) : (KC C)[X]) = 0 := by
      apply (transcendental_iff.mp htK)
      rw [map_sum, ← hk]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [aeval_monomial, Algebra.smul_def]
    have := congrArg (fun z : (KC C)[X] => z.coeff (i : ℕ)) hpoly
    simp only [finsetSum_coeff, coeff_monomial, coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro m _ hm
      rw [if_neg]
      exact fun h => hm (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hwL := linearIndependent_L C N hCmem hld _ hw
  rw [Fintype.linearIndependent_iff] at hwL
  have hcoeff := hwL (fun i : Fin n => p.coeff i) (by
    have := aeval_eq_sum_range' (lt_add_one p.natDegree) (t : F)
    rw [← Fin.sum_univ_eq_sum_range] at this
    rw [← hp, this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp)
  have hlead := hcoeff ⟨p.natDegree, lt_add_one _⟩
  exact hp0 (leadingCoeff_eq_zero.mp hlead)

open Polynomial in

theorem eq_zero_of_sum_eval₂_mul_eq_zero (t : N) (ht : t ∈ 𝔭) (ht0 : t ≠ 0)
    {m : ℕ} (d : Fin m → N)
    (hd : ∀ c : Fin m → C, (∑ i, φC C N hCmem (c i) * d i) ∈ 𝔭 → ∀ i, c i = 0) :
    ∀ (D : ℕ) (Q : Fin m → (C : Type _)[X]), (∀ i, (Q i).natDegree ≤ D) →
      ∑ i, (Q i).eval₂ (φC C N hCmem) t * d i = 0 → ∀ i, Q i = 0 := by
  intro D
  induction D with
  | zero =>
    intro Q hQ hsum i
    have hconst : ∀ i, Q i = Polynomial.C ((Q i).coeff 0) := fun i => eq_C_of_natDegree_le_zero (hQ i)
    have hmem : (∑ i, φC C N hCmem ((Q i).coeff 0) * d i) ∈ 𝔭 := by
      have : ∑ i, φC C N hCmem ((Q i).coeff 0) * d i = ∑ i, (Q i).eval₂ (φC C N hCmem) t * d i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_rhs => rw [hconst i]
        rw [eval₂_C]
      rw [this, hsum]
      exact 𝔭.zero_mem
    have h0 := hd _ hmem i
    rw [hconst i, h0, map_zero]
  | succ D ih =>
    intro Q hQ hsum

    have hmem : (∑ i, φC C N hCmem ((Q i).coeff 0) * d i) ∈ 𝔭 := by
      have hdiff : (∑ i, ((Q i).eval₂ (φC C N hCmem) t - φC C N hCmem ((Q i).coeff 0)) * d i) ∈ 𝔭 :=
        Ideal.sum_mem _ fun i _ => 𝔭.mul_mem_right _ (eval₂_sub_mem C N hCmem 𝔭 t ht (Q i))
      have : ∑ i, φC C N hCmem ((Q i).coeff 0) * d i =
          ∑ i, (Q i).eval₂ (φC C N hCmem) t * d i - ∑ i, ((Q i).eval₂ (φC C N hCmem) t - φC C N hCmem ((Q i).coeff 0)) * d i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [this, hsum, zero_sub]
      exact (Ideal.neg_mem_iff _).mpr hdiff
    have h0 : ∀ i, (Q i).coeff 0 = 0 := hd _ hmem
    have hdecomp : ∀ i, Q i = (Q i).divX * X := fun i => by
      conv_lhs => rw [← divX_mul_X_add (Q i), h0 i, map_zero, add_zero]

    have hsum' : ∑ i, ((Q i).divX).eval₂ (φC C N hCmem) t * d i = 0 := by
      have : (∑ i, ((Q i).divX).eval₂ (φC C N hCmem) t * d i) * t = 0 := by
        rw [← hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_rhs => rw [hdecomp i]
        rw [eval₂_mul, eval₂_X]
        ring
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h ht0
    have hdeg : ∀ i, ((Q i).divX).natDegree ≤ D := fun i => by
      rw [natDegree_divX_eq_natDegree_tsub_one]
      have := hQ i
      omega
    have hall := ih (fun i => (Q i).divX) hdeg hsum'
    intro i
    have hi := hall i
    rw [hdecomp i, hi, zero_mul]

end Poly

section Core

variable (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N)
variable (𝔭 : Ideal N) (hC𝔭 : ∀ c : C, φC C N hCmem c ∈ 𝔭 → c = 0)

open Polynomial IntermediateField in

theorem card_le_finrank (t : N) (ht : t ∈ 𝔭) (ht0 : t ≠ 0)
    (htK : letI := algKFN C N hCmem; Transcendental (KC C) (toFN N t))
    (hFD : letI := algKFN C N hCmem; FiniteDimensional (KC C)⟮toFN N t⟯ (FN N))
    {m : ℕ} (d : Fin m → N)
    (hd : ∀ c : Fin m → C, (∑ i, φC C N hCmem (c i) * d i) ∈ 𝔭 → ∀ i, c i = 0) :
    letI := algKFN C N hCmem
    m ≤ Module.finrank (KC C)⟮toFN N t⟯ (FN N) := by
  letI := algKFN C N hCmem
  letI := algCK C
  haveI := hFD
  classical
  set t' := toFN N t with ht'
  suffices hli : LinearIndependent (KC C)⟮t'⟯ (fun i => toFN N (d i)) by
    simpa using hli.fintype_card_le_finrank
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  have haq0 : ∀ q : (KC C)[X], q ≠ 0 → aeval t' q ≠ 0 := fun q hq h => hq ((transcendental_iff.mp htK) q h)

  have hfrac : ∀ i, ∃ p q : (KC C)[X], q ≠ 0 ∧ ((g i : (KC C)⟮t'⟯) : FN N) * aeval t' q = aeval t' p := by
    intro i
    obtain ⟨r, q, hrq⟩ := (mem_adjoin_simple_iff (KC C) ((g i : (KC C)⟮t'⟯) : FN N)).mp (g i).2
    by_cases hq : q = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      simp [hrq, hq]
    · refine ⟨r, q, hq, ?_⟩
      rw [hrq, div_mul_cancel₀ _ (haq0 q hq)]
  choose p q hq hpq using hfrac

  let P : Fin m → (KC C)[X] := fun i => p i * ∏ k ∈ Finset.univ.erase i, q k
  have hgP : ∀ i, ((g i : (KC C)⟮t'⟯) : FN N) * aeval t' (∏ k, q k) = aeval t' (P i) := by
    intro i
    rw [← Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i), map_mul, ← mul_assoc, hpq i, ← map_mul]
  have hrelP : ∑ i, aeval t' (P i) * toFN N (d i) = 0 := by
    have : (∑ i, (g i) • toFN N (d i)) * aeval t' (∏ k, q k) = 0 := by rw [hsum, zero_mul]
    rw [Finset.sum_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hgP i]
    show _ = ((g i : (KC C)⟮t'⟯) : FN N) * toFN N (d i) * _
    ring

  choose Z Qt hZ hZQ using fun i => exists_C_mul_eq_map C (P i)
  let R : Fin m → (C : Type _)[X] := fun i => Polynomial.C (∏ k ∈ Finset.univ.erase i, Z k) * Qt i
  have hR : ∀ i, Polynomial.C (algebraMap C (KC C) (∏ k, Z k)) * P i = (R i).map (algebraMap C (KC C)) := by
    intro i
    simp only [R, Polynomial.map_mul, map_C, ← hZQ i]
    rw [← Finset.mul_prod_erase Finset.univ Z (Finset.mem_univ i), map_mul, map_mul, mul_assoc,
      mul_left_comm]

  have hrelR : ∑ i, (R i).eval₂ (φC C N hCmem) t * d i = 0 := by
    apply toFN_injective N
    rw [map_sum, map_zero]
    have : (∑ i, aeval t' (P i) * toFN N (d i)) * aeval t' (Polynomial.C (algebraMap C (KC C) (∏ k, Z k))) = 0 := by
      rw [hrelP, zero_mul]
    rw [← this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← aeval_map_eq C N hCmem (R i) t, ← hR i, map_mul]
    ring

  have hRz := eq_zero_of_sum_eval₂_mul_eq_zero C N hCmem 𝔭 t ht ht0 d hd
    (Finset.univ.sup fun i => (R i).natDegree) R (fun i => Finset.le_sup (f := fun i => (R i).natDegree) (Finset.mem_univ i)) hrelR
  intro i
  have hQt : Qt i = 0 := by
    have h := hRz i
    simp only [R] at h
    rcases mul_eq_zero.mp h with h | h
    · rw [Polynomial.C_eq_zero] at h
      exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => hZ k)
    · exact h
  have hP : P i = 0 := by
    have h := hZQ i
    rw [hQt, Polynomial.map_zero] at h
    rcases mul_eq_zero.mp h with h | h
    · rw [Polynomial.C_eq_zero] at h
      exact absurd ((map_eq_zero_iff _ (algebraMap_CK_injective C)).mp h) (hZ i)
    · exact h
  have hp : p i = 0 := by
    have h := hP
    simp only [P] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => hq k)
  have : ((g i : (KC C)⟮t'⟯) : FN N) = 0 := by
    have h := hpq i
    rw [hp, map_zero] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (haq0 _ (hq i))
  exact Subtype.ext this

open IntermediateField in
include hC𝔭 in

theorem core [𝔭.IsPrime]
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → N), LinearIndependent C c →
      ∑ i, c i • ((a i : N) : F) = 0 → ∀ i, a i = 0)
    (h𝔭0 : 𝔭 ≠ ⊥)
    (hfin : ∀ x : F, Transcendental L x → FiniteDimensional L⟮x⟯ F) :
    ∃ n : ℕ, ∀ (m : ℕ) (d : Fin m → N),
      (∀ c : Fin m → C, (∑ i, φC C N hCmem (c i) * d i) ∈ 𝔭 → ∀ i, c i = 0) → m ≤ n := by
  letI := algKFN C N hCmem
  obtain ⟨t, ht𝔭, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭0
  have htK : Transcendental (KC C) (toFN N t) := transcendental_K C N hCmem 𝔭 hC𝔭 t ht𝔭 ht0
  have htL : Transcendental L ((toFN N t : FN N) : F) := transcendental_L C N hCmem hld (toFN N t) htK
  haveI : FiniteDimensional L⟮((toFN N t : FN N) : F)⟯ F := hfin _ htL
  have hFD : FiniteDimensional (KC C)⟮toFN N t⟯ (FN N) := finiteDimensional_adjoin_FN C N hCmem hld (toFN N t) htL htK
  exact ⟨_, fun m d hd => card_le_finrank C N hCmem 𝔭 t ht𝔭 ht0 htK hFD d hd⟩

end Core

section Adapters

variable (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ N)

theorem eq_zero_of_φC_mem [IsDomain C] [IsDiscreteValuationRing C]
    (𝔭 : Ideal N) [𝔭.IsPrime] (ϖ : C) (hϖu : ¬ IsUnit ϖ) (hϖ𝔭 : φC C N hCmem ϖ ∉ 𝔭)
    (c : C) (hc : φC C N hCmem c ∈ 𝔭) : c = 0 := by
  by_contra hc0
  let I : Ideal C := 𝔭.comap (φC C N hCmem)
  have hI : I.IsPrime := Ideal.IsPrime.comap _
  have hcI : c ∈ I := hc
  have hI0 : I ≠ ⊥ := fun h => hc0 (by rw [h] at hcI; exact hcI)
  have hImax : I.IsMaximal := hI.isMaximal hI0
  have hIeq : I = IsLocalRing.maximalIdeal C := IsLocalRing.eq_maximalIdeal hImax
  have hϖI : ϖ ∈ I := by rw [hIeq]; exact hϖu
  exact hϖ𝔭 hϖI

theorem finiteDimensional_of_bound (𝔭 : Ideal N) [𝔭.IsPrime] (n : ℕ)
    (hbound : ∀ (m : ℕ) (d : Fin m → N),
      (∀ c : Fin m → C, (∑ i, φC C N hCmem (c i) * d i) ∈ 𝔭 → ∀ i, c i = 0) → m ≤ n)
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    (κ : Type*) [Field κ] [Algebra (N ⧸ 𝔭) κ] [IsFractionRing (N ⧸ 𝔭) κ] [Algebra K κ]
    (hcompat : ∀ c : C, algebraMap K κ (algebraMap C K c) =
      algebraMap (N ⧸ 𝔭) κ (Ideal.Quotient.mk 𝔭 (φC C N hCmem c))) :
    FiniteDimensional K κ := by
  classical
  have hrank : Module.rank K κ ≤ n := by
    apply rank_le
    intro s hs
    set m := s.card with hm
    let x : Fin m → κ := fun i => ((s.equivFin.symm i : s) : κ)
    have hx : LinearIndependent K x := hs.comp _ s.equivFin.symm.injective

    have hfr := fun i => IsFractionRing.div_surjective (A := N ⧸ 𝔭) (x i)
    choose a b hb hab using hfr
    have hb0 : ∀ i, algebraMap (N ⧸ 𝔭) κ (b i) ≠ 0 := fun i =>
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hb i)
    set Bd : N ⧸ 𝔭 := ∏ i, b i with hBd_def
    have hBd : Bd ∈ nonZeroDivisors (N ⧸ 𝔭) := prod_mem fun i _ => hb i
    have hBd0 : algebraMap (N ⧸ 𝔭) κ Bd ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hBd
    let a' : Fin m → N ⧸ 𝔭 := fun i => a i * ∏ j ∈ Finset.univ.erase i, b j
    have hxa : ∀ i, x i * algebraMap (N ⧸ 𝔭) κ Bd = algebraMap (N ⧸ 𝔭) κ (a' i) := by
      intro i
      have hBi : Bd = b i * ∏ j ∈ Finset.univ.erase i, b j := by
        rw [hBd_def, Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)]
      have hbi := hb0 i
      rw [← hab i, hBi, map_mul, map_mul]
      field_simp

    choose d hd using fun i => Ideal.Quotient.mk_surjective (a' i)
    have key : ∀ c : Fin m → C, (∑ i, φC C N hCmem (c i) * d i) ∈ 𝔭 → ∀ i, c i = 0 := by
      intro c hc i
      have h0 : algebraMap (N ⧸ 𝔭) κ (Ideal.Quotient.mk 𝔭 (∑ i, φC C N hCmem (c i) * d i)) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc, map_zero]
      rw [map_sum, map_sum] at h0
      have h1 : (∑ i, algebraMap C K (c i) • x i) * algebraMap (N ⧸ 𝔭) κ Bd = 0 := by
        rw [← h0, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, hd i, ← hxa i, Algebra.smul_def, hcompat, mul_assoc]
      have h2 : ∑ i, algebraMap C K (c i) • x i = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h hBd0
      have h3 := (Fintype.linearIndependent_iff.mp hx) _ h2 i
      exact (map_eq_zero_iff _ (IsFractionRing.injective C K)).mp h3
    have := hbound m d key
    exact this
  have hlt : Module.rank K κ < Cardinal.aleph0 := lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := n))
  exact Module.rank_lt_aleph0_iff.mp hlt

end Adapters

end KappaFin
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finiteDimensional_fractionRing_quotient_of_not_mem.KappaFin"

open KappaFin in
theorem solution
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) [IsDiscreteValuationRing ↥C]
    [Algebra ↥C ↥𝒩₀] (hCalg : ∀ c : ↥C, ((algebraMap ↥C ↥𝒩₀ c : ↥𝒩₀) : F) = algebraMap L F (c : L))
    (ϖ : ↥C) (hϖu : ¬ IsUnit ϖ) (hϖ0 : ϖ ≠ 0)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : algebraMap ↥C ↥𝒩₀ ϖ ∉ 𝔭)
    (K κ : Type*) [Field K] [Field κ] [Algebra ↥C K] [IsFractionRing ↥C K]
    [Algebra (↥𝒩₀ ⧸ 𝔭) κ] [IsFractionRing (↥𝒩₀ ⧸ 𝔭) κ]
    [Algebra ↥C κ] [IsScalarTower ↥C (↥𝒩₀ ⧸ 𝔭) κ] [Algebra K κ] [IsScalarTower ↥C K κ] :
    FiniteDimensional K κ := by

  have hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀ := fun c hc => by
    rw [← hCalg ⟨c, hc⟩]
    exact (algebraMap ↥C ↥𝒩₀ ⟨c, hc⟩).2
  have hφ : ∀ c : ↥C, φC C 𝒩₀ hCmem c = algebraMap ↥C ↥𝒩₀ c := fun c =>
    Subtype.ext (by rw [coe_φC, hCalg])

  have hC𝔭 : ∀ c : ↥C, φC C 𝒩₀ hCmem c ∈ 𝔭 → c = 0 := fun c hc =>
    eq_zero_of_φC_mem C 𝒩₀ hCmem 𝔭 ϖ hϖu (by rw [hφ]; exact h𝔭ϖ) c hc

  obtain ⟨n, hn⟩ := core C 𝒩₀ hCmem 𝔭 hC𝔭 hld h𝔭0
    (fun x hx => AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hx)

  refine finiteDimensional_of_bound C 𝒩₀ hCmem 𝔭 n hn K κ fun c => ?_
  rw [hφ, ← IsScalarTower.algebraMap_apply ↥C K κ, IsScalarTower.algebraMap_apply ↥C (↥𝒩₀ ⧸ 𝔭) κ,
    ← Ideal.Quotient.mk_algebraMap]

end
end S_AlgebraicCurve_NodeAnnulusEngine_finiteDimensional_fractionRing_quotient_of_not_mem
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finiteDimensional_fractionRing_quotient_of_not_mem (solution)
