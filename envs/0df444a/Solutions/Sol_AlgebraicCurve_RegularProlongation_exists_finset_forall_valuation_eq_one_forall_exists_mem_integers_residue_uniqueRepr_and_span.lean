-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e4736fdb-f4fe-5c08-aa1c-1c44610f1319

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span

set_option autoImplicit false

universe u v

noncomputable section

open Polynomial

namespace ReducedBasis

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

private theorem rb_aeval_mem_adjoin (f : F) (p : L[X]) :
    aeval f p ∈ IntermediateField.adjoin L ({f} : Set F) := by
  have h1 : aeval f p ∈ Algebra.adjoin L ({f} : Set F) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  exact IntermediateField.algebra_adjoin_le_adjoin L _ h1

private theorem rb_aeval_mem_valuationSubring (f : F) (p : L[X]) (V : ValuationSubring F)
    (hL : ∀ c : L, algebraMap L F c ∈ V) (hf : f ∈ V) : aeval f p ∈ V := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c =>
    rw [aeval_monomial]
    exact mul_mem (hL c) (pow_mem hf n)

private theorem rb_transcendental (f : F) {ι : Type*} [Fintype ι] (y : ι → F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (hcard : Fintype.card ι = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hyli : ∀ c : ι → L[X], ∑ i, aeval f (c i) * y i = 0 → ∀ i, c i = 0) :
    Transcendental L f := by
  classical
  have hpos : 0 < Fintype.card ι := by
    rw [hcard]; exact Module.finrank_pos
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hpos
  rw [transcendental_iff]
  intro p hp
  have h := hyli (Pi.single i₀ p) (by
    rw [Finset.sum_eq_single i₀]
    · simp [hp]
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro h; exact absurd (Finset.mem_univ i₀) h) i₀
  simpa using h

private theorem rb_aeval_ne_zero {f : F} (hf : Transcendental L f) {p : L[X]} (hp : p ≠ 0) :
    aeval f p ≠ 0 := fun h => hp (transcendental_iff.mp hf p h)

private theorem rb_linearIndependent {f : F} (hf : Transcendental L f) {ι : Type*} [Fintype ι]
    (y : ι → F)
    (hyli : ∀ c : ι → L[X], ∑ i, aeval f (c i) * y i = 0 → ∀ i, c i = 0) :
    LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) y := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrep : ∀ i, ∃ (r s : L[X]), s ≠ 0 ∧ (g i : F) * aeval f s = aeval f r := by
    intro i
    obtain ⟨r, s, hrs⟩ :=
      (IntermediateField.mem_adjoin_simple_iff L (α := f) ((g i : F))).mp (g i).2
    by_cases hs : aeval f s = 0
    · exact ⟨0, 1, one_ne_zero, by rw [hrs, hs, div_zero, zero_mul, map_zero]⟩
    · exact ⟨r, s, fun h => hs (by rw [h, map_zero]), by rw [hrs, div_mul_cancel₀ _ hs]⟩
  choose r s hs0 hcl using hrep
  simp only [IntermediateField.smul_def, smul_eq_mul] at hg
  have hsum : (∑ i, aeval f (r i * ∏ l ∈ Finset.univ.erase i, s l) * y i) = 0 := by
    calc ∑ i, aeval f (r i * ∏ l ∈ Finset.univ.erase i, s l) * y i
        = ∑ i, ((g i : F) * y i) * ∏ l, aeval f (s l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, map_prod, ← hcl i,
            ← Finset.mul_prod_erase Finset.univ (fun l => aeval f (s l)) (Finset.mem_univ i)]
          ring
      _ = (∑ i, (g i : F) * y i) * ∏ l, aeval f (s l) := by rw [Finset.sum_mul]
      _ = 0 := by rw [hg, zero_mul]
  intro i
  have hri := hyli _ hsum i
  have hprodne : (∏ l ∈ Finset.univ.erase i, s l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ => hs0 l
  have hr0 : r i = 0 := by
    rcases mul_eq_zero.mp hri with h | h
    · exact h
    · exact absurd h hprodne
  have hcli := hcl i
  rw [hr0, map_zero] at hcli
  rcases mul_eq_zero.mp hcli with h | h
  · exact Subtype.ext (by simpa using h)
  · exact absurd h (rb_aeval_ne_zero hf (hs0 i))

private theorem rb_exists_poly_multiple {f : F} {ι : Type*} [Fintype ι]
    (bE : Module.Basis ι (IntermediateField.adjoin L ({f} : Set F)) F) (u : F) :
    ∃ (q : L[X]) (c : ι → L[X]), q ≠ 0 ∧ aeval f q * u = ∑ i, aeval f (c i) * bE i := by
  classical
  have hrep : ∀ i, ∃ (r s : L[X]), s ≠ 0 ∧ (bE.repr u i : F) * aeval f s = aeval f r := by
    intro i
    obtain ⟨r, s, hrs⟩ :=
      (IntermediateField.mem_adjoin_simple_iff L (α := f) ((bE.repr u i : F))).mp
        (bE.repr u i).2
    by_cases hs : aeval f s = 0
    · exact ⟨0, 1, one_ne_zero, by rw [hrs, hs, div_zero, zero_mul, map_zero]⟩
    · exact ⟨r, s, fun h => hs (by rw [h, map_zero]), by rw [hrs, div_mul_cancel₀ _ hs]⟩
  choose r s hs0 hcl using hrep
  refine ⟨∏ l, s l, fun i => r i * ∏ l ∈ Finset.univ.erase i, s l,
    Finset.prod_ne_zero_iff.mpr fun l _ => hs0 l, ?_⟩
  have hu : u = ∑ i, (bE.repr u i : F) * bE i := by
    conv_lhs => rw [← bE.sum_repr u]
    simp only [IntermediateField.smul_def, smul_eq_mul]
  conv_lhs => rw [hu]
  rw [map_prod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_prod, ← hcl i,
    ← Finset.mul_prod_erase Finset.univ (fun l => aeval f (s l)) (Finset.mem_univ i)]
  ring

private theorem rb_isIntegral_of_forall_mem (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F] (z : F)
    (hz : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z ∈ V) :
    IsIntegral (Algebra.adjoin L ({f} : Set F)) z :=
  AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring f f z
    (fun v htv => hz v.toValuationSubring v.algebraMap_mem' htv)

private theorem rb_isPrincipalIdealRing_adjoin (f : F) :
    IsPrincipalIdealRing (Algebra.adjoin L ({f} : Set F)) := by
  let e : (aeval f : L[X] →ₐ[L] F).range ≃ₐ[L] Algebra.adjoin L ({f} : Set F) :=
    Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval L f).symm
  let g : L[X] →ₐ[L] Algebra.adjoin L ({f} : Set F) := e.toAlgHom.comp (aeval f).rangeRestrict
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨p, hp⟩ : ∃ p : L[X], (aeval f).rangeRestrict p = e.symm w := by
      obtain ⟨p, hp⟩ := (e.symm w).2
      exact ⟨p, Subtype.ext hp⟩
    refine ⟨p, ?_⟩
    show e ((aeval f).rangeRestrict p) = w
    rw [hp]
    exact e.apply_symm_apply w
  exact IsPrincipalIdealRing.of_surjective g.toRingHom hg

open scoped IntermediateField.algebraAdjoinAdjoin in

private theorem rb_exists_aeval_eq_trace (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    {z : F} (hz : IsIntegral (Algebra.adjoin L ({f} : Set F)) z) :
    ∃ p : L[X], aeval f p =
      ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F z :
        IntermediateField.adjoin L ({f} : Set F)) : F) := by
  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({f} : Set F)) := rb_isPrincipalIdealRing_adjoin f
  have htr := Algebra.isIntegral_trace (L := IntermediateField.adjoin L ({f} : Set F)) hz
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral htr
  have hmem : ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F z :
      IntermediateField.adjoin L ({f} : Set F)) : F) ∈ Algebra.adjoin L ({f} : Set F) := by
    rw [← hw, IntermediateField.algebraAdjoinAdjoin.coe_algebraMap]
    exact w.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  exact hmem

private def rb_consts (p : L[X]) : Finset L := by
  classical exact p.support.image p.coeff

private theorem rb_mem_consts_iff (p : L[X]) (s : L) :
    s ∈ rb_consts p ↔ ∃ n, p.coeff n ≠ 0 ∧ p.coeff n = s := by
  unfold rb_consts
  simp only [Finset.mem_image, Polynomial.mem_support_iff]

private theorem rb_consts_ne_zero (p : L[X]) : ∀ s ∈ rb_consts p, s ≠ 0 := by
  intro s hs
  obtain ⟨n, hn, rfl⟩ := (rb_mem_consts_iff p s).mp hs
  exact hn

private theorem rb_coeff_mem_of_consts (A : ValuationSubring L) (p : L[X])
    (hp : ∀ s ∈ rb_consts p, A.valuation s = 1) (n : ℕ) : p.coeff n ∈ A := by
  by_cases hn : p.coeff n = 0
  · rw [hn]; exact zero_mem _
  · apply A.mem_of_valuation_le_one
    rw [hp _ ((rb_mem_consts_iff p _).mpr ⟨n, hn, rfl⟩)]

section Prolongation

variable (A : ValuationSubring L) {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
  (R : AlgebraicCurve.RegularProlongation A F Fb)

private theorem rb_aeval_mem_integers {f : F} (hfR : f ∈ R.integers) (p : L[X])
    (hp : ∀ n, p.coeff n ∈ A) : aeval f p ∈ R.integers := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun n _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem ((R.algebraMap_mem_iff _).mpr (hp n)) (pow_mem hfR n)

private theorem rb_mem_of_isIntegral {z : F} (hz : IsIntegral R.integers z) : z ∈ R.integers := by
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hz
  rw [← hw]
  exact w.2

private theorem rb_mem_integers_of_equation (z : F) (d : ℕ) (b : ℕ → F)
    (hb : ∀ k ∈ Finset.range d, b k ∈ R.integers)
    (heq : z ^ d + ∑ k ∈ Finset.range d, b k * z ^ k = 0) : z ∈ R.integers := by
  classical
  apply rb_mem_of_isIntegral A R
  set b' : ℕ → R.integers := fun k => if h : k ∈ Finset.range d then ⟨b k, hb k h⟩ else 0 with hb'
  have hb'coe : ∀ k ∈ Finset.range d, ((b' k : R.integers) : F) = b k := by
    intro k hk
    have hk' : k < d := Finset.mem_range.mp hk
    simp [hb', hk']
  set Q : Polynomial R.integers := X ^ d + ∑ k ∈ Finset.range d, C (b' k) * X ^ k with hQ
  have hQm : Q.Monic := by
    apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun k hk => ?_
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk)
  refine ⟨Q, hQm, ?_⟩
  rw [hQ]
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_finsetSum, eval₂_mul, eval₂_C]
  rw [← heq]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← hb'coe k hk]
  rfl

private theorem rb_residue_aeval {f : F} (hfR : f ∈ R.integers) (p : A[X]) :
    R.residue ⟨aeval f (p.map (algebraMap A L)), rb_aeval_mem_integers A R hfR _
        (fun n => by rw [coeff_map]; exact (p.coeff n).2)⟩
      = aeval (R.residue ⟨f, hfR⟩) (p.map (IsLocalRing.residue A)) := by

  set ρ : A →+* R.integers :=
    ((algebraMap L F).comp (algebraMap A L)).codRestrict R.integers
      (fun a => (R.algebraMap_mem_iff _).mpr a.2) with hρ
  set fO : R.integers := ⟨f, hfR⟩ with hfO
  have hlhs : (⟨aeval f (p.map (algebraMap A L)), rb_aeval_mem_integers A R hfR _
      (fun n => by rw [coeff_map]; exact (p.coeff n).2)⟩ : R.integers) = p.eval₂ ρ fO := by
    apply Subtype.ext
    show aeval f (p.map (algebraMap A L)) = R.integers.subtype (p.eval₂ ρ fO)
    rw [Polynomial.hom_eval₂, aeval_def, eval₂_map]
    congr 1
  rw [hlhs, Polynomial.hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  show R.residue (ρ a) = algebraMap (IsLocalRing.ResidueField A) Fb (IsLocalRing.residue A a)
  exact R.residue_algebraMap a

private theorem rb_residue_aeval_ne_zero {f : F} (hfR : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩))
    (p : A[X]) {n : ℕ} (hn : IsUnit (p.coeff n)) :
    aeval (R.residue ⟨f, hfR⟩) (p.map (IsLocalRing.residue A)) ≠ 0 := by
  apply rb_aeval_ne_zero htr
  intro h0
  have hc := congrArg (fun q => Polynomial.coeff q n) h0
  simp only [coeff_map, coeff_zero] at hc
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hn hc

private theorem rb_trace_mem_integers {f : F} (hfR : f ∈ R.integers)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (z : F) (hzO : z ∈ R.integers)
    (h₁ : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z ∈ V)
    (h₂ : ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∉ V →
      z * (f ^ m)⁻¹ ∈ V) :
    ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F z :
      IntermediateField.adjoin L ({f} : Set F)) : F) ∈ R.integers := by
  obtain ⟨m, hm⟩ := h₂
  have hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb := by
    rw [hdeg]; exact Module.finrank_pos
  have h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {f} → (e ∈ V ↔ e ∈ R.integers)) → z ∈ V := by
    intro V hV
    have hVR := AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R
      ⟨f, hfR⟩ htr hfin hdeg.symm V hV
    rw [hVR]; exact hzO
  obtain ⟨p, hpm, -, hpz⟩ :=
    AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
      A R ⟨f, hfR⟩ htr z m h₁ (fun V hL hfV => hm V hL hfV) h₃

  set K := IntermediateField.adjoin L ({f} : Set F) with hK
  have hfK : f ∈ K := IntermediateField.mem_adjoin_simple_self L f
  set fK : K := ⟨f, hfK⟩ with hfKdef
  set OG : ValuationSubring K := R.integers.comap (algebraMap K F) with hOG
  letI : Algebra OG F := ((algebraMap K F).comp (algebraMap OG K)).toAlgebra
  haveI : IsScalarTower OG K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hcoe : ∀ q : L[X], ((aeval fK q : K) : F) = aeval f q := by
    intro q
    have h := Polynomial.aeval_algebraMap_apply F fK q
    exact h.symm
  set φK : A[X] →+* K := (aeval fK).toRingHom.comp (Polynomial.mapRingHom (algebraMap A L)) with hφK
  have hφmem : ∀ c : A[X], φK c ∈ OG := by
    intro c
    rw [hOG, ValuationSubring.mem_comap]
    show ((aeval fK (c.map (algebraMap A L)) : K) : F) ∈ R.integers
    rw [hcoe]
    exact rb_aeval_mem_integers A R hfR _ (fun n => by rw [coeff_map]; exact (c.coeff n).2)
  set ψ : A[X] →+* OG := φK.codRestrict OG hφmem with hψ
  have hint : IsIntegral OG z := by
    refine ⟨p.map ψ, hpm.map ψ, ?_⟩
    rw [eval₂_map]
    have hcomp : (algebraMap OG F).comp ψ
        = Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) f := by
      ext c
      · show ((aeval fK (Polynomial.map (algebraMap A L) (Polynomial.C c)) : K) : F) = _
        rw [hcoe]
        simp
      · show ((aeval fK (Polynomial.map (algebraMap A L) Polynomial.X) : K) : F) = _
        rw [hcoe]
        simp
    rw [hcomp]
    exact hpz
  have htrI := Algebra.isIntegral_trace (L := K) hint
  haveI : IsIntegrallyClosed OG := inferInstance
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral htrI
  have hwF : ((Algebra.trace K F z : K) : F) = algebraMap K F (w : K) := by
    rw [← hw]; rfl
  rw [hwF]
  exact (ValuationSubring.mem_comap).mp w.2

end Prolongation

private theorem rb_exists_equation (f : F) {z : F}
    (hz : IsIntegral (Algebra.adjoin L ({f} : Set F)) z) :
    ∃ (d : ℕ) (a : ℕ → L[X]), z ^ d + ∑ k ∈ Finset.range d, aeval f (a k) * z ^ k = 0 := by
  obtain ⟨P, hPm, hPz⟩ := hz
  have hcoef : ∀ k, ∃ a : L[X], aeval f a = (algebraMap (Algebra.adjoin L ({f} : Set F)) F (P.coeff k)) := by
    intro k
    have hk : (algebraMap (Algebra.adjoin L ({f} : Set F)) F (P.coeff k)) ∈
        (aeval f : L[X] →ₐ[L] F).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (P.coeff k).2
    exact hk
  choose a ha using hcoef
  refine ⟨P.natDegree, a, ?_⟩
  have h := hPz
  rw [Polynomial.eval₂_eq_eval_map, hPm.as_sum] at h
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul,
    eval_C] at h
  simpa only [ha] using h

private theorem rb_exists_bound (f : F) {z : F}
    (hz : IsIntegral (Algebra.adjoin L ({f} : Set F)) z) :
    ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∉ V →
      z * (f ^ m)⁻¹ ∈ V := by
  classical
  obtain ⟨d, a, heq⟩ := rb_exists_equation f hz
  refine ⟨(Finset.range d).sup (fun k => (a k).natDegree), ?_⟩
  set m := (Finset.range d).sup (fun k => (a k).natDegree) with hm
  intro V hL hfV
  rw [← inv_pow]
  have hf0 : f ≠ 0 := fun h => hfV (h ▸ zero_mem V)
  set u : F := f⁻¹ with hu
  have huV : u ∈ V := (V.mem_or_inv_mem f).resolve_left hfV
  have hfu : f * u = 1 := mul_inv_cancel₀ hf0

  have hb : ∀ k ∈ Finset.range d, aeval f (a k) * u ^ (m * (d - k)) ∈ V := by
    intro k hk
    have hdeg : (a k).natDegree ≤ m * (d - k) := by
      have h1 : (a k).natDegree ≤ m := Finset.le_sup (f := fun k => (a k).natDegree) hk
      have h2 : 1 ≤ d - k := by
        have := Finset.mem_range.mp hk; omega
      calc (a k).natDegree ≤ m := h1
        _ = m * 1 := (mul_one m).symm
        _ ≤ m * (d - k) := Nat.mul_le_mul_left m h2
    rw [aeval_eq_sum_range, Finset.sum_mul]
    refine sum_mem fun j hj => ?_
    have hj' : j ≤ m * (d - k) := by
      have := Finset.mem_range.mp hj; omega
    rw [Algebra.smul_def, mul_assoc]
    refine mul_mem (hL _) ?_
    have : f ^ j * u ^ (m * (d - k)) = u ^ (m * (d - k) - j) := by
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hj'
      rw [ht, pow_add, Nat.add_sub_cancel_left, ← mul_assoc, ← mul_pow, hfu, one_pow, one_mul]
    rw [this]
    exact pow_mem huV _

  set w : F := z * u ^ m with hw
  show w ∈ V
  by_contra hwV
  have hw0 : w ≠ 0 := fun h => hwV (h ▸ zero_mem V)
  have hwinv : w⁻¹ ∈ V := (V.mem_or_inv_mem w).resolve_left hwV

  have hzd : z ^ d = - ∑ k ∈ Finset.range d, aeval f (a k) * z ^ k := eq_neg_of_add_eq_zero_left heq
  have hwd : w ^ d = - ∑ k ∈ Finset.range d, (aeval f (a k) * u ^ (m * (d - k))) * w ^ k := by
    rw [hw, mul_pow, ← pow_mul, hzd, neg_mul, Finset.sum_mul, neg_inj]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkd : k ≤ d := (Finset.mem_range.mp hk).le
    have hsplit : u ^ (m * d) = u ^ (m * (d - k)) * u ^ (m * k) := by
      rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hkd]
    rw [hsplit]
    ring

  have hone : (1 : F) = - ∑ k ∈ Finset.range d,
      (aeval f (a k) * u ^ (m * (d - k))) * (w⁻¹) ^ (d - k) := by
    have h1 : w ^ d * (w⁻¹) ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow]
    rw [← h1, hwd, neg_mul, Finset.sum_mul, neg_inj]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkd : k ≤ d := (Finset.mem_range.mp hk).le
    have hsplit : (w⁻¹) ^ d = (w⁻¹) ^ k * (w⁻¹) ^ (d - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hkd]
    rw [hsplit, mul_assoc, ← mul_assoc (w ^ k), ← mul_pow, mul_inv_cancel₀ hw0, one_pow, one_mul]
  set v₀ : F := - ∑ k ∈ Finset.range d,
      (aeval f (a k) * u ^ (m * (d - k))) * (w⁻¹) ^ (d - k - 1) with hv₀
  have hv₀V : v₀ ∈ V :=
    neg_mem (sum_mem fun k hk => mul_mem (hb k hk) (pow_mem hwinv _))
  have hv₀w : v₀ * w⁻¹ = 1 := by
    rw [hv₀, neg_mul, Finset.sum_mul, hone, neg_inj]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hpos : 1 ≤ d - k := by have := Finset.mem_range.mp hk; omega
    have hsucc : d - k = (d - k - 1) + 1 := by omega
    have hpow : (w⁻¹) ^ (d - k) = (w⁻¹) ^ (d - k - 1) * w⁻¹ := by
      rw [← pow_succ, ← hsucc]
    rw [hpow]
    ring
  have hv₀eq : v₀ = w := (mul_inv_eq_one₀ hw0).mp hv₀w
  exact hwV (hv₀eq ▸ hv₀V)

private theorem rb_det_ne_zero (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bE : Module.Basis ι (IntermediateField.adjoin L ({f} : Set F)) F)
    (tp : ι → ι → L[X])
    (htp : ∀ i j, aeval f (tp i j) =
      ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (bE i * bE j) :
        IntermediateField.adjoin L ({f} : Set F)) : F)) :
    (Matrix.of tp).det ≠ 0 := by
  intro h0
  have hdisc := Algebra.discr_not_zero_of_basis (IntermediateField.adjoin L ({f} : Set F)) bE
  apply hdisc
  apply (algebraMap (IntermediateField.adjoin L ({f} : Set F)) F).injective
  rw [map_zero, Algebra.discr_def, RingHom.map_det]
  have h1 : (algebraMap (IntermediateField.adjoin L ({f} : Set F)) F).mapMatrix
      (Algebra.traceMatrix (IntermediateField.adjoin L ({f} : Set F)) ⇑bE)
      = (aeval f : L[X] →ₐ[L] F).toRingHom.mapMatrix (Matrix.of tp) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [htp i j, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rfl
  rw [h1, ← RingHom.map_det, h0, map_zero]

section Cramer

variable (A : ValuationSubring L) {Fb : Type v} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
  (R : AlgebraicCurve.RegularProlongation A F Fb)

private theorem rb_exists_lift (p : L[X]) (hp : ∀ n, p.coeff n ∈ A) :
    ∃ p' : A[X], p'.map (algebraMap A L) = p := by
  have hl : p ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨p.coeff n, hp n⟩, rfl⟩
  exact (Polynomial.mem_lifts p).mp hl

private theorem rb_cramer {f : F} (hfR : f ∈ R.integers)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bE : Module.Basis ι (IntermediateField.adjoin L ({f} : Set F)) F)
    (hbint : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → bE i ∈ V)
    (hbO : ∀ i, bE i ∈ R.integers)
    (tp' : ι → ι → A[X])
    (htp' : ∀ i j, aeval f ((tp' i j).map (algebraMap A L)) =
      ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (bE i * bE j) :
        IntermediateField.adjoin L ({f} : Set F)) : F))
    (x : F) (hxO : x ∈ R.integers)
    (hxint : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → x ∈ V) :
    ∀ i, aeval f ((Matrix.of tp').det.map (algebraMap A L)) * (bE.repr x i : F) ∈ R.integers := by
  have hfK : f ∈ (IntermediateField.adjoin L ({f} : Set F)) := IntermediateField.mem_adjoin_simple_self L f
  set fK : (IntermediateField.adjoin L ({f} : Set F)) := ⟨f, hfK⟩ with hfKdef
  have hcoe : ∀ q : L[X], ((aeval fK q : (IntermediateField.adjoin L ({f} : Set F))) : F) = aeval f q := fun q =>
    (Polynomial.aeval_algebraMap_apply F fK q).symm

  set χ : A[X] →+* (IntermediateField.adjoin L ({f} : Set F)) :=
    (aeval fK).toRingHom.comp (Polynomial.mapRingHom (algebraMap A L)) with hχ
  have hχcoe : ∀ q : A[X],
      ((χ q : (IntermediateField.adjoin L ({f} : Set F))) : F) = aeval f (q.map (algebraMap A L)) :=
    fun q => hcoe _
  set TK : Matrix ι ι (IntermediateField.adjoin L ({f} : Set F)) := χ.mapMatrix (Matrix.of tp') with hTK
  have hTKapply : ∀ i j, TK i j = Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (bE i * bE j) := by
    intro i j
    apply Subtype.ext
    show ((χ (tp' i j) : (IntermediateField.adjoin L ({f} : Set F))) : F) = _
    rw [hχcoe, htp' i j]

  set cK : ι → (IntermediateField.adjoin L ({f} : Set F)) := fun i => bE.repr x i with hcK
  set tK : ι → (IntermediateField.adjoin L ({f} : Set F)) :=
    fun i => Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (bE i * x) with htK
  have hsys : TK.mulVec cK = tK := by
    funext i
    simp only [Matrix.mulVec, dotProduct, hTKapply, htK, hcK]
    conv_rhs => rw [← bE.sum_repr x, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hcram : ∀ i, TK.det * cK i = ∑ j, TK.adjugate i j * tK j := by
    intro i
    have h := congrFun (congrArg (fun w => TK.adjugate.mulVec w) hsys) i
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    simp [Matrix.mulVec, dotProduct]

  have hdet : TK.det = χ (Matrix.of tp').det := by rw [hTK, ← RingHom.map_det]
  have hadj : ∀ i j, TK.adjugate i j = χ ((Matrix.of tp').adjugate i j) := by
    intro i j
    rw [hTK, ← RingHom.map_adjugate]
    rfl

  have htmem : ∀ j, ((tK j : (IntermediateField.adjoin L ({f} : Set F))) : F) ∈ R.integers := by
    intro j
    have hint : IsIntegral (Algebra.adjoin L ({f} : Set F)) (bE j * x) :=
      rb_isIntegral_of_forall_mem f _ (fun V hL hfV => mul_mem (hbint j V hL hfV) (hxint V hL hfV))
    exact rb_trace_mem_integers A R hfR htr hdeg (bE j * x) (mul_mem (hbO j) hxO)
      (fun V hL hfV => mul_mem (hbint j V hL hfV) (hxint V hL hfV)) (rb_exists_bound f hint)

  have hadjmem : ∀ i j, ((TK.adjugate i j : (IntermediateField.adjoin L ({f} : Set F))) : F) ∈ R.integers := by
    intro i j
    rw [hadj, hχcoe]
    exact rb_aeval_mem_integers A R hfR _
      (fun n => by rw [coeff_map]; exact (((Matrix.of tp').adjugate i j).coeff n).2)
  intro i
  have h := congrArg (algebraMap (IntermediateField.adjoin L ({f} : Set F)) F) (hcram i)
  rw [map_mul, map_sum] at h
  have hdetF : algebraMap (IntermediateField.adjoin L ({f} : Set F)) F TK.det
      = aeval f ((Matrix.of tp').det.map (algebraMap A L)) := by
    rw [hdet]; exact hχcoe _
  rw [hdetF] at h
  have hci : algebraMap (IntermediateField.adjoin L ({f} : Set F)) F (cK i) = (bE.repr x i : F) := rfl
  rw [hci] at h
  rw [h]
  exact sum_mem fun j _ => by
    rw [map_mul]
    exact mul_mem (hadjmem i j) (htmem j)

private theorem rb_residue_mem_span_of_integral {f : F} (hfR : f ∈ R.integers)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    [IsAlgClosed L]
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bE : Module.Basis ι (IntermediateField.adjoin L ({f} : Set F)) F)
    (hbint : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → bE i ∈ V)
    (hbO : ∀ i, bE i ∈ R.integers)
    (tp' : ι → ι → A[X])
    (htp' : ∀ i j, aeval f ((tp' i j).map (algebraMap A L)) =
      ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (bE i * bE j) :
        IntermediateField.adjoin L ({f} : Set F)) : F))
    (hdF : R.residue ⟨aeval f ((Matrix.of tp').det.map (algebraMap A L)),
      rb_aeval_mem_integers A R hfR _ (fun n => by rw [coeff_map]; exact ((Matrix.of tp').det.coeff n).2)⟩
      ≠ 0)
    (x : F) (hxO : x ∈ R.integers)
    (hxint : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → x ∈ V) :
    ∃ c : ι → IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb),
      R.residue ⟨x, hxO⟩ = ∑ i, (c i : Fb) * R.residue ⟨bE i, hbO i⟩ := by
  set Kb := IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)
    with hKb
  set D : L[X] := (Matrix.of tp').det.map (algebraMap A L) with hD
  have hDmem : ∀ n, D.coeff n ∈ A := fun n => by
    rw [hD, coeff_map]; exact ((Matrix.of tp').det.coeff n).2
  set dF : F := aeval f D with hdFdef
  have hdFO : dF ∈ R.integers := rb_aeval_mem_integers A R hfR D hDmem
  set dO : R.integers := ⟨dF, hdFO⟩ with hdO
  have hdO0 : R.residue dO ≠ 0 := hdF
  have hcoord := rb_cramer A R hfR htr hdeg bE hbint hbO tp' htp' x hxO hxint

  set cO : ι → R.integers := fun i => ⟨dF * (bE.repr x i : F), hcoord i⟩ with hcO

  have hsumO : dO * ⟨x, hxO⟩ = ∑ i, cO i * ⟨bE i, hbO i⟩ := by
    apply Subtype.ext
    push_cast [hdO, hcO]
    conv_lhs => rw [← bE.sum_repr x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [IntermediateField.smul_def, smul_eq_mul]
    ring

  have hcmem : ∀ i, R.residue (cO i) ∈ Kb := by
    intro i
    set w : (IntermediateField.adjoin L ({f} : Set F)) := ⟨dF, rb_aeval_mem_adjoin f D⟩ * bE.repr x i with hw
    have hwF : (w : F) = dF * (bE.repr x i : F) := rfl
    have hwi : (w : F) ∈ R.integers := hwF ▸ hcoord i
    have h := GaussProlongation.residue_mem_adjoin_residue_of_mem_adjoin_integers A
      (fun _ : Unit => Fb) (fun _ => R) f (fun _ => hfR) (fun _ => htr) () () w hwi hwi
    have hsub : (⟨(w : F), hwi⟩ : R.integers) = ⟨dF * (bE.repr x i : F), hcoord i⟩ :=
      Subtype.ext hwF
    rw [hsub] at h
    exact h
  have hdmem : R.residue dO ∈ Kb := by
    have h : R.residue dO = aeval (R.residue ⟨f, hfR⟩)
        ((Matrix.of tp').det.map (IsLocalRing.residue A)) :=
      rb_residue_aeval A R hfR (Matrix.of tp').det
    rw [h]
    exact rb_aeval_mem_adjoin _ _

  set dKb : Kb := ⟨R.residue dO, hdmem⟩ with hdKb
  refine ⟨fun i => ⟨R.residue (cO i), hcmem i⟩ / dKb, ?_⟩
  have hres := congrArg R.residue hsumO
  rw [map_mul, map_sum] at hres
  simp only [map_mul] at hres
  have hinv : R.residue ⟨x, hxO⟩ = (R.residue dO)⁻¹ * (R.residue dO * R.residue ⟨x, hxO⟩) := by
    rw [← mul_assoc, inv_mul_cancel₀ hdO0, one_mul]
  rw [hinv, hres, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast [hdKb]
  ring

private theorem rb_forall_exists_residue_eq {f : F} (hfR : f ∈ R.integers)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    [IsAlgClosed L]
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bE : Module.Basis ι (IntermediateField.adjoin L ({f} : Set F)) F)
    (hbint : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → bE i ∈ V)
    (hbO : ∀ i, bE i ∈ R.integers)
    (tp' : ι → ι → A[X])
    (htp' : ∀ i j, aeval f ((tp' i j).map (algebraMap A L)) =
      ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (bE i * bE j) :
        IntermediateField.adjoin L ({f} : Set F)) : F))
    (hdF : R.residue ⟨aeval f ((Matrix.of tp').det.map (algebraMap A L)),
      rb_aeval_mem_integers A R hfR _ (fun n => by rw [coeff_map]; exact ((Matrix.of tp').det.coeff n).2)⟩
      ≠ 0)
    (b : Fb) :
    ∃ c : ι → IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb),
      b = ∑ i, (c i : Fb) * R.residue ⟨bE i, hbO i⟩ := by
  classical
  set Kb := IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)
    with hKb
  obtain ⟨u, rfl⟩ := R.residue_surjective b
  obtain ⟨q, cq, hq0, hqu⟩ := rb_exists_poly_multiple bE (u : F)

  have hne : (rb_consts q).Nonempty :=
    ⟨q.leadingCoeff, (rb_mem_consts_iff q _).mpr ⟨q.natDegree, leadingCoeff_ne_zero.mpr hq0, rfl⟩⟩
  obtain ⟨c₀, hc₀mem, hc₀max⟩ := Finset.exists_max_image (rb_consts q) (fun s => A.valuation s) hne
  have hc₀0 : c₀ ≠ 0 := rb_consts_ne_zero q c₀ hc₀mem
  obtain ⟨n₀, hn₀, hc₀eq⟩ := (rb_mem_consts_iff q c₀).mp hc₀mem
  set q₁ : L[X] := C c₀⁻¹ * q with hq₁
  have hq₁coeff : ∀ n, q₁.coeff n ∈ A := by
    intro n
    rw [hq₁, coeff_C_mul]
    by_cases hn : q.coeff n = 0
    · rw [hn, mul_zero]; exact zero_mem _
    · apply A.mem_of_valuation_le_one
      rw [map_mul, map_inv₀]
      have hle : A.valuation (q.coeff n) ≤ A.valuation c₀ :=
        hc₀max _ ((rb_mem_consts_iff q _).mpr ⟨n, hn, rfl⟩)
      have hv0 : A.valuation c₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hc₀0
      calc (A.valuation c₀)⁻¹ * A.valuation (q.coeff n)
          ≤ (A.valuation c₀)⁻¹ * A.valuation c₀ := mul_le_mul_right hle _
        _ = 1 := inv_mul_cancel₀ hv0
  obtain ⟨q₁', hq₁'⟩ := rb_exists_lift A q₁ hq₁coeff

  have hunit : IsUnit (q₁'.coeff n₀) := by
    have h1 : ((q₁'.coeff n₀ : A) : L) = 1 := by
      have h := congrArg (fun p => Polynomial.coeff p n₀) hq₁'
      simp only [coeff_map] at h
      rw [hq₁, coeff_C_mul, hc₀eq, inv_mul_cancel₀ hc₀0] at h
      exact h
    have h2 : q₁'.coeff n₀ = 1 := Subtype.ext h1
    rw [h2]; exact isUnit_one

  have hs₁O : aeval f q₁ ∈ R.integers := rb_aeval_mem_integers A R hfR q₁ hq₁coeff
  have hs₁res : R.residue ⟨aeval f q₁, hs₁O⟩
      = aeval (R.residue ⟨f, hfR⟩) (q₁'.map (IsLocalRing.residue A)) := by
    have h := rb_residue_aeval A R hfR q₁'
    have hel : (⟨aeval f q₁, hs₁O⟩ : R.integers)
        = ⟨aeval f (q₁'.map (algebraMap A L)), rb_aeval_mem_integers A R hfR _
            (fun n => by rw [coeff_map]; exact (q₁'.coeff n).2)⟩ :=
      Subtype.ext (by simp only [hq₁'])
    rw [hel, h]
  have hs₁ne : R.residue ⟨aeval f q₁, hs₁O⟩ ≠ 0 := by
    rw [hs₁res]; exact rb_residue_aeval_ne_zero A R hfR htr q₁' hunit
  have hs₁mem : R.residue ⟨aeval f q₁, hs₁O⟩ ∈ Kb := by
    rw [hs₁res]; exact rb_aeval_mem_adjoin _ _

  set x₁ : F := aeval f q₁ * u with hx₁
  have hx₁O : x₁ ∈ R.integers := mul_mem hs₁O u.2
  have hx₁int : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → x₁ ∈ V := by
    intro V hL hfV
    have hx₁eq : x₁ = algebraMap L F c₀⁻¹ * ∑ i, aeval f (cq i) * bE i := by
      rw [hx₁, hq₁, map_mul, aeval_C, mul_assoc, hqu]
    rw [hx₁eq]
    exact mul_mem (hL _) (sum_mem fun i _ =>
      mul_mem (rb_aeval_mem_valuationSubring f _ V hL hfV) (hbint i V hL hfV))
  obtain ⟨c, hc⟩ := rb_residue_mem_span_of_integral A R hfR htr hdeg bE hbint hbO tp' htp' hdF
    x₁ hx₁O hx₁int

  have hx₁res : R.residue ⟨x₁, hx₁O⟩ = R.residue ⟨aeval f q₁, hs₁O⟩ * R.residue u := by
    rw [← map_mul]; rfl
  set sKb : Kb := ⟨R.residue ⟨aeval f q₁, hs₁O⟩, hs₁mem⟩ with hsKb
  refine ⟨fun i => c i / sKb, ?_⟩
  have hinv : R.residue u = (R.residue ⟨aeval f q₁, hs₁O⟩)⁻¹ *
      (R.residue ⟨aeval f q₁, hs₁O⟩ * R.residue u) := by
    rw [← mul_assoc, inv_mul_cancel₀ hs₁ne, one_mul]
  rw [hinv, ← hx₁res, hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast [hsKb]
  ring

end Cramer

private theorem rb_uniqueRepr {K₁ : Type u} [Field K₁] {E : Type v} [Field E] [Algebra K₁ E]
    {t : E} (ht : Transcendental K₁ t) {ι : Type*} [Fintype ι] (z : ι → E)
    (hcard : Fintype.card ι = Module.finrank (IntermediateField.adjoin K₁ ({t} : Set E)) E)
    (hspan : ∀ b : E, ∃ c : ι → IntermediateField.adjoin K₁ ({t} : Set E),
      b = ∑ i, (c i : E) * z i) :
    ∀ q q' : ι → K₁[X], ∑ i, aeval t (q i) * z i = ∑ i, aeval t (q' i) * z i → q = q' := by
  classical
  have htop : (⊤ : Submodule (IntermediateField.adjoin K₁ ({t} : Set E)) E)
      ≤ Submodule.span (IntermediateField.adjoin K₁ ({t} : Set E)) (Set.range z) := by
    intro b _
    obtain ⟨c, hc⟩ := hspan b
    rw [hc]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hsm : (c i : E) * z i = c i • z i := by
      rw [IntermediateField.smul_def, smul_eq_mul]
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (IntermediateField.adjoin K₁ ({t} : Set E)) z :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop hcard
  intro q q' hqq
  funext i
  set g : ι → IntermediateField.adjoin K₁ ({t} : Set E) :=
    fun j => ⟨aeval t (q j - q' j), rb_aeval_mem_adjoin t _⟩ with hg
  have hsum : ∑ j, g j • z j = 0 := by
    have h1 : ∀ j, g j • z j = aeval t (q j) * z j - aeval t (q' j) * z j := by
      intro j
      rw [IntermediateField.smul_def, smul_eq_mul]
      show aeval t (q j - q' j) * z j = _
      rw [map_sub, sub_mul]
    simp only [h1, Finset.sum_sub_distrib, hqq, sub_self]
  have hgi : g i = 0 := (Fintype.linearIndependent_iff.mp hli) g hsum i
  have h0 : aeval t (q i - q' i) = 0 := congrArg Subtype.val hgi
  exact sub_eq_zero.mp (transcendental_iff.mp ht _ h0)

end ReducedBasis

open ReducedBasis in
theorem solution
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    {ι : Type*} [Fintype ι] (y : ι → F)
    (hcard : Fintype.card ι = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hyint : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y i ∈ V)
    (hyli : ∀ c : ι → Polynomial L,
      ∑ i, Polynomial.aeval f (c i) * y i = 0 → ∀ i, c i = 0) :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∀ (Fb : Type v) [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) →
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
          ∃ hyO : ∀ i, y i ∈ R.integers,
            (∀ q q' : ι → Polynomial (IsLocalRing.ResidueField A),
              ∑ i, Polynomial.aeval (R.residue ⟨f, hfR⟩) (q i) * R.residue ⟨y i, hyO i⟩
                = ∑ i, Polynomial.aeval (R.residue ⟨f, hfR⟩) (q' i) * R.residue ⟨y i, hyO i⟩ →
              q = q') ∧
            ∀ b : Fb, ∃ c : ι →
                IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb),
              b = ∑ i, (c i : Fb) * R.residue ⟨y i, hyO i⟩ := by
  classical
  have hf : Transcendental L f := rb_transcendental f y hcard hyli
  have hli := rb_linearIndependent hf y hyli
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by rw [hcard]; exact Module.finrank_pos)
  let bE : Module.Basis ι (IntermediateField.adjoin L ({f} : Set F)) F :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbE : ∀ i, bE i = y i := fun i => by
    simp [bE, coe_basisOfLinearIndependentOfCardEqFinrank]

  have hyI : ∀ i, IsIntegral (Algebra.adjoin L ({f} : Set F)) (y i) :=
    fun i => rb_isIntegral_of_forall_mem f (y i) (hyint i)
  have hyyI : ∀ i j, IsIntegral (Algebra.adjoin L ({f} : Set F)) (y i * y j) :=
    fun i j => rb_isIntegral_of_forall_mem f _ (fun V hL hfV => mul_mem (hyint i V hL hfV) (hyint j V hL hfV))

  choose tp htp using fun i j => rb_exists_aeval_eq_trace f (hyyI i j)
  have htpb : ∀ i j, aeval f (tp i j) =
      ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (bE i * bE j) :
        IntermediateField.adjoin L ({f} : Set F)) : F) := by
    intro i j
    rw [hbE i, hbE j]
    exact htp i j
  have hDne : (Matrix.of tp).det ≠ 0 := rb_det_ne_zero f bE tp htpb

  choose d a ha using fun i => rb_exists_equation f (hyI i)

  refine ⟨((Finset.univ.biUnion fun i => (Finset.range (d i)).biUnion fun k => rb_consts (a i k)) ∪
      (Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => rb_consts (tp i j))) ∪
      {(Matrix.of tp).det.leadingCoeff}, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · rcases Finset.mem_union.mp hs with hs | hs
      · obtain ⟨i, -, hs⟩ := Finset.mem_biUnion.mp hs
        obtain ⟨k, -, hs⟩ := Finset.mem_biUnion.mp hs
        exact rb_consts_ne_zero _ _ hs
      · obtain ⟨i, -, hs⟩ := Finset.mem_biUnion.mp hs
        obtain ⟨j, -, hs⟩ := Finset.mem_biUnion.mp hs
        exact rb_consts_ne_zero _ _ hs
    · rw [Finset.mem_singleton.mp hs]
      exact leadingCoeff_ne_zero.mpr hDne
  intro A hS Fb _ _ R hfR htr hdeg
  have hSa : ∀ i, ∀ k ∈ Finset.range (d i), ∀ s ∈ rb_consts (a i k), A.valuation s = 1 :=
    fun i k hk s hs => hS s (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨k, hk, hs⟩⟩)))
  have hStp : ∀ i j, ∀ s ∈ rb_consts (tp i j), A.valuation s = 1 :=
    fun i j s hs => hS s (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hs⟩⟩)))
  have hSlead : A.valuation (Matrix.of tp).det.leadingCoeff = 1 :=
    hS _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

  have hyO : ∀ i, y i ∈ R.integers := fun i =>
    rb_mem_integers_of_equation A R (y i) (d i) (fun k => aeval f (a i k))
      (fun k hk => rb_aeval_mem_integers A R hfR _ (rb_coeff_mem_of_consts A _ (hSa i k hk)))
      (ha i)
  have hbO : ∀ i, bE i ∈ R.integers := fun i => by rw [hbE i]; exact hyO i
  have hbint : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V →
      bE i ∈ V := fun i V hL hfV => by rw [hbE i]; exact hyint i V hL hfV

  choose tp' htp' using fun i j => rb_exists_lift A (tp i j) (rb_coeff_mem_of_consts A _ (hStp i j))
  have htp'b : ∀ i j, aeval f ((tp' i j).map (algebraMap A L)) =
      ((Algebra.trace (IntermediateField.adjoin L ({f} : Set F)) F (bE i * bE j) :
        IntermediateField.adjoin L ({f} : Set F)) : F) := by
    intro i j
    rw [htp' i j]
    exact htpb i j
  have hdetmap : (Matrix.of tp').det.map (algebraMap A L) = (Matrix.of tp).det := by
    have h := RingHom.map_det (Polynomial.mapRingHom (algebraMap A L)) (Matrix.of tp')
    simp only [Polynomial.coe_mapRingHom] at h
    rw [h]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Polynomial.coe_mapRingHom,
      htp' i j]

  have hdF : R.residue ⟨aeval f ((Matrix.of tp').det.map (algebraMap A L)),
      rb_aeval_mem_integers A R hfR _
        (fun n => by rw [coeff_map]; exact ((Matrix.of tp').det.coeff n).2)⟩ ≠ 0 := by
    rw [rb_residue_aeval A R hfR]
    refine rb_residue_aeval_ne_zero A R hfR htr (Matrix.of tp').det
      (n := (Matrix.of tp).det.natDegree) ?_
    have hc : (((Matrix.of tp').det.coeff (Matrix.of tp).det.natDegree : A) : L)
        = (Matrix.of tp).det.leadingCoeff := by
      show algebraMap A L _ = _
      rw [← coeff_map, hdetmap]
      rfl
    rw [A.valuation_eq_one_iff, hc]
    exact hSlead

  have hspan : ∀ b : Fb, ∃ c : ι →
      IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb),
      b = ∑ i, (c i : Fb) * R.residue ⟨y i, hyO i⟩ := by
    intro b
    obtain ⟨c, hc⟩ := rb_forall_exists_residue_eq A R hfR htr hdeg bE hbint hbO tp' htp'b hdF b
    have hsub : ∀ i, (⟨bE i, hbO i⟩ : R.integers) = ⟨y i, hyO i⟩ := fun i => Subtype.ext (hbE i)
    simp only [hsub] at hc
    exact ⟨c, hc⟩
  exact ⟨hyO, rb_uniqueRepr htr _ (hcard.trans hdeg.symm) hspan, hspan⟩

end
end S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span (solution)
