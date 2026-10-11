-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0015
-- name    : PNT_ZeroFree_433_0015
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:18:40.795046+00:00
-- url     : https://prove2.me/theorems/46c4796f-45ef-4121-a0d3-acb38dd2e553
-- title:
--   Zero-free region foundations: GaussSum.QuadraticTrace [0015]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L24-L598

import Definitions.Def_PNT_ZeroFree_433_0014

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L24-L598
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

section

open ActualEisensteinCoordinates ShortDraftLatticeCount

theorem omega_sq_for_norm : omega ^ 2 = -omega - 1 := by
  simpa [omega] using
    IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem conjO_eval_coordinates (a b : ℤ) :
    conjO (eval a b) = eval (a - b) (-b) := by
  have hω : ActualEisensteinCoordinates.omega = omega := rfl
  simp only [eval, map_add, map_mul, map_intCast, hω, conjO_omega]
  rw [omega_sq_for_norm]
  push_cast
  ring

theorem coordinate_norm_eq_mul_conjO (p : O) :
    ((q (coords p) : ℤ) : O) = p * conjO p := by
  let a := (coords p).1
  let b := (coords p).2
  have hp : p = eval a b := (eval_coords p).symm
  symm
  calc
    p * conjO p = eval a b * eval (a - b) (-b) := by
      rw [hp, conjO_eval_coordinates]
    _ = ((q (coords p) : ℤ) : O) := by
      rw [eval_mul]
      simp only [eval, q]
      dsimp [a, b]
      push_cast
      ring

theorem algebraNorm_eq_coordinate_norm (p : O) :
    Algebra.norm ℤ p = q (coords p) := by
  have h := (norm_int_eq_mul_conjO p).trans
    (coordinate_norm_eq_mul_conjO p).symm
  exact_mod_cast h

theorem qNat_eq_absNorm_span (p : O) :
    qNat p = Ideal.absNorm (Ideal.span {p}) := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq_coordinate_norm]
  unfold qNat
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (qO_nonneg p),
    Int.natAbs_of_nonneg (qO_nonneg p)]

end

section

theorem prime_sixth_row_approx_ideal_norm
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0)
    (hprime : (Ideal.span {p} : Ideal O).IsMaximal)
    (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns,
      Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / Ideal.absNorm (Ideal.span {p}) + 1) : ℕ) := by
  have hcol : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D := by
    intro n hn
    rw [qNat_eq_absNorm_span]
    exact hcolnorm n hn
  simpa only [qNat_eq_absNorm_span] using
    (prime_sixth_row_approx_maximal P hgood columns support weight p hp
      hprime D hsupport hcol hweight)

theorem sixth_power_eq_implies_same_prime_ideal
    (p q : O)
    (hp : (Ideal.span {p} : Ideal O).IsMaximal)
    (hq : (Ideal.span {q} : Ideal O).IsMaximal)
    (h : p ^ 6 = q ^ 6) :
    (Ideal.span {p} : Ideal O) = Ideal.span {q} := by
  have hq6 : q ^ 6 ∈ Ideal.span {q} :=
    Ideal.mem_span_singleton.mpr (dvd_pow_self q (by decide))
  have hp6 : p ^ 6 ∈ Ideal.span {q} := by rw [h]; exact hq6
  have hpmem : p ∈ Ideal.span {q} :=
    hq.isPrime.mem_of_pow_mem 6 hp6
  have hle : (Ideal.span {p} : Ideal O) ≤ Ideal.span {q} :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpmem
  exact hp.eq_of_le hq.ne_top hle

theorem sixth_power_rows_injective
    {ι : Type*} (S : Finset ι) (P : ι → Ideal O) (p : ι → O)
    (hprime : ∀ i ∈ S, (P i).IsMaximal)
    (hgen : ∀ i ∈ S, P i = Ideal.span {p i})
    (hinj : Set.InjOn P (S : Set ι)) :
    Set.InjOn (fun i => p i ^ 6) (S : Set ι) := by
  intro i hi j hj heq
  have hsame : Ideal.span {p i} = (Ideal.span {p j} : Ideal O) :=
    sixth_power_eq_implies_same_prime_ideal (p i) (p j)
      (hgen i hi ▸ hprime i hi)
      (hgen j hj ▸ hprime j hj) heq
  apply hinj hi hj
  rw [hgen i hi, hgen j hj]
  exact hsame

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

theorem rational_modulus_card (m : ℕ) (_hm : m ≠ 0) :
    Nat.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
  have hnorm : Algebra.norm ℤ (m : O) = (m : ℤ) ^ 2 := by
    have h := Algebra.norm_algebraMap_of_basis
      EisensteinEmbedding.pb.basis (m : ℤ)
    simpa [EisensteinEmbedding.pb_dim] using h
  calc
    Nat.card (O ⧸ Ideal.span {(m : O)}) =
        Ideal.absNorm (Ideal.span {(m : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = (Algebra.norm ℤ (m : O)).natAbs :=
      Ideal.absNorm_span_singleton (m : O)
    _ = m ^ 2 := by rw [hnorm]; simp

private theorem mk_eval_congr_mod (m : ℕ) (a b c d : ℤ)
    (ha : (a : ZMod m) = c) (hb : (b : ZMod m) = d) :
    Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval a b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval c d) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have hda : (m : ℤ) ∣ a - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub c a m).mp ha.symm
  have hdb : (m : ℤ) ∣ b - d :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d b m).mp hb.symm
  obtain ⟨r, hr⟩ := hda
  obtain ⟨s, hs⟩ := hdb
  apply (Ideal.mem_span_singleton).mpr
  refine ⟨ActualEisensteinCoordinates.eval r s, ?_⟩
  dsimp [ActualEisensteinCoordinates.eval]
  rw [show a = c + m*r by omega, show b = d + m*s by omega]
  push_cast
  ring

noncomputable def rationalCoordMap (m : ℕ) :
    ZMod m × ZMod m → (O ⧸ Ideal.span {(m : O)}) :=
  fun ab => Ideal.Quotient.mk (Ideal.span {(m : O)})
    (ActualEisensteinCoordinates.eval (ZMod.cast ab.1) (ZMod.cast ab.2))

theorem rationalCoordMap_surjective (m : ℕ) :
    Function.Surjective (rationalCoordMap m) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, b, hab⟩ := ActualEisensteinCoordinates.exists_coordinates z
  refine ⟨((a : ZMod m), (b : ZMod m)), ?_⟩
  change Ideal.Quotient.mk (Ideal.span {(m : O)})
      (ActualEisensteinCoordinates.eval (ZMod.cast (a : ZMod m))
        (ZMod.cast (b : ZMod m))) = _
  rw [hab]
  apply mk_eval_congr_mod
  · exact ZMod.intCast_zmod_cast _
  · exact ZMod.intCast_zmod_cast _

noncomputable def rationalCoordEquiv (m : ℕ) (hm : m ≠ 0) :
    ZMod m × ZMod m ≃ (O ⧸ Ideal.span {(m : O)}) := by
  letI : NeZero m := ⟨hm⟩
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  refine Equiv.ofBijective (rationalCoordMap m) ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · exact rationalCoordMap_surjective m
  · have hq : Fintype.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
      simpa only [Nat.card_eq_fintype_card] using rational_modulus_card m hm
    simp [hq, Fintype.card_prod, sq]

theorem breveE_rational_trace (m : ℕ) [NeZero m] (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) =
      (ZMod.stdAddChar (N := m)) (b : ZMod m) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / m) = star z / m := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / m) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / m) =
      2 * Real.pi * Complex.I * (b : ℂ) / m := by
    rw [← add_div, hL]
    ring
  rw [harg, ZMod.stdAddChar_coe]

theorem eisEmbedding_eval (a b : ℤ) :
    eisEmbedding (ActualEisensteinCoordinates.eval a b) =
      (a : ℂ) + (b : ℂ) * omega3 := by
  have hgen : ActualEisensteinCoordinates.omega =
      EisensteinEmbedding.pb.gen := by
    rw [← ActualEisensteinCoordinates.pb_gen]
    rfl
  rw [ActualEisensteinCoordinates.eval, hgen]
  change EisensteinEmbedding.embedding omega3 omega3_sq
    (a + b * EisensteinEmbedding.pb.gen : O) = _
  exact EisensteinEmbedding.embedding_apply_ab omega3 omega3_sq a b

theorem rationalCoordEquiv_apply (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    rationalCoordEquiv m hm (a,b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b)) := rfl

theorem rational_quadratic_phase (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    letI : NeZero m := ⟨hm⟩
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      breveE_period_coordinates (m : O) (by exact_mod_cast hm)
    ψ ((rationalCoordEquiv m hm (a,b)) ^ 2) =
      ZMod.stdAddChar (2*a*b - b^2) := by
  let : NeZero m := ⟨hm⟩
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    breveE_period_coordinates (m : O) (by exact_mod_cast hm)
  let A : ℤ := ZMod.cast a
  let B : ℤ := ZMod.cast b
  change ShortDraftTrace.breveE
    (eisEmbedding (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b) ^ 2) /
      (eisEmbedding (m : O) * eisLam)) = _
  rw [pow_two, ActualEisensteinCoordinates.eval_mul]
  rw [eisEmbedding_eval, map_natCast]
  change ShortDraftTrace.breveE
    ((((A*A-B*B : ℤ) : ℂ) + ((A*B+B*A-B*B : ℤ) : ℂ) * omega3) /
      ((m : ℂ) * eisLam)) = _
  have hdiv (X : ℂ) : X / ((m : ℂ) * eisLam) = (X / eisLam) / m := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hdiv, breveE_rational_trace]
  congr 1
  dsimp [A, B]
  push_cast
  ring

theorem rational_quadratic_character_sum (m : ℕ) [NeZero m]
    (hodd : Odd m) :
    (∑ a : ZMod m, ∑ b : ZMod m,
      ZMod.stdAddChar (2*a*b-b^2)) = (m : ℂ) := by
  let ψ : AddChar (ZMod m) ℂ := ZMod.stdAddChar
  have htwo : IsUnit (2 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hodd)
  have hmulzero (b : ZMod m) : (2 : ZMod m) * b = 0 ↔ b = 0 := by
    simpa only [mul_zero] using
      (htwo.mul_right_inj (b := b) (c := (0 : ZMod m)))
  calc
    (∑ a : ZMod m, ∑ b : ZMod m,
      ZMod.stdAddChar (2*a*b-b^2)) =
        ∑ b : ZMod m, ∑ a : ZMod m, ψ (2*a*b-b^2) := by
      rw [Finset.sum_comm]
    _ = ∑ b : ZMod m, (if b = 0 then (m : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a : ZMod m, ψ (2*a*b-b^2)) =
            (∑ a : ZMod m, ψ (a*(2*b))) * ψ (-b^2) := by
          simp_rw [show ∀ a : ZMod m, 2*a*b-b^2 = a*(2*b)+(-b^2) from
            fun a => by ring, map_add_eq_mul]
          rw [Finset.sum_mul]
        _ = (if (2 : ZMod m)*b = 0 then (m : ℂ) else 0) * ψ (-b^2) := by
          rw [AddChar.sum_mulShift (2*b) (ZMod.isPrimitive_stdAddChar m)]
          simp
        _ = if b = 0 then (m : ℂ) else 0 := by
          simp only [hmulzero]
          split_ifs with h
          · subst b
            simp [ψ]
          · simp
    _ = (m : ℂ) := by simp

noncomputable def quadraticGammaRational (m : ℕ) (hm : m ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates
    (m : O) (by exact_mod_cast hm)
  exact (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) /
    (‖eisEmbedding (m : O)‖ : ℂ)

theorem quadraticGammaRational_eq_one (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) : quadraticGammaRational m hm = 1 := by
  let : NeZero m := ⟨hm⟩
  let : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  let : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates
    (m : O) (by exact_mod_cast hm)
  have hsum : (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) = (m : ℂ) := by
    have hreindex := ((rationalCoordEquiv m hm).sum_comp
      (fun x : O ⧸ Ideal.span {(m : O)} => ψ (x ^ 2))).symm
    rw [hreindex, Fintype.sum_prod_type]
    calc
      (∑ x : ZMod m, ∑ y : ZMod m,
        ψ ((rationalCoordEquiv m hm) (x, y) ^ 2)) =
        ∑ x : ZMod m, ∑ y : ZMod m,
          ZMod.stdAddChar (2*x*y-y^2) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact rational_quadratic_phase m hm x y
      _ = (m : ℂ) := rational_quadratic_character_sum m hodd
  have hnorm : ‖eisEmbedding (m : O)‖ = m := by simp
  unfold quadraticGammaRational
  change (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) /
    (‖eisEmbedding (m : O)‖ : ℂ) = 1
  rw [hsum, hnorm]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  exact div_self hmC

theorem breveGaussianFourTerms_rational_odd (m : ℕ) (hodd : Odd m) :
    breveGaussianFourTerms (m : ℤ) 0 = 1 := by
  have hsq : (Complex.I ^ m) ^ 2 = -1 := by
    calc
      (Complex.I ^ m) ^ 2 = Complex.I ^ (m * 2) := by rw [pow_mul]
      _ = Complex.I ^ (2 * m) := by rw [mul_comm]
      _ = (Complex.I ^ 2) ^ m := by rw [pow_mul]
      _ = (-1 : ℂ) ^ m := by rw [Complex.I_sq]
      _ = -1 := hodd.neg_one_pow
  have hinv : (Complex.I ^ m)⁻¹ = -(Complex.I ^ m) := by
    apply inv_eq_of_mul_eq_one_right
    calc
      (Complex.I ^ m) * -(Complex.I ^ m) = -((Complex.I ^ m) ^ 2) := by ring
      _ = 1 := by rw [hsq]; ring
  rw [breveGaussianFourTerms_formula]
  simp only [zero_sub,  zpow_neg, zpow_zero, inv_one, zpow_natCast]
  rw [hinv]
  ring

theorem quadraticGammaRational_eq_fourTerms (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) :
    quadraticGammaRational m hm = breveGaussianFourTerms (m : ℤ) 0 := by
  rw [quadraticGammaRational_eq_one m hm hodd,
    breveGaussianFourTerms_rational_odd m hodd]

end

section

theorem cubic_roots_reduce_injective (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) {x y : O}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  obtain ⟨j, hj, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hy
  have hij : i = j := by
    apply (omega_reduced_primitive P hgood).pow_inj hi hj
    simpa only [map_pow] using hxy
  rw [hij]

theorem cubicChar_omega (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  let χ := cubicChar P hgood
  have hx : (χ (Ideal.Quotient.mk P omega)) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply ((omega_reduced_primitive P hgood).isUnit (by decide))
  have hy : (omega ^ ((Nat.card (O ⧸ P) - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, omega_primitive.pow_eq_one, one_pow]
  apply cubic_roots_reduce_injective P hgood hx hy
  rw [map_pow]
  exact cubicChar_reduce P hgood (Ideal.Quotient.mk P omega)

theorem cubicChar_omega_eq_one_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 1) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = 1 := by
  rw [cubicChar_omega P hgood]
  apply (omega_primitive.pow_eq_one_iff_dvd _).mpr
  omega

theorem cubicChar_omega_eq_omega_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 4) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = omega := by
  rw [cubicChar_omega P hgood]
  calc
    omega ^ ((Nat.card (O ⧸ P) - 1) / 3) = omega ^ 1 := by
      apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
      rw [← omega_primitive.eq_orderOf]
      omega
    _ = omega := pow_one omega

theorem cubicChar_omega_eq_omega_sq_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 7) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = omega ^ 2 := by
  rw [cubicChar_omega P hgood]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  omega

theorem cubicChar_omega_sq (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (omega ^ 2)) =
      omega ^ (2 * ((Nat.card (O ⧸ P) - 1) / 3)) := by
  rw [map_pow, map_pow, cubicChar_omega P hgood]
  ring

theorem finiteSquarefreeRow_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) :
    finiteSquarefreeRow P hgood S 1 = 1 := by
  classical
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_one
  intro i hi
  simp

theorem finite_actual_prime_extraction
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hrows : selected.image (fun i => p i ^ 6) ⊆ rows)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hrowbound : ∀ i ∈ selected,
      ((64 * (D / Ideal.absNorm (Ideal.span {p i}) + 1) : ℕ) : ℝ) ≤
        (D : ℝ) ^ (49 / 60 : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rows,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      2 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hinjRows : Set.InjOn (fun i => p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i => (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi; rfl
    · exact hinj
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤ (D : ℝ) ^ (49 / 60 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) D hsupport hcolnorm hweight).trans
      (hrowbound i hi)
  have hmean' : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
  have hbound := PowerExtraction.from_finite_sixth_power_rows
    rows selected (fun i => p i ^ 6) A 1 (D : ℝ) ε
    (by exact_mod_cast hD) hε hrows hinjRows happrox hcount hmean'
  simpa only [hone] using hbound

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_int_trace_div (q u v : ℤ) (_hq : q ≠ 0) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / q) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q)))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / q) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / q by simp]
  rw [← add_div, hL]
  congr 1
  ring

theorem breveE_quadratic_coordinate (a b x y : ℤ)
    (hq : a*a - a*b + b*b ≠ 0) :
    let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
    let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
    ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  let z : ℂ := (x : ℂ) + (y : ℂ) * omega3
  let cb : ℂ := ((a-b : ℤ) : ℂ) - (b : ℂ) * omega3
  let q : ℤ := a*a-a*b+b*b
  let U : ℤ := (x*x-y*y)*(a-b)+b*(2*x*y-y*y)
  let V : ℤ := -b*x*x+2*a*x*y+(b-a)*y*y
  have hnorm : c * cb = (q : ℂ) := by
    dsimp [c, cb, q]
    push_cast
    linear_combination -(b : ℂ)^2 * omega3_sq
  have hnum : z ^ 2 * cb = (U : ℂ) + (V : ℂ) * omega3 := by
    dsimp [z, cb, U, V]
    push_cast
    linear_combination
      ((y : ℂ)^2 * ((a : ℂ)-(b : ℂ)-(b : ℂ)*omega3) -
        (b : ℂ) * (2*(x : ℂ)*(y : ℂ)-(y : ℂ)^2)) * omega3_sq
  have hqC : (q : ℂ) ≠ 0 := by
    dsimp [q]
    exact_mod_cast hq
  have hc : c ≠ 0 := by
    intro hc
    apply hqC
    rw [← hnorm, hc, zero_mul]
  have hcb : cb ≠ 0 := by
    intro hcb
    apply hqC
    rw [← hnorm, hcb, mul_zero]
  have hdiv : z ^ 2 / (c * eisLam) =
      ((z ^ 2 * cb) / eisLam) / q := by
    rw [← hnorm]
    field_simp [hc, hcb, eisLam_ne_zero]
  change ShortDraftTrace.breveE (z ^ 2 / (c * eisLam)) = _
  rw [hdiv, hnum, breveE_int_trace_div q U V (by simpa [q] using hq)]

end

theorem cubicChar_traceLambda_relation (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by
  have ht : traceLambda = omega * (1 - omega) := by
    rw [traceLambda_eq_unit_mul_lambda]
    dsimp [lambda]
    ring
  calc
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
        cubicChar P hgood (Ideal.Quotient.mk P (omega * (1 - omega))) := by rw [ht]
    _ = cubicChar P hgood (Ideal.Quotient.mk P omega) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by rw [map_mul, map_mul]
    _ = _ := by rw [cubicChar_omega P hgood]

theorem cubicChar_lambda_eq_one_sub_omega (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P lambda) =
      cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by
  have hl : lambda = (-1 : O) * (1 - omega) := by
    dsimp [lambda]
    ring
  calc
    cubicChar P hgood (Ideal.Quotient.mk P lambda) =
        cubicChar P hgood (Ideal.Quotient.mk P ((-1 : O) * (1 - omega))) := by rw [hl]
    _ = cubicChar P hgood (-1) *
        cubicChar P hgood (Ideal.Quotient.mk P (1 - omega)) := by rw [map_mul, map_mul, map_neg, map_one]
    _ = _ := by rw [A3_cubicChar_neg_one P hgood, one_mul]

theorem cubicChar_traceLambda_eq_lambda_of_card_mod_nine
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 1) :
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
      cubicChar P hgood (Ideal.Quotient.mk P lambda) := by
  have hpow : omega ^ ((Nat.card (O ⧸ P) - 1) / 3) = 1 := by
    rw [← cubicChar_omega P hgood]
    exact cubicChar_omega_eq_one_of_card_mod_nine P hgood hcard
  rw [cubicChar_traceLambda_relation P hgood, hpow, one_mul,
    cubicChar_lambda_eq_one_sub_omega P hgood]

end ActualEisensteinCubic

end

end OAI

end


