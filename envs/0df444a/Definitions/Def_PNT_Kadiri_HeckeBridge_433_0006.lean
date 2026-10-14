-- Prove2me | Definitions.Def_PNT_Kadiri_HeckeBridge_433_0006
-- name    : PNT_Kadiri_HeckeBridge_433_0006
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-12T12:35:25.655694+00:00
-- url     : https://prove2.me/theorems/8cd635df-0017-484f-8ca7-c2032328f295
-- title:
--   Complete Hecke-to-zeta bridge, part 0006
-- statement:
--   Complete proved arithmetic and analytic lemmas connecting the Eisenstein Hecke L-function to ordinary Dirichlet L-functions and the Riemann zeta function. The final bridge transfers Hecke nonvanishing in Re(s) > 7/8 to zeta nonvanishing. Original hypotheses and proof bodies are retained; no unproved theorem is imported. Source modules: OAI.NumberTheory.DirichletL.Hecke.NormFiberCharacters, OAI.NumberTheory.DirichletL.Hecke.ThetaSeries, OAI.NumberTheory.DirichletL.Poisson.BinaryGaussian, OAI.NumberTheory.DirichletL.Poisson.GaussianMoments
-- source:
--   OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0; ported to Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_HeckeSevenEighths
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0005

/- Complete Hecke-to-Dirichlet and zeta bridge lemmas.
Source: OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.NormFiberCharacters
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge


noncomputable def baseChangeChar {q : ℕ} (χ : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (q * 3) :=
  χ.changeLevel (Nat.dvd_mul_right q 3) *
    chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q)


end ShortDraftHeckeBridge


namespace ShortDraftHeckeBridge

theorem ideals_isRelPrime_of_norms_coprime (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    IsRelPrime I J := by
  have hcast : IsCoprime ((Ideal.absNorm I : ℕ) : O)
      ((Ideal.absNorm J : ℕ) : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime h).map (Int.castRingHom O)
  obtain ⟨a, b, hab⟩ := hcast
  apply IsCoprime.isRelPrime
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨a * (Ideal.absNorm I : O),
    I.mul_mem_left a (Ideal.absNorm_mem I),
    b * (Ideal.absNorm J : O),
    J.mul_mem_left b (Ideal.absNorm_mem J), hab⟩

theorem baseChangeWeight_mul_of_coprime_norms {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    baseChangeWeight χ (I * J) =
      baseChangeWeight χ I * baseChangeWeight χ J := by
  have hrel := ideals_isRelPrime_of_norms_coprime I J h
  simp only [baseChangeWeight, map_mul, hrel.moebius_mul, Int.cast_mul, Nat.cast_mul]
  ring

theorem baseChangeChar_apply_of_coprime {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ)
    (h : n.Coprime (q * 3)) :
    baseChangeChar χ n = χ n * chiMinusThree n := by
  have hc : IsCoprime (n : ℤ) (q * 3 : ℕ) := by
    simpa [Int.isCoprime_iff_nat_coprime, Int.natAbs_mul] using h
  rw [baseChangeChar, MulChar.mul_apply]
  have hχ : χ.changeLevel (Nat.dvd_mul_right q 3) n = χ n := by
    simpa using (DirichletCharacter.changeLevel_eq_cast_of_dvd' χ
      (Nat.dvd_mul_right q 3) hc)
  have hη : chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) n =
      chiMinusThree n := by
    simpa using (DirichletCharacter.changeLevel_eq_cast_of_dvd' chiMinusThree
      (Nat.dvd_mul_left 3 q) hc)
  rw [hχ, hη]

theorem chiMinusThree_three : chiMinusThree (3 : ℕ) = 0 := by
  simpa using (DirichletCharacter.apply_eq_zero_iff chiMinusThree 3).mpr
    (by simp [Int.isCoprime_iff_nat_coprime])

theorem baseChangeChar_three {q : ℕ} (χ : DirichletCharacter ℂ q) :
    baseChangeChar χ (3 : ℕ) = 0 := by
  simpa using (DirichletCharacter.apply_eq_zero_iff (baseChangeChar χ) 3).mpr
    (by
      intro hc
      have hn : Nat.Coprime 3 (q * 3) := by
        simpa [Int.isCoprime_iff_nat_coprime, Int.natAbs_mul] using hc
      have hself : Nat.Coprime 3 3 := hn.of_dvd_right (Nat.dvd_mul_left 3 q)
      norm_num at hself)

private abbrev K := CyclotomicField 3 ℚ
private instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0006_1 : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0006_2 : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K

private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]

private theorem orderOf_mod3_eq_two {p : ℕ} (h : p % 3 = 2) :
    orderOf (p : ZMod 3) = 2 := by
  have hc : (p : ZMod 3) = 2 :=
    (ZMod.natCast_eq_natCast_iff' p 2 3).2 (by simpa using h)
  rw [hc]
  have hdvd : orderOf (2 : ZMod 3) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 3) ^ 2 = 1)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).1 hdvd with h1 | h2
  · have h21 : (2 : ZMod 3) = 1 := orderOf_eq_one_iff.mp h1
    exact False.elim ((by decide : (2 : ZMod 3) ≠ 1) h21)
  · exact h2

private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide

private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two

private theorem not_dvd_three {p : ℕ} (hp : p.Prime) (hneq : p ≠ 3) : ¬ p ∣ 3 := by
  intro hd
  have h := (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd
  rcases h with h1 | h3
  · exact hp.ne_one h1
  · exact hneq h3

theorem split_count_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega

theorem inert_count_of_mod_two {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_two hmod, gal_card_two] at hmain
  omega

theorem ramified_count :
    ((Ideal.span {(3 : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 K

theorem absNorm_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_one hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf, pow_one]

theorem absNorm_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 2 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_two hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf]

theorem absNorm_ramified
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    Ideal.absNorm P = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hfin : (Ideal.span {(3 : ℤ)}).inertiaDegIn O = 1 := by
    simpa using IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime 3 K
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(3 : ℤ)}) P Gal(K/ℚ)]
    exact hfin
  rw [← Ideal.pow_inertiaDeg 3 P, hf, pow_one]

theorem norm_prime_implies_over {p : ℕ} (hp : p.Prime) (I : Ideal O)
    (hI : Ideal.absNorm I = p) :
    I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by
      rw [hI]
      exact (Nat.irreducible_iff_nat_prime p).2 hp)
  have hover : I.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    rw [Ideal.under_def, algebraMap_int_eq]
    simpa [hI] using Ideal.span_singleton_absNorm (I := I) (hI ▸ hp)
  exact ⟨hprime, hover⟩

theorem norm_p_fiber_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    {I : Ideal O | Ideal.absNorm I = p} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over hp I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_split hp hmod I

theorem norm_p_fiber_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p} = ∅ := by
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hI
  have hOver := norm_prime_implies_over hp I hI
  let : I.IsPrime := hOver.1
  let : I.LiesOver (Ideal.span {(p : ℤ)}) := hOver.2
  have hNorm := absNorm_inert hp hmod I
  have hpge := hp.two_le
  nlinarith

theorem norm_three_fiber :
    {I : Ideal O | Ideal.absNorm I = 3} =
      (Ideal.span {(3 : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over (by decide) I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(3 : ℤ)}) := hI.2
    exact absNorm_ramified I

theorem norm_p_sq_fiber_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p ^ 2} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · intro hI
    have hdiv : p ∣ Ideal.absNorm I := by
      rw [hI]
      exact dvd_pow_self p (by decide)
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = p ^ 2 := absNorm_inert hp hmod P
    obtain ⟨J, hIJ⟩ := hPdiv
    have hJN : Ideal.absNorm J = 1 := by
      have heq := congrArg Ideal.absNorm hIJ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJN
    subst J
    simp only [Ideal.mul_top] at hIJ
    subst I
    exact ⟨inferInstance, inferInstance⟩
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_inert hp hmod I

theorem norm_p_sq_split_factors {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ 2) :
    ∃ P Q : Ideal O,
      P ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      Q ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      I = P * Q := by
  have hdiv : p ∣ Ideal.absNorm I := by
    rw [hI]
    exact dvd_pow_self p (by decide)
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
  have : P.IsPrime := hPmax.isPrime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  obtain ⟨Q, hIQ⟩ := hPdiv
  have hQN : Ideal.absNorm Q = p := by
    have heq := congrArg Ideal.absNorm hIQ
    simp only [map_mul] at heq
    rw [hI, hPN] at heq
    have hppos := hp.pos
    nlinarith
  exact ⟨P, Q, ⟨inferInstance, inferInstance⟩,
    norm_prime_implies_over hp Q hQN, hIQ⟩


theorem norm_nine_fiber_ramified :
    {I : Ideal O | Ideal.absNorm I = 9} =
      {I : Ideal O | ∃ P : Ideal O,
        P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
  ext I
  constructor
  · intro hI
    have hdiv : 3 ∣ Ideal.absNorm I := by
      rw [hI]
      decide
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' (by decide : Nat.Prime 3) I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(3 : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
    obtain ⟨Q, hIQ⟩ := hPdiv
    have hQN : Ideal.absNorm Q = 3 := by
      have heq := congrArg Ideal.absNorm hIQ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      omega
    have hQover := norm_prime_implies_over (by decide : Nat.Prime 3) Q hQN
    have hPover : P ∈ (Ideal.span {(3 : ℤ)}).primesOver O :=
      ⟨inferInstance, inferInstance⟩
    have hfinite : ((Ideal.span {(3 : ℤ)}).primesOver O).Finite := by
      rw [← norm_three_fiber]
      exact Ideal.finite_setOfPred_absNorm_eq 3
    have hsub : ∀ {A B : Ideal O},
        A ∈ (Ideal.span {(3 : ℤ)}).primesOver O →
        B ∈ (Ideal.span {(3 : ℤ)}).primesOver O → A = B :=
      (Set.ncard_le_one_iff hfinite).mp (by rw [ramified_count])
    have hPQ : P = Q := hsub hPover hQover
    refine ⟨P, hPover, ?_⟩
    rw [hIQ, ← hPQ, pow_two]
  · rintro ⟨P, hP, rfl⟩
    have : P.IsPrime := hP.1
    have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
    change Ideal.absNorm (P ^ 2) = 9
    rw [map_pow, absNorm_ramified P]
    norm_num


theorem local_inert_p {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) p = 0 := by
  have hf := norm_p_fiber_inert hp hmod
  unfold normFiberCoeff
  simp [hf]

theorem local_split_p {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) p = -(2 : ℂ) * χ p := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) p
  have hcard : hf.toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p} hf]
    rw [norm_p_fiber_split hp hmod]
    exact split_count_of_mod_one hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) p =
      ∑ I ∈ hf.toFinset, -χ p := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = p := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime p).2 hp))
    rw [baseChangeWeight_prime χ I hprime, hnorm]
  rw [hsum]
  simp [hcard]

theorem local_ramified_three {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 3 = -χ 3 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 3
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = 3} hf]
    rw [norm_three_fiber]
    exact ramified_count
  have hsum : normFiberCoeff (baseChangeWeight χ) 3 =
      ∑ I ∈ hf.toFinset, -χ 3 := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = 3 := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime 3).2 (by decide)))
    simpa only [hnorm, Nat.cast_ofNat] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]

theorem local_inert_p_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = -χ (p ^ 2) := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p ^ 2} hf]
    rw [norm_p_sq_fiber_inert hp hmod]
    exact inert_count_of_mod_two hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
      ∑ I ∈ hf.toFinset, -χ (p ^ 2) := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hover : I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
      rw [← norm_p_sq_fiber_inert hp hmod]
      exact hf.mem_toFinset.mp hI
    have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hI
    let : I.IsPrime := hover.1
    have hprime : Prime I := Ideal.prime_of_isPrime (by
      intro hbot
      have : Ideal.absNorm I = 0 := by rw [hbot]; simp
      rw [hnorm] at this
      exact (pow_ne_zero 2 hp.ne_zero) this) inferInstance
    simpa only [hnorm, Nat.cast_pow] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]

theorem local_ramified_nine {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 9 = 0 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 9
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 9 := hf.mem_toFinset.mp hI
  have hfactor : I ∈ {I : Ideal O | ∃ P : Ideal O,
      P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
    rw [← norm_nine_fiber_ramified]
    exact hnorm
  obtain ⟨P, hP, rfl⟩ := hfactor
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
  have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
  have hnotunit : ¬ IsUnit P := by
    intro hunit
    have htop : P = ⊤ := Ideal.isUnit_iff.mp hunit
    rw [htop, Ideal.absNorm_top] at hPN
    norm_num at hPN
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    apply hnotunit
    exact hsq P (by rw [pow_two])
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp

private theorem baseChangeWeight_prime_sq_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ (P ^ 2) = 0 := by
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    have hunit : IsUnit P := hsq P (by rw [pow_two])
    exact hP.irreducible.not_isUnit hunit
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp

theorem local_split_p_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = χ (p ^ 2) := by
  classical
  let s : Set (Ideal O) := (Ideal.span {(p : ℤ)}).primesOver O
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.mp (split_count_of_mod_one hp hmod)
  have hPover : P ∈ s := by
    change P ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  have hQover : Q ∈ s := by
    change Q ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  let : P.IsPrime := hPover.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover.2
  let : Q.IsPrime := hQover.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover.2
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  have hQN : Ideal.absNorm Q = p := absNorm_split hp hmod Q
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hPN
    exact hp.ne_zero hPN.symm
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hQN
    exact hp.ne_zero hQN.symm
  have hPprime : Prime P := Ideal.prime_of_isPrime hPne inferInstance
  have hQprime : Prime Q := Ideal.prime_of_isPrime hQne inferInstance
  have : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPne
  have : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQne
  have hrel : IsRelPrime P Q := (Ideal.isCoprime_of_isMaximal hPQ).isRelPrime
  have hmu : UniqueFactorizationMonoid.moebius (P * Q) = 1 := by
    rw [hrel.moebius_mul, hPprime.irreducible.moebius_eq,
      hQprime.irreducible.moebius_eq]
    norm_num
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hmem : P * Q ∈ hf.toFinset := by
    rw [hf.mem_toFinset]
    change Ideal.absNorm (P * Q) = p ^ 2
    rw [map_mul, hPN, hQN, pow_two]
  calc
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        ∑ I ∈ hf.toFinset, baseChangeWeight χ I := by rfl
    _ = baseChangeWeight χ (P * Q) := by
      apply Finset.sum_eq_single (P * Q)
      · intro I hImem hneq
        have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hImem
        obtain ⟨A, B, hA, hB, rfl⟩ := norm_p_sq_split_factors hp hmod I hnorm
        rw [hset] at hA hB
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
        rcases hA with hAP | hAQ <;> rcases hB with hBP | hBQ
        · rw [hAP, hBP]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ P hPprime
        · exact False.elim (hneq (by rw [hAP, hBQ]))
        · exact False.elim (hneq (by rw [hAQ, hBP, mul_comm]))
        · rw [hAQ, hBQ]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ Q hQprime
      · intro hnot
        exact False.elim (hnot hmem)
    _ = χ (p ^ 2) := by
      rw [baseChangeWeight, hmu]
      have hnorm : Ideal.absNorm (P * Q) = p ^ 2 := by
        rw [map_mul, hPN, hQN, pow_two]
      simp [hnorm, Nat.cast_pow]


end ShortDraftHeckeBridge

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.ThetaSeries
section
namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability

@[simp] theorem periodicCoeff_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    periodicCoeff w (0, 0) = w (0, 0) := by
  simp [periodicCoeff, residueEquiv, regroup, Int.divModEquiv, Int.natMod]

theorem norm_periodicCoeff_le {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (n : ℤ × ℤ) : ‖periodicCoeff w n‖ ≤ ∑ a, ‖w a‖ := by
  unfold periodicCoeff
  exact Finset.single_le_sum (fun a _ => norm_nonneg (w a)) (Finset.mem_univ _)

private theorem normForm_coordinates_eq_zero (n : ℤ × ℤ) :
    normForm n.1 n.2 = 0 ↔ n = (0, 0) := by
  rw [normForm_eq_zero_iff]
  simp only [Int.cast_eq_zero, Prod.ext_iff]

theorem theta_sub_zero_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => if normForm n.1 n.2 = 0 then 0 else
      periodicCoeff w n * (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ))
      ((pair w).f t - (pair w).f₀) := by
  have h := (theta_hasSum w ht).sub (hasSum_ite_eq (0, 0) (w (0, 0)))
  rw [pair_f₀]
  convert! h using 1
  funext n
  simp only [normForm_coordinates_eq_zero]
  by_cases hn : n = (0, 0)
  · subst n
    simp [normForm]
  · simp [hn]

theorem completed_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
      periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s) (completed w s) := by
  have hsum : Summable (fun n : ℤ × ℤ => ‖periodicCoeff w n‖ /
      normForm n.1 n.2 ^ s.re) :=
    summable_weighted_normForm (norm_periodicCoeff_le w) hs
  have h := hasSum_mellin_pi_mul₀
    (a := periodicCoeff w) (p := fun n : ℤ × ℤ => normForm n.1 n.2)
    (F := fun t => (pair w).f t - (pair w).f₀)
    (fun _ => normForm_nonneg _ _) (by linarith : 0 < s.re)
    (fun _ ht => theta_sub_zero_hasSum w ht) hsum
  rwa [(pair_hasMellin w hs).2] at h

theorem latticeL_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s)
      (latticeL w s) := by
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (Real.pi : ℂ) ^ s ≠ 0 := fun h => hπ ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have h := (completed_hasSum w hs).mul_left ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹)
  change HasSum _ ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s)
  convert! h using 1
  funext n
  rw [Complex.cpow_neg]
  field_simp

end SevenEighths.HeckeTheta

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Poisson.BinaryGaussian
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

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem eisEmbedding_eval_norm_sq (x y : ℤ) :
    ‖eisEmbedding (ActualEisensteinCoordinates.eval x y)‖ ^ 2 =
      (x*x-x*y+y*y : ℤ) := by
  rw [eisEmbedding_eval, ← Complex.normSq_eq_norm_sq]
  have hre : ((x : ℂ) + (y : ℂ) * omega3).re =
      (x : ℝ) - (y : ℝ) / 2 := by
    simp [omega3, Complex.add_re, Complex.mul_re]
    ring
  have him : ((x : ℂ) + (y : ℂ) * omega3).im =
      (y : ℝ) * Real.sqrt 3 / 2 := by
    simp [omega3, Complex.add_im, Complex.mul_im]
    ring
  rw [Complex.normSq_apply, hre, him]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  push_cast
  nlinarith


end ActualEisensteinCubic


end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Poisson.GaussianMoments
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
open Filter Real Asymptotics


namespace ActualEisensteinCubic

section

open ShortDraftLatticeCount


theorem rational_qNat_eq_one_iff (x : O) : qNat x = 1 ↔ IsUnit x := by
  rw [qNat_eq_absNorm_span, Ideal.absNorm_eq_one_iff,
    Ideal.span_singleton_eq_top]


end


end ActualEisensteinCubic


end

end OAI

end


