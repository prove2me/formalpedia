-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaFix
-- name    : RPLib_S4_TameInertiaFix
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:43:48.928193+00:00
-- url     : https://prove2.me/theorems/67dfb0be-0c8e-4983-9eac-496ed6964cbf
-- title:
--   The Abhyankar polynomial and the inertia-fixed small root
-- statement:
--   In characteristic $p$ let $$G = X^{N(p+1)} - f X^N + 1 \in A[X].$$ Every root $z$ satisfies $z G'(z) = -N$, so all roots lie in $K_U$ when $N$ is a unit of $A$ (by the unit-derivative criterion). Inertia elements preserve $v_P(w) < 1$; an inertia element fixes the unique root $w$ with $v_P(w) < 1$ of the split trinomial $X^{p+1} - F X + 1$ when $v_P(F) > 1$ and $F$ is fixed; a pole of $a \in K$ at $x = Q \cap R_0$ is a pole at $Q \cap B_L$ for every finite level $L$; and pro-chart inertia elements fix the small root at a finite Galois level.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   S. S. Abhyankar, Coverings of algebraic curves, Amer. J. Math. 79 (1957), 825-856; J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter IV, Section 2

import Mathlib
import Definitions.Def_RPLib_S4_TameInertiaUnr
import Definitions.Def_RPLib_S4_TameInertiaNewton
import Definitions.Def_RPLib_S4_TameInertiaUp

/-!
# Tame inertia, part Fix: the Abhyankar polynomial and the inertia-fixed small root (S4-PD item (2), T5 applied + T7)

* `abhy p N f = X^(N(p+1)) - f X^N + 1 ∈ A[X]`; in characteristic `p`, `z · G'(z) = -N` at every root
  (`abhy_ud`), so every root lies in `K_U` when `N` is a unit of `A` (`mem_maxUnram_abhy`).
* `valuation_smul_lt_one`: an inertia element preserves `v_P(w) < 1`.
* `fix_small_root`: an inertia element fixes the unique root `w` with `v_P(w) < 1` of a split trinomial
  `X^(p+1) - F X + 1` with `1 < v_P(F)` and `F` fixed (Newton uniqueness, `trin_existsUnique_small`).
* `one_lt_valuation_level`: a pole of `a ∈ K` at `x = Q ∩ R0` is a pole at the prime `Q ∩ B_L` of every level.
* `fix_of_inertia_small`: pro-chart inertia elements fix the small root at a finite Galois level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

section Abhy

variable {A : Type} [CommRing A]

/-- The Abhyankar polynomial `X^(N(p+1)) - f X^N + 1`. -/
def abhy (p N : ℕ) (f : A) : A[X] := X ^ (N * (p + 1)) - C f * X ^ N + 1

theorem aeval_abhy {R : Type*} [CommRing R] [Algebra A R] (p N : ℕ) (f : A) (y : R) :
    aeval y (abhy p N f) = (y ^ N) ^ (p + 1) - algebraMap A R f * y ^ N + 1 := by
  simp [abhy, pow_mul]

theorem abhy_monic [Nontrivial A] {p N : ℕ} (hp : 0 < p) (hN : 0 < N) (f : A) : (abhy p N f).Monic := by
  have h : abhy p N f = X ^ (N * (p + 1)) + (C (-f) * X ^ N + C 1) := by
    rw [abhy, C_neg, C_1]; ring
  rw [h]
  refine monic_X_pow_add ?_
  calc degree (C (-f) * X ^ N + C 1) ≤ (N : WithBot ℕ) :=
        (degree_add_le _ _).trans (max_le (degree_C_mul_X_pow_le _ _)
          (degree_C_le.trans (by exact_mod_cast Nat.zero_le N)))
    _ < ((N * (p + 1) : ℕ) : WithBot ℕ) := by exact_mod_cast (show N < N * (p + 1) by nlinarith)

theorem aeval_derivative_abhy {R : Type*} [CommRing R] [Algebra A R] (p : ℕ) {N : ℕ} (hN : N ≠ 0)
    (f : A) (y : R) :
    y * aeval y (derivative (abhy p N f)) =
      ((N * (p + 1) : ℕ) : R) * y ^ (N * (p + 1)) - (N : R) * (algebraMap A R f * y ^ N) := by
  have h1 : N * (p + 1) ≠ 0 := Nat.mul_ne_zero hN (Nat.succ_ne_zero p)
  rw [abhy, derivative_add, derivative_sub, derivative_C_mul, derivative_X_pow, derivative_X_pow,
    derivative_one, add_zero]
  simp only [map_sub, map_mul, aeval_C, aeval_X_pow, map_natCast]
  rw [← mul_pow_sub_one h1 y, ← mul_pow_sub_one hN y]
  ring

/-- In characteristic `p`, the Abhyankar polynomial has the unit-derivative property `z · G'(z) = -N`. -/
theorem abhy_ud_of_cast {R : Type*} [CommRing R] [Algebra A R] {p : ℕ} (hp : (p : R) = 0) {N : ℕ}
    (hN : N ≠ 0) (f : A) {y : R} (hy : aeval y (abhy p N f) = 0) :
    y * aeval y (derivative (abhy p N f)) = -(N : R) := by
  rw [aeval_derivative_abhy p hN f y, pow_mul]
  rw [aeval_abhy] at hy
  push_cast
  linear_combination (N : R) * hy + ((N : R) * (y ^ N) ^ (p + 1)) * hp

variable {K : Type} [Field K] [Algebra A K]

theorem abhy_ud {p : ℕ} [CharP K p] {N : ℕ} (hN : IsUnit (N : A)) (f : A) :
    ∀ y : AlgebraicClosure K, aeval y (abhy p N f) = 0 →
      y * aeval y (derivative (abhy p N f)) = algebraMap A (AlgebraicClosure K) ((-hN.unit : Aˣ) : A) := by
  intro y hy
  have : Nontrivial A := (algebraMap A (AlgebraicClosure K)).domain_nontrivial
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hN
    exact not_isUnit_zero hN
  have hp : (p : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), CharP.cast_eq_zero, map_zero]
  rw [abhy_ud_of_cast hp hN0 f hy, Units.val_neg, IsUnit.unit_spec, map_neg, map_natCast]

/-- **T5 applied.** Every root of the Abhyankar polynomial lies in `K_U`. -/
theorem mem_maxUnram_abhy {p : ℕ} [CharP K p] (hp : 0 < p) {N : ℕ} (hN : IsUnit (N : A)) (f : A)
    {y : AlgebraicClosure K} (hy : aeval y (abhy p N f) = 0) : y ∈ maxUnram A K := by
  have : Nontrivial A := (algebraMap A (AlgebraicClosure K)).domain_nontrivial
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by
    rintro rfl
    rw [Nat.cast_zero] at hN
    exact not_isUnit_zero hN)
  exact mem_maxUnram_of_ud (abhy_monic hp hN0 f) _ (abhy_ud hN f) hy

theorem map_abhy_one {L : Type*} [Field L] [Algebra K L] (p : ℕ) (f : A) :
    ((abhy p 1 f).map (algebraMap A K)).map (algebraMap K L) = trin p (algebraMap K L (algebraMap A K f)) := by
  simp [abhy, trin, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-- The roots of `g = abhy p 1 f` are `N`-th powers of roots of `abhy p N f`. -/
theorem udField_abhy_one_le [Nontrivial A] {p : ℕ} (hp : 0 < p) {N : ℕ} (hN : 0 < N) (f : A) :
    udField A K (abhy p 1 f) ≤ udField A K (abhy p N f) := by
  rw [IntermediateField.adjoin_le_iff]
  intro y hy
  have hy0 := (mem_rootSet.1 hy).2
  rw [aeval_map_algebraMap, aeval_abhy, pow_one] at hy0
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y hN
  have hzr : z ∈ ((abhy p N f).map (algebraMap A K)).rootSet (AlgebraicClosure K) := by
    rw [mem_rootSet]
    refine ⟨((abhy_monic hp hN f).map (algebraMap A K)).ne_zero, ?_⟩
    rw [aeval_map_algebraMap, aeval_abhy, hz]
    exact hy0
  rw [← hz]
  exact pow_mem (IntermediateField.subset_adjoin K _ hzr) N

end Abhy

section Gen

variable {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
  {G : Type*} [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : B), σ • algebraMap B L s = algebraMap B L (σ • s))

include hc in
/-- Inertia elements preserve `v_P(w) < 1`. -/
theorem valuation_smul_lt_one (P : HeightOneSpectrum B) {σ : G} (hσ : σ ∈ P.asIdeal.inertia G) {w : L}
    (hw : P.valuation L w < 1) : P.valuation L (σ • w) < 1 := by
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer w hw.le
  have hd1 : P.valuation L (algebraMap B L d) = 1 := (P.valuation_eq_one_iff_notMem (K := L)).2 d.2
  have hn : n ∈ P.asIdeal := by
    refine (P.valuation_lt_one_iff_mem (K := L) n).1 ?_
    show P.valuation L (algebraMap B L n) < 1
    rw [← hnd, map_mul, hd1, mul_one]
    exact hw
  have hσn : σ • n ∈ P.asIdeal := by
    have h := P.asIdeal.add_mem (AddSubgroup.mem_inertia.1 hσ n) hn
    rwa [sub_add_cancel] at h
  have hσd : σ • (d : B) ∉ P.asIdeal := fun h => d.2 (by
    have h' := P.asIdeal.sub_mem h (AddSubgroup.mem_inertia.1 hσ (d : B))
    rwa [sub_sub_cancel] at h')
  have hmul : σ • w * algebraMap B L (σ • (d : B)) = algebraMap B L (σ • n) := by
    rw [← hc, ← hc, ← smul_mul', hnd]
  have h1 : P.valuation L (algebraMap B L (σ • (d : B))) = 1 :=
    (P.valuation_eq_one_iff_notMem (K := L)).2 hσd
  have h2 : P.valuation L (algebraMap B L (σ • n)) < 1 := (P.valuation_lt_one_iff_mem (K := L) _).2 hσn
  rw [← hmul, map_mul, h1, mul_one] at h2
  exact h2

include hc in
/-- **T7 (level form).** An inertia element fixing `F` fixes the unique small root of the split trinomial. -/
theorem fix_small_root (P : HeightOneSpectrum B) {p : ℕ} (hp : 0 < p) {F : L} (hF : 1 < P.valuation L F)
    (hs : (trin p F).Splits) {σ : G} (hσ : σ ∈ P.asIdeal.inertia G) (hσF : σ • F = F) {w : L}
    (hw : (trin p F).IsRoot w) (hwv : P.valuation L w < 1) : σ • w = w := by
  obtain ⟨w₀, -, huniq⟩ := trin_existsUnique_small (P.valuation L) hp hF hs
  have hr : (trin p F).IsRoot (σ • w) := by
    have h := congrArg (fun t => σ • t) ((trin_isRoot_iff p F w).1 hw)
    simp only [smul_add, smul_sub, smul_mul', smul_pow', smul_one, smul_zero, hσF] at h
    exact (trin_isRoot_iff p F _).2 h
  exact (huniq (σ • w) ⟨hr, valuation_smul_lt_one hc P hσ hwv⟩).trans (huniq w ⟨hw, hwv⟩).symm

end Gen

section Level

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

/-- A pole at `x = Q ∩ R0` is a pole at the prime `Q ∩ B_L` of every finite level. -/
theorem one_lt_valuation_level {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    {Q : Ideal (proChart A K R0)} (x : HeightOneSpectrum R0)
    (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    (P : HeightOneSpectrum (integralClosure R0 L)) (hP : P.asIdeal = Q.comap (inclU R0 hLU))
    {a : K} (ha : 1 < x.valuation K a) : 1 < P.valuation L (algebraMap K L a) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact not_lt_of_ge zero_le' ha
  have hinv : x.valuation K a⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ ha
  obtain ⟨n, d, hnd⟩ := x.exists_primeCompl_mul_eq_of_integer a⁻¹ hinv.le
  have hn : n ∈ x.asIdeal := by
    refine (x.valuation_lt_one_iff_mem (K := K) n).1 ?_
    show x.valuation K (algebraMap R0 K n) < 1
    rw [← hnd, map_mul, (x.valuation_eq_one_iff_notMem (K := K)).2 d.2, mul_one]
    exact hinv
  have hmem : ∀ r : R0, algebraMap R0 (integralClosure R0 L) r ∈ P.asIdeal ↔ r ∈ x.asIdeal := by
    intro r
    rw [hP, hx, Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  have h1 : P.valuation L (algebraMap _ L (algebraMap R0 (integralClosure R0 L) (d : R0))) = 1 :=
    (P.valuation_eq_one_iff_notMem (K := L)).2 fun h => d.2 ((hmem d).1 h)
  have h2 : P.valuation L (algebraMap _ L (algebraMap R0 (integralClosure R0 L) n)) < 1 :=
    (P.valuation_lt_one_iff_mem (K := L) _).2 ((hmem n).2 hn)
  have hL : (algebraMap K L a)⁻¹ * algebraMap _ L (algebraMap R0 (integralClosure R0 L) (d : R0)) =
      algebraMap _ L (algebraMap R0 (integralClosure R0 L) n) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R0 K L, IsScalarTower.algebraMap_apply R0 K L n, ← map_inv₀, ← map_mul, hnd]
  rw [← hL, map_mul, h1, mul_one, map_inv₀] at h2
  have hpos : 0 < P.valuation L (algebraMap K L a) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 ha0))
  exact (inv_lt_one₀ hpos).1 h2

/-- **T7.** Pro-chart inertia elements fix the small root of the trinomial at a finite Galois level. -/
theorem fix_of_inertia_small {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] [IsGalois K L]
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    {Q : Ideal (proChart A K R0)} (P : HeightOneSpectrum (integralClosure R0 L))
    (hP : P.asIdeal = Q.comap (inclU R0 hLU)) {p : ℕ} (hp : 0 < p) {a : K}
    (hF : 1 < P.valuation L (algebraMap K L a)) (hs : (trin p (algebraMap K L a)).Splits) {w : L}
    (hw : (trin p (algebraMap K L a)).IsRoot w) (hwv : P.valuation L w < 1) {σ : Pi1 A K}
    (hσ : σ ∈ Q.inertia (Pi1 A K)) :
    σ (IntermediateField.inclusion hLU w) = IntermediateField.inclusion hLU w := by
  obtain ⟨τ, hτ⟩ := exists_restrict hLU σ
  have hτI := restrict_mem_inertia hLU hσ hτ
  rw [← hP] at hτI
  have hfix : τ • w = w := fix_small_root (fun _ _ => rfl) P hp hF hs hτI (τ.commutes a) hw hwv
  apply Subtype.ext
  rw [← hτ w]
  exact congrArg Subtype.val hfix

end Level

end

end TameInertia
end RamanujanPetersson


