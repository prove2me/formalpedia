-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteExponentialTaylor
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteExponentialTaylor
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:56.433196+00:00
-- url     : https://prove2.me/theorems/382b8c12-08be-4e45-986b-d35b060576e0
-- title:
--   Computable analysis · FiniteExponentialTaylor · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteExponentialTaylor.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FinitePolynomialCalculus

set_option autoImplicit true

/-!
# Finite exponential Taylor enclosures

This module gives a potential-infinity remainder certificate for the rational
exponential Taylor prefixes.  Every object below is a finite rational sum.
The executable schedule chooses a first omitted degree; the main theorem says
that every later finite prefix stays in one explicit rational interval around
the scheduled prefix.

There is no completed infinite sum, classical limit, completeness argument,
or Mathlib dependency in this construction.
-/

namespace ComputableAnalysis

namespace FiniteExponentialTaylor

/-- A finite block of exponential Taylor monomials, beginning at `start`.

`remainderPartial x start terms` is the rational sum of exactly `terms`
monomials, with degrees `start, ..., start + terms - 1`. -/
def remainderPartial (x : Rat) (start : Nat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      remainderPartial x start terms +
        FormalPowerSeries.expCoeff (start + terms) * x ^ (start + terms)

/-- Rewriting the integrated-prefix recurrence in the usual factorial
monomial form.  This is an identity in rational arithmetic. -/
theorem expCoeff_succ_monomial (x : Rat) (n : Nat) :
    FormalPowerSeries.expCoeff (n + 1) * x ^ (n + 1) =
      FormalPowerSeries.expCoeff n *
        (x ^ (n + 1) / ((n + 1 : Nat) : Rat)) := by
  unfold FormalPowerSeries.expCoeff
  rw [FormalPowerSeries.factorialRat_succ,
    Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The difference between two finite exponential Taylor prefixes is exactly
the intervening finite block of factorial monomials. -/
theorem remainderPartial_eq_expTaylorPrefix_sub
    (x : Rat) (n terms : Nat) :
    remainderPartial x (n + 1) terms =
      FinitePolynomial.expTaylorPrefix (n + terms) x -
        FinitePolynomial.expTaylorPrefix n x := by
  induction terms with
  | zero =>
      rw [Nat.add_zero, remainderPartial]
      grind [Rat.sub_eq_add_neg]
  | succ terms ih =>
      rw [remainderPartial, ih]
      rw [show n + (terms + 1) = (n + terms) + 1 by omega,
        FinitePolynomial.expTaylorPrefix_succ]
      have hindex : n + 1 + terms = n + terms + 1 := by omega
      rw [hindex]
      rw [expCoeff_succ_monomial]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- On the rational interval `|x| <= C`, a finite remainder block is bounded
by the corresponding finite factorial majorant. -/
theorem remainderPartial_abs_le_factorialTailPartial
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C)
    (start terms : Nat) :
    qabs (remainderPartial x start terms) <=
      RationalMajorant.factorialTailPartial C start terms := by
  induction terms with
  | zero =>
      rw [remainderPartial, RationalMajorant.factorialTailPartial]
      exact Rat.le_refl
  | succ terms ih =>
      rw [remainderPartial, RationalMajorant.factorialTailPartial]
      have hterm :=
        FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
          hC hx (start + terms)
      calc
        qabs
            (remainderPartial x start terms +
              FormalPowerSeries.expCoeff (start + terms) *
                x ^ (start + terms)) <=
            qabs (remainderPartial x start terms) +
              qabs
                (FormalPowerSeries.expCoeff (start + terms) *
                  x ^ (start + terms)) :=
          qabs_add_le _ _
        _ <= RationalMajorant.factorialTailPartial C start terms +
            RationalMajorant.factorialTailTerm C (start + terms) :=
          rat_add_le_add ih hterm

/-- Explicit finite Taylor-prefix remainder bound.  If the first omitted
degree is far enough into the factorial tail, every later finite prefix is
within twice that first omitted majorant term. -/
theorem expTaylorPrefix_remainder_le_two_first_omitted
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C)
    (n terms : Nat)
    (hstart : C <= (((n + 2 : Nat) : Rat) / 2)) :
    qabs
        (FinitePolynomial.expTaylorPrefix (n + terms) x -
          FinitePolynomial.expTaylorPrefix n x) <=
      2 * RationalMajorant.factorialTailTerm C (n + 1) := by
  rw [← remainderPartial_eq_expTaylorPrefix_sub]
  exact Rat.le_trans
    (remainderPartial_abs_le_factorialTailPartial hC hx (n + 1) terms)
    (RationalMajorant.factorialTailPartial_bound hC hstart terms)

/-- Executable first omitted degree for a bounded interval and a positive
rational error request. -/
def scheduledTailStart (C : Rat) (eps : QPos) : Nat :=
  RationalMajorant.factorialTailStart C +
    RationalMajorant.halfDecayShift
      (2 * RationalMajorant.factorialTailTerm C
        (RationalMajorant.factorialTailStart C)) eps

/-- Degree of the finite prefix immediately before `scheduledTailStart`. -/
def scheduledPrefixDegree (C : Rat) (eps : QPos) : Nat :=
  scheduledTailStart C eps - 1

theorem scheduledTailStart_pos (C : Rat) (eps : QPos) :
    0 < scheduledTailStart C eps := by
  unfold scheduledTailStart RationalMajorant.factorialTailStart
  omega

theorem scheduledPrefixDegree_succ (C : Rat) (eps : QPos) :
    scheduledPrefixDegree C eps + 1 = scheduledTailStart C eps := by
  unfold scheduledPrefixDegree
  have hpos := scheduledTailStart_pos C eps
  omega

/-- Potential-infinity form of the exponential Taylor remainder theorem.

For every rational `x` in `[-C,C]`, the scheduled finite prefix is within
`eps` of every extension by any finite number of terms.  The quantification
is solely over later finite stages. -/
theorem scheduled_expTaylorPrefix_remainder_le
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C)
    (eps : QPos) (extraTerms : Nat) :
    qabs
        (FinitePolynomial.expTaylorPrefix
            (scheduledPrefixDegree C eps + extraTerms) x -
          FinitePolynomial.expTaylorPrefix
            (scheduledPrefixDegree C eps) x) <=
      eps.val := by
  have hfinite := remainderPartial_abs_le_factorialTailPartial
    hC hx (scheduledTailStart C eps) extraTerms
  have heps := RationalMajorant.factorialTailPartial_shifted_le_eps
    hC eps extraTerms
  have hbound :
      qabs (remainderPartial x (scheduledTailStart C eps) extraTerms) <=
        eps.val := by
    exact Rat.le_trans hfinite (by simpa [scheduledTailStart] using heps)
  rw [← scheduledPrefixDegree_succ C eps] at hbound
  rw [remainderPartial_eq_expTaylorPrefix_sub] at hbound
  exact hbound

/-- Explicit rational enclosure for every later finite exponential Taylor
prefix at every point of the bounded interval `|x| <= C`. -/
theorem scheduled_expTaylorPrefix_enclosure
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C)
    (eps : QPos) (extraTerms : Nat) :
    let center := FinitePolynomial.expTaylorPrefix
      (scheduledPrefixDegree C eps) x
    let later := FinitePolynomial.expTaylorPrefix
      (scheduledPrefixDegree C eps + extraTerms) x
    center - eps.val <= later /\ later <= center + eps.val := by
  dsimp
  let difference : Rat :=
    FinitePolynomial.expTaylorPrefix
        (scheduledPrefixDegree C eps + extraTerms) x -
      FinitePolynomial.expTaylorPrefix (scheduledPrefixDegree C eps) x
  have hrem : qabs difference <= eps.val := by
    simpa [difference] using
      scheduled_expTaylorPrefix_remainder_le hC hx eps extraTerms
  have hlo : -eps.val <= difference :=
    Rat.le_trans (Rat.neg_le_neg hrem) (neg_qabs_le_self difference)
  have hhi : difference <= eps.val :=
    Rat.le_trans (self_le_qabs difference) hrem
  dsimp [difference] at hlo hhi
  constructor <;> grind [Rat.sub_eq_add_neg]

end FiniteExponentialTaylor

end ComputableAnalysis


