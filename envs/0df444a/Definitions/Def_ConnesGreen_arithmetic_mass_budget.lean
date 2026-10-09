-- Prove2me | Definitions.Def_ConnesGreen_arithmetic_mass_budget
-- name    : ConnesGreen_arithmetic_mass_budget
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-09T00:39:56.341647+00:00
-- url     : https://prove2.me/theorems/8867a340-041e-4275-b6cb-b1140929da8c
-- title:
--   Original active prime weights, physical test energy and archimedean bracket
-- statement:
--   For a real support radius $T$, let $A_T=\{n\in\mathbb N:\ n\text{ is a prime power},\ \log n<2T\}$. This finite set defines the exact active prime weight $P_T=\sum_{n\in A_T}\Lambda(n)/\sqrt n$. For a compact smooth complex test $g$, write $M(g)=\int_{\mathbb R}|g|^2$ and $E(g)=\int_{\mathbb R}|g\prime|^2+M(g)/4$. The archimedean bracket is $\gamma(r)=\Re\psi(1/4+ir/2)-\log\pi$. The explicit prime summand is $(\Lambda(n)/\sqrt n)(g(\log n)+g(-\log n))$. These are the existing repository definitions, registered unchanged to express arithmetic estimates on the original canonical Connes test class. No new carrier, zero family or arithmetic hypothesis is introduced.
-- source:
--   Exact original definitions in monocap-tech/weil: PrimeSupport.lean, ExplicitFormulaBridge.lean, NonArchimedeanEnergy.lean, CanonicalGreenMarkerMargin.lean and Upstream/Zeta23/ExplicitFormula.lean; compiling source 8374c1d6419c567e9c1319e441c6a1348d0d0969

import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace WeilDefect
/-- Prime powers active under the compact-window support inequality log n < 2c. -/
def activePrimePowers (c : ℝ) : Set ℕ :=
  {n | IsPrimePow n ∧ Real.log (n : ℝ) < 2 * c}

/--
WD-T34 arithmetic core: for every fixed real support radius, only finitely many
natural prime powers satisfy the strict compact-window inequality log n < 2c.
-/
theorem wd_t34_active_prime_powers_finite (c : ℝ) :
    (activePrimePowers c).Finite := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (Real.exp (2 * c))
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  rcases hn with ⟨hnpp, hnlog⟩
  have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hnpp.two_le
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hnexp : (n : ℝ) < Real.exp (2 * c) :=
    (Real.log_lt_iff_lt_exp hnpos).mp hnlog
  have hnNreal : (n : ℝ) < (N : ℝ) := lt_trans hnexp hN
  exact_mod_cast hnNreal


/-- Finite set of active prime powers at support radius c. -/
noncomputable def activePrimePowerFinset (c : ℝ) : Finset ℕ :=
  (wd_t34_active_prime_powers_finite c).toFinset

@[simp]
theorem mem_activePrimePowerFinset
    (c : ℝ) (n : ℕ) :
    n ∈ activePrimePowerFinset c ↔
      IsPrimePow n ∧ Real.log (n : ℝ) < 2 * c := by
  simp [activePrimePowerFinset, activePrimePowers]


end WeilDefect
namespace ConnesRZArithmetic
def explicitPrimeSummand (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (g (Real.log n) + g (-Real.log n))
end ConnesRZArithmetic
namespace Zeta23.EF
def gammaBracket (r : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi
end Zeta23.EF
namespace ConnesGreen
open WeilDefect
def activePrimeWeight (T : ℝ) : ℝ :=
  ∑ n ∈ activePrimePowerFinset T, ArithmeticFunction.vonMangoldt n / Real.sqrt n

def physicalTestEnergy (g : ℝ → ℂ) : ℝ :=
  (∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)
end ConnesGreen


