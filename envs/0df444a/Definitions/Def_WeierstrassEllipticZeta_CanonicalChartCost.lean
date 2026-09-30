-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_CanonicalChartCost
-- name    : WeierstrassEllipticZeta_CanonicalChartCost
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T13:49:22.900355+00:00
-- url     : https://prove2.me/theorems/280c1d1a-850d-4901-a797-2df74951d590
-- title:
--   Canonical positive costs for capped elliptic chart budgets
-- statement:
--   Fix a chart c and a point z. For each of the three capped derivative blocks, collect the localized quotient lengths at primes that lie below evaluation at z and are minimal primes of both the current block ideal and the next block ideal. Define cappedChartLengthValues as the set of their natural-number lengths, and cappedChartCost E(c,z) as the maximum of 1 and the supremum of that set.
--
--   Finiteness of the set, finiteness of each actual localized length, and the assertion that E is the least positive valid budget are theorems, not assumptions in these definitions. The cost is a classical finite-maximum description; no algorithm for calculating primary components or numerical degree bound is built in.
-- source:
--   Canonical positive local costs for the current A.1 capped-budget interface. Noetherian minimal-prime finiteness is Stacks Project Lemma 10.31.6, https://stacks.math.columbia.edu/tag/00FR. Finite length of the quotient localized at a minimal prime follows from the local-support criterion, Lemma 10.62.3, https://stacks.math.columbia.edu/tag/00L5; the Lean proof uses the equivalent zero-dimensional Noetherian-to-Artinian criterion. E(c,z) is the maximum of 1 and the finite set of lengths tested by the budget. It is the least positive budget at that chart point. For k nonempty labels, minimizing the old weights gives k*E(c,z) <= sum_i e_i, since the budget predicate is label-independent. This finite-maximum construction is derived for the mission's interface, not quoted from Kumar's Appendix A. The equivalent frontier retains W and C. No algorithm for computing components, bidegree estimate, or proof of the remaining uniform k*E bound is asserted.

import Definitions.Def_WeierstrassEllipticZeta_CappedChartJets
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Lattice.Nat

noncomputable section
namespace WeierstrassEllipticZeta

/-- Length values of precisely the persistent minimal components tested by a capped budget. -/
def cappedChartLengthValues (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (c : Fin 2) (z : ℂ) : Set ℕ :=
  {n | ∃ (i : Fin 3) (p : PrimeSpectrum (MvPolynomial (Fin 4) ℂ)),
    p.asIdeal ≤ RingHom.ker (MvPolynomial.eval (extensionChartCoordinates S c z)) ∧
    p.asIdeal ∈ (extensionChartJetIdeal L Q c (min (i.val * T) N)).minimalPrimes ∧
    p.asIdeal ∈ (extensionChartJetIdeal L Q c (min ((i.val + 1) * T) N)).minimalPrimes ∧
    n = (Module.length (Localization.AtPrime p.asIdeal)
      ((Localization.AtPrime p.asIdeal) ⧸
        (extensionChartJetIdeal L Q c (min (i.val * T) N)).map
          (algebraMap (MvPolynomial (Fin 4) ℂ) (Localization.AtPrime p.asIdeal)))).toNat}

/-- The least positive budget at a fixed chart point; finiteness and optimality are proved separately. -/
def cappedChartCost (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (c : Fin 2) (z : ℂ) : ℕ :=
  max 1 (sSup (cappedChartLengthValues L S Q N T c z))

end WeierstrassEllipticZeta


