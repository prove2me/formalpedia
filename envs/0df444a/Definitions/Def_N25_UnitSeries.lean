-- Prove2me | Definitions.Def_N25_UnitSeries
-- name    : N25_UnitSeries
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:39.485661+00:00
-- url     : https://prove2.me/theorems/9f2ad280-9d0d-4419-9126-7187a93f5ef2
-- title:
--   Integral $q$-series for the five level-$25$ units
-- statement:
--   The file fixes the residue pairs $$(1,7),(2,11),(3,4),(6,8),(9,12)$$ and the $q$-orders $(1,-1,2,1,-3)$. From stabilized Euler products $E_g(q)=∏_{m≥0}(1-q^{25m+g})(1-q^{25(m+1)-g})$, it defines pair series, the common denominator corresponding to $Δ^3$, numerator series, and normalized Laurent series for five units. These are the integral $q$-expansions used throughout the modular-unit argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
set_option autoImplicit false

noncomputable section
open scoped BigOperators
namespace N25

/-- The five pairs of residues defining the unpowered Siegel ratios. -/
def unitResidues25 : Fin 5 → ℕ × ℕ :=
  ![(1, 7), (2, 11), (3, 4), (6, 8), (9, 12)]

/-- Orders of the five ratios at the q-place. -/
def unitQOrder25 : Fin 5 → ℤ := ![1, -1, 2, 1, -3]

/-- The integral Euler product, defined by its stabilized coefficients. -/
def etaResidueSeries25 (g : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    PowerSeries.coeff n
      (∏ m ∈ Finset.range (n + 1),
        ((1 - PowerSeries.X ^ (25 * m + g)) *
          (1 - PowerSeries.X ^ (25 * (m + 1) - g)) : PowerSeries ℤ))

def unitPairSeries25 (i : Fin 5) : PowerSeries ℤ :=
  etaResidueSeries25 (unitResidues25 i).1 *
    etaResidueSeries25 (unitResidues25 i).2

/-- The integral expansion of the common denominator, the cube of the discriminant. -/
def unitDenominatorSeries25 : PowerSeries ℤ :=
  (PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ 3

def unitNumeratorSeries25 (i : Fin 5) : PowerSeries ℤ :=
  PowerSeries.X ^ (3 + unitQOrder25 i).toNat *
    ModularCurve.dedekindEtaUnit ^ 3 *
    unitPairSeries25 i *
    (unitPairSeries25 (i + 1)).invOfUnit (1 : ℤˣ)

/-- The normalized integral Laurent expansion of each unpowered unit. -/
def unitSeries25 (K : Type*) [Field K] (i : Fin 5) : LaurentSeries K :=
  ModularCurve.intSeriesC K (unitNumeratorSeries25 i) /
    ModularCurve.intSeriesC K unitDenominatorSeries25

end N25


