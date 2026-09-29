-- Prove2me | Definitions.Def_WeierstrassCurve_ModularityLiftingConductor
-- name    : WeierstrassCurve_ModularityLiftingConductor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/d80ebc41-f15c-56c5-9b82-19a2f2fb9597
-- title:
--   Modularity lifting with level pinned to the conductor
-- statement:
--   Three propositions about integral Weierstrass models are named here. First, `IsModularModelOfExactConductorLevel W` (an abbreviation for [`Mlc1IsModularModelOfExactConductorLevel`](../def/WeierstrassCurve_Mlc1RowStatement.html#L9)) asserts the existence of a natural number $N > 0$ that is squarefree, whose prime divisors are exactly the primes $q$ with $q \mid \Delta_W$ (the equivalence $q \mid N \iff q \mid \Delta_W$ being required for every prime $q$), and such that `W.IsModularModelOfLevel N` holds: there is a cusp form $f$ of weight $2$ for $\Gamma_0(N)$ whose $q$-expansion coefficients satisfy the normalised-eigenform recursions (first coefficient $1$, multiplicativity at coprime indices, and the two prime-power recursions according as the prime divides $N$ or not), with $a_p(f) = a_p(W)$ for every prime $p$ with $p \nmid \Delta_W$ and $p \nmid N$; here $a_p(W)$ is $p + 1$ minus the number of points of the reduction of the chosen model modulo $p$. Second, `ModularityLiftingAtConductor p` (an abbreviation for [`Mlc1ModularityLiftingAtConductor`](../def/WeierstrassCurve_Mlc1RowStatement.html#L14)) says that every $W$ over $\mathbb{Z}$ with $\Delta_W \neq 0$, with $q \nmid c_4(W)$ for each prime $q \mid \Delta_W$, with irreducible mod-$p$ representation in the sense of `ModRepIsIrreducible` (the $p$-torsion of the base change of $W$ to $\overline{\mathbb{Q}}$ is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $\bot$ and $\top$), and residually modular at $p$ in the sense of `IsResiduallyModular` (a normalised eigenform of weight $2$ and some positive level $M$ whose coefficients at primes $\ell \neq p$ good for $W$ and not dividing $M$ are congruent to $a_\ell(W)$ modulo a maximal ideal of $\overline{\mathbb{Z}} \subset \mathbb{C}$ containing $p$), satisfies the exact-conductor-level conclusion above. Third, `ModularityLiftingAtConductorOrdinary p` is the same implication with the extra hypothesis $p \mid \Delta_W$ or $p \nmid a_p(W)$. All three are conditions on a chosen integral model, and residual modularity is a congruence of coefficients rather than an isomorphism of representations. A classical decidable-equality instance on $\overline{\mathbb{Q}}$ is also provided.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve`, cusp forms for $\Gamma_0(N)$ and $q$-expansions; the notions of modular model, $a_p$ of a model, semistable model, irreducibility of the mod-$p$ representation and residual modularity used here are the project's own.
--
--   **Where it is used.** These are the consumer-form statements of Taylor–Wiles modularity lifting used in the Fermat argument: the conclusion supplies a squarefree level supported exactly on the primes of bad reduction, which is what the transport step of the $3$–$5$ switch and the level-lowering descent both require.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ModularityLiftingConductor.lean

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_WeierstrassCurve_Mlc1RowStatement
import Definitions.Def_WeierstrassCurve_ModularityProps
import Definitions.Def_WeierstrassCurve_Semistability
import Definitions.Def_WeierstrassCurve_ThreeFiveSwitchConditioned

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

abbrev IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  Mlc1IsModularModelOfExactConductorLevel W

namespace IsModularModelOfExactConductorLevel

end IsModularModelOfExactConductorLevel

abbrev ModularityLiftingAtConductor (p : ℕ) : Prop :=
  Mlc1ModularityLiftingAtConductor p

def ModularityLiftingAtConductorOrdinary (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) →
    W.IsResiduallyModular p → W.IsModularModelOfExactConductorLevel

end WeierstrassCurve

namespace FreyPackage

open WeierstrassCurve WeierstrassCurve.Affine.Point FreyCurve

noncomputable local instance instDecEqQbarLedgerStageTwo :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

end FreyPackage

end


