-- Prove2me | Definitions.Def_WeierstrassCurve_ThreeFiveSwitchConditioned
-- name    : WeierstrassCurve_ThreeFiveSwitchConditioned
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/26a460f7-4eef-5afd-a526-5f933f1ea3ae
-- title:
--   Conditioned three–five switch property for integral Weierstrass models
-- statement:
--   This module defines a single predicate, [`WeierstrassCurve.ThreeFiveSwitchCurveAtThreeConditioned`](../def/WeierstrassCurve_ThreeFiveSwitchConditioned.html#L7), on a Weierstrass curve $W$ over $\mathbb{Z}$. It asserts an implication: if the discriminant $\Delta(W)$ is nonzero, if $W$ is a semistable model in the sense that every prime $p$ dividing $\Delta(W)$ fails to divide $c_4(W)$ (`IsSemistableModel`), and if the mod-$5$ representation of $W$ is irreducible — meaning, by `ModRepIsIrreducible`, that the $\mathbb{Z}/5$-module of $5$-torsion points of $W$ base-changed to $\overline{\mathbb{Q}}$ is nontrivial and its only submodules stable under all $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}}$ are $\bot$ and $\top$ — then there exists a further Weierstrass curve $W'$ over $\mathbb{Z}$ with the following properties. First, $\Delta(W')\neq 0$ and $W'$ is again a semistable model. Second, the mod-$3$ representation of $W'$ is irreducible in the same sense, and it has a unipotent element (`ModRepHasUnipotent`): some $\sigma \in \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ acts on the $3$-torsion by an endomorphism $\rho(\sigma)$ with $(\rho(\sigma)-1)^2 = 0$ and $\rho(\sigma) - 1 \neq 0$. Third, a conditional clause at $3$: if $3 \mid \Delta(W)$ or $3 \nmid a_3(W)$, then likewise $3 \mid \Delta(W')$ or $3 \nmid a_3(W')$; here `IsGoodPrimeFor` $\ell$ means $\ell \nmid \Delta$, and `apOfModel` $\ell$ is $\#\mathbb{Z}/\ell + 1$ minus the number of points of the reduction of the model modulo $\ell$. Fourth, for every prime $\ell \neq 5$ at which both $W$ and $W'$ are good, $5 \mid a_\ell(W') - a_\ell(W)$. The link between $W'$ and $W$ is thus a congruence of Frobenius traces modulo $5$ at primes good for both models, not an asserted isomorphism of mod-$5$ representations; and all the conditions are conditions on the chosen integral models, phrased through $\Delta$, $c_4$ and point counts of reductions.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve` over $\mathbb{Z}$ together with $\Delta$, $c_4$, base change and affine point groups; semistability of a model, mod-$n$ irreducibility and the existence of a unipotent element in the mod-$n$ image, good primes, and the Frobenius trace of a reduction are the project's own definitions, built from the $\mathbb{Z}/n$-module of $n$-torsion points over `AlgebraicClosure ℚ` and from point counts of reductions.
--
--   **Where it is used.** In the route to Fermat's Last Theorem one must treat Frey curves whose mod-$3$ representation is reducible, where only mod-$5$ irreducibility is available; the three–five switch replaces such a curve by a semistable curve with irreducible mod-$3$ representation whose Frobenius traces are congruent to the original ones modulo $5$, so that modularity can be transported back along the congruence. This variant conditions the behaviour at $3$ of the new curve on that of the original curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ThreeFiveSwitchConditioned.lean

import Definitions.Def_WeierstrassCurve_ModularityProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve

def ThreeFiveSwitchCurveAtThreeConditioned (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible 5 →
    ∃ W' : WeierstrassCurve ℤ, W'.Δ ≠ 0 ∧ W'.IsSemistableModel ∧
      W'.ModRepIsIrreducible 3 ∧ W'.ModRepHasUnipotent 3 ∧
      ((¬ W.IsGoodPrimeFor 3 ∨ ¬ (3 : ℤ) ∣ W.apOfModel 3) →
        (¬ W'.IsGoodPrimeFor 3 ∨ ¬ (3 : ℤ) ∣ W'.apOfModel 3)) ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 →
        (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ)

end WeierstrassCurve


