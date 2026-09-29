-- Prove2me | Definitions.Def_WeierstrassCurve_Mlc1RowStatement
-- name    : WeierstrassCurve_Mlc1RowStatement
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/85d80272-df5b-5787-a632-5be0c22e9f3f
-- title:
--   Exact-support modular level; modularity lifting at p=3 and p=5
-- statement:
--   Three propositions about integral Weierstrass models are introduced. First, [`Mlc1IsModularModelOfExactConductorLevel W`](../def/WeierstrassCurve_Mlc1RowStatement.html#L9), for $W$ a Weierstrass curve over $\mathbb{Z}$, asserts the existence of a natural number $N>0$ that is squarefree, whose prime divisors are exactly the primes $q$ with $q \mid \Delta(W)$ (an if-and-only-if, so no bad prime of the chosen model is allowed to be missing from the level and no good prime may divide it), and for which `W.IsModularModelOfLevel N` holds: there is a weight-two cusp form $f$ on $\Gamma_0(N)$ satisfying the project's `IsNormalizedEigenform` conditions — first $q$-coefficient $1$, multiplicativity of the coefficients at coprime indices, and the two Hecke recursions at prime powers, the one with the $p\,a_{p^r}$ term for $p \nmid N$ and the one without it for $p \mid N$ — such that for every prime $p$ with $p \nmid \Delta(W)$ and $p \nmid N$ one has $a_p(f) = p + 1 - \#E_p$, where $\#E_p$ is the number of points of the reduction of $W$ modulo $p$ (the point at infinity included). All of this is a condition on the given model $W$ and its discriminant, not on a minimal model or the conductor proper.
--
--   Second, [`Mlc1ModularityLiftingAtConductor p`](../def/WeierstrassCurve_Mlc1RowStatement.html#L14) asserts that every $W$ over $\mathbb{Z}$ with $\Delta(W) \neq 0$ which is semistable in the project's sense (no prime dividing $\Delta(W)$ divides $c_4(W)$), whose mod-$p$ representation is irreducible (the $\mathbb{Z}/p$-module of $p$-torsion points of $W$ over $\overline{\mathbb{Q}}$ is nontrivial and has no Galois-stable submodule other than $\bot$ and $\top$), and which is residually modular at $p$ (for some level $M>0$ there are a normalized weight-two eigenform on $\Gamma_0(M)$ and a maximal ideal $\mathfrak{m}$ of $\overline{\mathbb{Z}} \subset \mathbb{C}$ containing $p$ with $a_\ell(f) \equiv a_\ell(W) \bmod \mathfrak{m}$ for all primes $\ell \neq p$ good for $W$ with $\ell \nmid M$), satisfies the exact-support conclusion above. No further restriction on $M$ is imposed. Third, [`Mlc1RowStatement`](../def/WeierstrassCurve_Mlc1RowStatement.html#L18) is the conjunction of this for $p = 3$ and $p = 5$.
--
--   **Relation to Mathlib.** The ambient objects — `WeierstrassCurve` over a commutative ring, affine points, `CuspForm` for `CongruenceSubgroup.Gamma0 N` of weight $2$, the $q$-expansion used to define coefficients, and `Squarefree` — are Mathlib's. Mathlib has no notion of a normalized Hecke eigenform, of a Weierstrass model being modular of a given level, of semistability of a model, or of the mod-$n$ Galois representation on torsion points and its irreducibility; these are the project's own definitions, phrased throughout as conditions on a chosen integral model and on its discriminant $\Delta$ and invariant $c_4$.
--
--   **Where it is used.** These predicates package the conclusion and the hypotheses of the modularity lifting step ($R = \mathbb{T}$, Taylor–Wiles patching) for semistable curves, in the form in which it is combined with Langlands–Tunnell at $p = 3$ and with the $3$–$5$ switch at $p = 5$. The exact-support condition on the level is what allows the resulting modular form to be fed into the level-lowering argument applied to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_Mlc1RowStatement.lean

import Definitions.Def_WeierstrassCurve_ModularityProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

set_option maxHeartbeats 400000

noncomputable section

def Mlc1IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ Squarefree N ∧
    (∀ q : ℕ, q.Prime → (q ∣ N ↔ (q : ℤ) ∣ W.Δ)) ∧
    W.IsModularModelOfLevel N

def Mlc1ModularityLiftingAtConductor (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    W.IsResiduallyModular p → Mlc1IsModularModelOfExactConductorLevel W

def Mlc1RowStatement : Prop :=
  ∀ (p : ℕ), p = 3 ∨ p = 5 → Mlc1ModularityLiftingAtConductor p

end


