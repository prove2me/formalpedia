-- Prove2me | Definitions.Def_WeierstrassCurve_ConductorLevel
-- name    : WeierstrassCurve_ConductorLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/19a6b382-0387-50c4-a2d4-210c57dd92f7
-- title:
--   Conductor level: radical of a Weierstrass discriminant
-- statement:
--   For a Weierstrass curve $W$ over $\mathbb{Z}$ (Mathlib's `WeierstrassCurve ℤ`, i.e. a chosen integral Weierstrass presentation rather than an abstract elliptic curve), [`WeierstrassCurve.conductorLevel W`](../def/WeierstrassCurve_ConductorLevel.html#L11) is defined to be `radical W.Δ.natAbs`, the radical in the unique factorisation monoid $\mathbb{N}$ of the absolute value of the discriminant $\Delta(W)$: the product of the distinct primes dividing $\Delta(W)$. It is thus an invariant of the model, not of the isomorphism class, and it is by construction a squarefree positive natural number supported exactly on the primes dividing $\Delta(W)$; note the degenerate case $\Delta(W)=0$, where the radical of $0$ is $1$, so the definition returns $1$.
--
--   Three accompanying facts are recorded. [`WeierstrassCurve.conductorLevel_pos`](../def/WeierstrassCurve_ConductorLevel.html#L14) states $0 < \operatorname{conductorLevel}(W)$ for every $W$, and an instance derived from it registers `NeZero W.conductorLevel`, so that the conductor level may be used wherever a nonzero modulus or level is required (for instance as the modulus of a cyclotomic or congruence-subgroup level). [`WeierstrassCurve.squarefree_conductorLevel`](../def/WeierstrassCurve_ConductorLevel.html#L19) states that $\operatorname{conductorLevel}(W)$ is squarefree. [`WeierstrassCurve.prime_dvd_conductorLevel_iff`](../def/WeierstrassCurve_ConductorLevel.html#L22) states that for $W$ with $\Delta(W) \neq 0$ and a prime natural number $q$, one has $q \mid \operatorname{conductorLevel}(W)$ if and only if $(q : \mathbb{Z}) \mid \Delta(W)$; the hypothesis $\Delta(W) \neq 0$ is needed precisely because of the degenerate case above. No minimality of the model, and no semistability, is assumed anywhere in this module: the number defined here agrees with the arithmetic conductor $N_E$ only under such additional hypotheses, and in general it is merely the squarefree integer whose prime support is that of the discriminant of the given model.
--
--   **Relation to Mathlib.** Built directly on Mathlib's `WeierstrassCurve` and `UniqueFactorizationMonoid.radical`; the notion of "conductor level" of an integral Weierstrass model is the project's own packaging, and is not Mathlib's conductor of an elliptic curve.
--
--   **Where it is used.** The conductor level supplies the squarefree level at which modularity statements for Frey-type curves are instantiated: it is the modulus fed to the project's exact-conductor-level modularity predicate, and hence to the modularity lifting ($R = \mathbb{T}$) statements used in the Frey–Serre–Ribet–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ConductorLevel.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

open UniqueFactorizationMonoid

def conductorLevel (W : WeierstrassCurve ℤ) : ℕ :=
  radical W.Δ.natAbs

theorem conductorLevel_pos (W : WeierstrassCurve ℤ) : 0 < W.conductorLevel :=
  Nat.radical_pos _

instance (W : WeierstrassCurve ℤ) : NeZero W.conductorLevel := ⟨W.conductorLevel_pos.ne'⟩

theorem squarefree_conductorLevel (W : WeierstrassCurve ℤ) : Squarefree W.conductorLevel :=
  squarefree_radical

theorem prime_dvd_conductorLevel_iff (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {q : ℕ}
    (hq : q.Prime) : q ∣ W.conductorLevel ↔ (q : ℤ) ∣ W.Δ := by
  rw [conductorLevel, dvd_radical_iff_of_irreducible hq.prime.irreducible
    (Int.natAbs_ne_zero.mpr hΔ)]
  exact Int.natCast_dvd.symm

end WeierstrassCurve

end


