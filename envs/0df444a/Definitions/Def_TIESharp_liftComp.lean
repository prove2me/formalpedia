-- Prove2me | Definitions.Def_TIESharp_liftComp
-- name    : TIESharp_liftComp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:02.201742+00:00
-- url     : https://prove2.me/theorems/f3a4bb89-1129-472e-9a3a-9ecfa71efe01
-- title:
--   Components lifted from subprofiles
-- statement:
--   Given, at every job count $m'$, assignment weights $Y^{m'}_A(\cdot)$ and potentials $V^{m'}_i(\cdot)$, a **component** at job count $m$ is a choice of a job subset $J\subseteq[m]$ of size $m'$ (its columns taken in increasing order) and a coordinate, either an assignment weight $Y^{m'}_A$ or a potential $V^{m'}_i$. Its **lift** is the function of the full profile $t$ obtained by evaluating that coordinate at the subprofile $t_J$, ignoring the other columns:
--   $$t\mapsto Y^{m'}_A(t_J)\quad\text{or}\quad t\mapsto V^{m'}_i(t_J).$$
--   Lemma 4.3 says that weak-star limits commute with lifting and that finite linear identities among such lifted components survive the limit.
--
--   **Formalization Note.** $J$ is an order embedding `Fin m' ↪o Fin m`; the coordinate is `(Fin m' → Fin n) ⊕ Fin n`. Marginals are finite sums of assignment coordinates.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.3, p.16; §4.2.2, p.17

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- A **component lifted from a subprofile** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Lemma 4.3, p.16, and §4.2.2, p.17: "For a job subset J, lift a
lower-dimensional function f(t_J) by ignoring the other columns"). Given, for every job count `m'`,
assignment probabilities `Y m' b A` and potentials `V m' b i`, a component is a triple
`c = (m', e, κ)`: an order embedding `e : Fin m' ↪o Fin m` (the job subset `J`, columns in
increasing order) and a coordinate `κ`, either an assignment `A : Fin m' → Fin n` or a machine `i`.
Its lift evaluates that coordinate at the subprofile `t_J = (t_{i, e(l)})`.

**Formalization Note.** Marginal probabilities are finite sums of assignment coordinates, so they
are finite linear combinations of components. -/
def liftComp {n m : ℕ}
    (Y : (m' : ℕ) → (Fin n → Fin m' → ℝ) → (Fin m' → Fin n) → ℝ)
    (V : (m' : ℕ) → (Fin n → Fin m' → ℝ) → Fin n → ℝ)
    (c : Σ m' : ℕ, (Fin m' ↪o Fin m) × ((Fin m' → Fin n) ⊕ Fin n))
    (t : Fin n → Fin m → ℝ) : ℝ :=
  Sum.elim (fun A => Y c.1 (fun i l => t i (c.2.1 l)) A)
    (fun i => V c.1 (fun i' l => t i' (c.2.1 l)) i) c.2.2

end TIESharp


