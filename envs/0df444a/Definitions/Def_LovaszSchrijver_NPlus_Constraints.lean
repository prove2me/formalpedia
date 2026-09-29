-- Prove2me | Definitions.Def_LovaszSchrijver_NPlus_Constraints
-- name    : LovaszSchrijver_NPlus_Constraints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:58:45.277988+00:00
-- url     : https://prove2.me/theorems/e0a1fdbe-6be5-4fe5-94b6-172a24a62f49
-- title:
--   Odd holes, odd antiholes, odd wheels and the wheel constraint (Section 2.a)
-- statement:
--   Let $G = (V,E)$ be a finite graph. The paper introduces four classes of inequalities valid for $\mathrm{STAB}(G)$ (pp. 175–176):
--
--   1. "The *clique constraints* strengthen the class (2): for each clique $B$, we have (3) $\sum_{i\in B} x_i \le 1$."
--   2. "The *odd hole constraints* express the nonbipartiteness of the graph: if $C$ induces a chordless odd cycle in $G$, then (4) $\sum_{i\in C} x_i \le \tfrac12(|C|-1)$."
--   3. "The *odd antihole constraints* are defined by sets $D$ that induce a chordless odd cycle in the complement of $G$: (5) $\sum_{i\in D} x_i \le 2$."
--   4. "let $U$ induce an odd wheel in $G$, with center $u_0 \in U$. Then the constraint
--   $$\sum_{i\in U\setminus\{u_0\}} x_i + \frac{|U|-2}{2}\, x_{u_0} \le \frac{|U|-2}{2}$$
--   is called a *wheel constraint*."
--
--   This file defines the combinatorial notions:
--
--   - **Odd hole.** $C \subseteq V$ induces a chordless odd cycle: for some odd $m \ge 3$ the nodes of $C$ can be numbered $c_0, \dots, c_{m-1}$ so that $c_s c_t \in E$ exactly when $t \equiv s \pm 1 \pmod m$. Triangles ($m = 3$) are included.
--   - **Odd antihole.** $D$ induces a chordless odd cycle in the complement $\bar G$, and $|D| \ge 5$.
--   - **Odd wheel.** $U$ induces an odd wheel with center $u_0 \in U$: $U \setminus \{u_0\}$ is an odd hole of $G$ and $u_0$ is adjacent to every node of $U \setminus \{u_0\}$. The page gives no further definition; this is the standard meaning. For a triangle rim ($U$ a $K_4$) the wheel constraint is the clique constraint of $U$.
--   - **Wheel coefficient vector** $w^{U,u_0}$: $1$ on $U \setminus \{u_0\}$, $(|U|-2)/2$ at $u_0$, $0$ outside $U$.
--
--   The clique, odd hole and odd antihole constraints use the incidence vector $\chi^B$, $\chi^C$, $\chi^D$ as coefficient vector.
--
--   **Formalization Note** A 3-node "antihole" is a stable set of $G$, for which (5) fails at its own incidence vector (sum $3 > 2$); so $|D| \ge 5$ is part of the notion. The odd hole constraint is stated for chordless cycles only, the literal reading of (4); the page notes the inequality also holds, and is implied, when $C$ has chords. The coefficient $(|U|-2)/2$ is computed in $\mathbb R$ after casting $|U|$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), pp. 175–176, Section 2.a, (3), (4), (5) and the wheel constraint

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet

namespace LovaszSchrijver.NPlus

/-- `C` induces a chordless odd cycle (an odd hole, triangles included) in `G`: for some odd
`m ≥ 3` the nodes of `C` can be numbered `0, …, m-1` so that two of them are adjacent in `G`
exactly when their numbers are consecutive modulo `m` (pp. 175–176). -/
def IsOddHole {V : Type} (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ ∃ f : Fin m ≃ C, ∀ s t : Fin m,
    G.Adj (f s : V) (f t : V) ↔ (t.val = (s.val + 1) % m ∨ s.val = (t.val + 1) % m)

/-- `D` induces a chordless odd cycle in the complement of `G` with at least `5` nodes
(an odd antihole, p. 176). -/
def IsOddAntihole {V : Type} (G : SimpleGraph V) (D : Finset V) : Prop :=
  5 ≤ D.card ∧ IsOddHole Gᶜ D

/-- `U` induces an odd wheel in `G` with center `u₀ ∈ U` (p. 176): `U \ {u₀}` is an odd hole
and `u₀` is adjacent to every node of it. -/
def IsOddWheel {V : Type} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) (u₀ : V) : Prop :=
  u₀ ∈ U ∧ IsOddHole G (U.erase u₀) ∧ ∀ w ∈ U.erase u₀, G.Adj u₀ w

/-- Coefficient vector of the wheel constraint (p. 176):
`Σ_{i ∈ U \ {u₀}} xᵢ + ((|U| - 2)/2) x_{u₀} ≤ (|U| - 2)/2`. -/
noncomputable def wheelCoeff {V : Type} [DecidableEq V] (U : Finset V) (u₀ : V) : V → ℝ :=
  fun i => if i = u₀ then ((U.card : ℝ) - 2) / 2 else if i ∈ U then 1 else 0

end LovaszSchrijver.NPlus


