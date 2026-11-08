-- Prove2me | Definitions.Def_AffDisp4n_State_Valid
-- name    : AffDisp4n_State_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T08:01:51.425282+00:00
-- url     : https://prove2.me/theorems/11d144ad-4661-4df3-9553-5fac9313d1db
-- title:
--   A state valid for the original circuit $C_0$
-- statement:
--   A state is **valid for the original circuit $C_0$** if it satisfies every invariant that gate elimination maintains:
--
--   1. $\Phi$ is injective, that is, $u \mapsto L u$ is injective;
--   2. $P$ consists of disjoint pairs of distinct parameters;
--   3. **fairness**: the auxiliary matrix $A$ is invertible;
--   4. every equation has at most three nonconstant terms, i.e. every row of $(A \mid N)$ has at most three nonzero entries;
--   5. $C(u) = C_0(\Phi(u))$ for all $u \in Z(P)$.
--
--   The initial state ($\Phi = \mathrm{id}$, $P = \emptyset$, no equations, acyclic part $C_0$) is valid, and each step of gate elimination preserves validity.
--
--   **Formalization Note** The paper reasons about "the current state" of its algorithm. Its proofs use only these invariants, never the history, so the milestones quantify over all valid states.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.2, p.13; §2.3 (i), p.13; §2.4, p.16; §2.6, pp.18–19

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_PairsDisjoint
import Definitions.Def_AffDisp4n_Z
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_Phi
import Definitions.Def_AffDisp4n_State_eval

namespace AffDisp4n

/-- A state is **valid for the original circuit `C₀`** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.2–§2.4 and §2.6, pp.13–19): it meets
every invariant that gate elimination maintains.
1. `Φ` is injective (§2.2, p.13), i.e. `u ↦ L u` is injective.
2. `P` consists of disjoint pairs of distinct parameters (§2.2, p.13).
3. Fairness: the auxiliary matrix `A` is invertible (§2.3 (i), p.13).
4. Every equation has at most three nonconstant terms: each row of `(A | N)` has at most three nonzero
   entries (§2.3 (i), p.13).
5. `C(u) = C₀(Φ(u))` for every `u ∈ Z(P)` (§2.4, p.16).

**Formalization Note** The paper's statements concern "the current state" of the algorithm. Its proofs
use only these invariants, never the history, so the milestones quantify over every valid state. -/
structure State.Valid {n : ℕ} (σ : State n) (C₀ : Circuit n) : Prop where
  /-- `Φ` is injective -/
  inj : Function.Injective σ.L.mulVec
  /-- `P` consists of disjoint pairs -/
  pairs : PairsDisjoint σ.P
  /-- fairness: `A` is invertible -/
  fair : IsUnit σ.A.det
  /-- at most three nonconstant terms per equation -/
  three : ∀ i : Fin σ.r, Nat.card {k : Fin σ.r // σ.A i k ≠ 0} + Nat.card {y : Fin σ.m // σ.N i y ≠ 0} ≤ 3
  /-- the invariant `C(u) = C₀(Φ(u))` on `Z(P)` -/
  correct : ∀ u ∈ Z σ.P, σ.eval u = C₀.eval (σ.Phi u)

end AffDisp4n


