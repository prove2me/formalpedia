-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsMinimalSystem
-- name    : CombOpt_MatchingPolytope_IsMinimalSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:00.920456+00:00
-- url     : https://prove2.me/theorems/2a229327-57a2-4f3c-97a0-2a8c0e44dba1
-- title:
--   A minimal defining system $A'x=b',\ A''x\le b''$
-- statement:
--   A system of equations $A'x=b'$ and inequalities $A''x\le b''$ with solution set $P$ is **minimal** if
--
--   1. no inequality can be made into an equation without reducing the solution set: for each row $i$ of $A''$, $\{x\in P:\ (a''_i)^\top x=b''_i\}\ne P$;
--   2. no inequality can be omitted without enlarging the solution set;
--   3. no equation can be omitted without enlarging the solution set.
--
--   Theorem 6.17 characterizes minimal systems by linear independence and facets.
--
--   **Formalization Note** Making an inequality an equation can only shrink the solution set and omitting a row can only enlarge it, so "different from $P$" means "strictly smaller", resp. "strictly larger". The rows are indexed by $\{1,\dots,p\}$ and $\{1,\dots,q\}$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, p. 212 (PDF p. 220)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_systemSol

namespace CombOpt.MatchingPolytope

/-- **A minimal defining system.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, p. 212 (PDF p. 220): "A system of inequalities and equations is minimal if no
inequality can be made into an equation without reducing the size of the solution set and no
inequality or equation can be omitted without enlarging the solution set."

For the system `A′x = b′, A″x ≤ b″` with solution set `P`:
1. making inequality `i` an equation gives `{x ∈ P : (a″_i)^T x = b″_i}`, which must differ from `P`;
2. omitting inequality `i` must give a set different from `P`;
3. omitting equation `j` must give a set different from `P`.

**Formalization Note.** Making an inequality an equation can only shrink the solution set, and
omitting a row can only enlarge it, so "≠ P" is "strictly smaller" resp. "strictly larger".
Rows are indexed by `Fin p` and `Fin q`; omitting row `i` restricts the index to `{k // k ≠ i}`. -/
def IsMinimalSystem {ι : Type*} [Fintype ι] {p q : ℕ} (A' : Fin p → ι → ℝ) (b' : Fin p → ℝ)
    (A'' : Fin q → ι → ℝ) (b'' : Fin q → ℝ) : Prop :=
  (∀ i : Fin q, {x | x ∈ systemSol A' b' A'' b'' ∧ A'' i ⬝ᵥ x = b'' i} ≠ systemSol A' b' A'' b'') ∧
  (∀ i : Fin q, systemSol A' b' (fun k : {k : Fin q // k ≠ i} => A'' k)
      (fun k : {k : Fin q // k ≠ i} => b'' k) ≠ systemSol A' b' A'' b'') ∧
  (∀ j : Fin p, systemSol (fun k : {k : Fin p // k ≠ j} => A' k)
      (fun k : {k : Fin p // k ≠ j} => b' k) A'' b'' ≠ systemSol A' b' A'' b'')

end CombOpt.MatchingPolytope


