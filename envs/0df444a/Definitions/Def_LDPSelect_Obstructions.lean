-- Prove2me | Definitions.Def_LDPSelect_Obstructions
-- name    : LDPSelect_Obstructions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:59.69828+00:00
-- url     : https://prove2.me/theorems/08b59f2d-4879-4d20-9b47-c18c311f4ccc
-- title:
--   The nine four-element obstructions $O_1,\dots,O_9$ and the families $B_m$
-- statement:
--   The nine four-element families of §5 are given by their minimally infeasible sets (writing $123$ for $\{1,2,3\}$):
--
--   | family | minimally infeasible sets |
--   |---|---|
--   | $O_1$ (paw) | $23, 14, 24, 34$ |
--   | $O_2$ ($=B_3$) | $123, 14, 24, 34$ |
--   | $O_3$ ($P_4$) | $13, 24, 34$ |
--   | $O_4$ | $123, 24, 34$ |
--   | $O_5$ ($T$) | $123, 124, 34$ |
--   | $O_6$ | $124, 34$ |
--   | $O_7$ ($U_{2,4}$) | $123, 124, 134, 234$ |
--   | $O_8$ | $124, 134, 234$ |
--   | $O_9$ | $134, 234$ |
--
--   For $m\ge1$, on the ground set $[m]\cup\{x\}$ with $x\notin[m]$,
--
--   $$B_m=\{S : S\subsetneq[m]\}\cup\{\{x\}\}.$$
--
--   Its minimally infeasible sets are $[m]$ and the pairs $\{x,y\}$, $y\in[m]$. Theorem 1 says that $O_1,\dots,O_9$ and $B_m$, $m\ge4$, are exactly the minor-minimal families outside $\mathcal G$.
--
--   **Formalization Note** `O i` for `i : Fin 9` is the paper's $O_{i+1}$, on `Fin 4` with the paper's element $e$ as value $e-1$ (so $23$ is `{1, 2}`). `B m` lives on `Fin (m+1)` with $x$ = `Fin.last m`.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 1, p.2 (pdf p.3); §5, p.9 (pdf p.10)

import Mathlib
import Definitions.Def_LDPSelect_Family

namespace LDPSelect

/-!
# The listed excluded minors `O1, …, O9` and `B_m`

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 1, p.2 (`B_m`); §5, p.9 (`O1–O9`).

**Formalization Note.** `O i` for `i : Fin 9` is the paper's `O_{i+1}`, and the paper's element `e` is
`Fin 4` value `e − 1`: the paper's `23` is `{1, 2}`. On `Fin (m + 1)`, the paper's `x` is `Fin.last m`,
and `[m]` is the set of all other elements.
-/

/-- The nine four-element families of §5, p.9, by their minimally infeasible sets:
`O1: 23, 14, 24, 34`; `O2: 123, 14, 24, 34`; `O3: 13, 24, 34`; `O4: 123, 24, 34`; `O5: 123, 124, 34`;
`O6: 124, 34`; `O7: 123, 124, 134, 234`; `O8: 124, 134, 234`; `O9: 134, 234`. -/
def O : Fin 9 → Family 4
  | 0 => fromMIS [{1, 2}, {0, 3}, {1, 3}, {2, 3}]
  | 1 => fromMIS [{0, 1, 2}, {0, 3}, {1, 3}, {2, 3}]
  | 2 => fromMIS [{0, 2}, {1, 3}, {2, 3}]
  | 3 => fromMIS [{0, 1, 2}, {1, 3}, {2, 3}]
  | 4 => fromMIS [{0, 1, 2}, {0, 1, 3}, {2, 3}]
  | 5 => fromMIS [{0, 1, 3}, {2, 3}]
  | 6 => fromMIS [{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}]
  | 7 => fromMIS [{0, 1, 3}, {0, 2, 3}, {1, 2, 3}]
  | 8 => fromMIS [{0, 2, 3}, {1, 2, 3}]

/-- `B_m = {S : S ⊊ [m]} ∪ {{x}}` on `[m] ∪ {x}` (Theorem 1, p.2). -/
def B (m : ℕ) : Family (m + 1) :=
  {S | (Fin.last m ∉ S ∧ S ≠ Finset.univ.erase (Fin.last m)) ∨ S = {Fin.last m}}

end LDPSelect


