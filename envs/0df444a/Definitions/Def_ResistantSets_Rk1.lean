-- Prove2me | Definitions.Def_ResistantSets_Rk1
-- name    : ResistantSets_Rk1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:43.129056+00:00
-- url     : https://prove2.me/theorems/3c814462-d63c-4f06-b889-c0f2560bffa0
-- title:
--   The sets $R_{k,1}=\{\mathbf 0^{k+1},\mathbf 1^{k+1}\}\ast\{0\}$
-- statement:
--   For $k\ge1$,
--   $$
--   R_{k,1}=\{\mathbf 0^{k+1},\mathbf 1^{k+1}\}\ast\{0\}\subseteq\{0,1\}^{k+2},
--   $$
--   where $\mathbf 0^{k+1},\mathbf 1^{k+1}$ are the all-zeros and all-ones vectors of length $k+1$ and $\{0\}\subseteq\{0,1\}^1$. Thus $R_{k,1}$ consists of $(\mathbf 0^{k+1},0)$, $(\mathbf 1^{k+1},0)$ and every $(x,1)$ with $x\notin\{\mathbf 0^{k+1},\mathbf 1^{k+1}\}$. For example $R_{1,1}=\{000,110,101,011\}$.
--
--   These sets form the infinite family of the classification theorem.
--
--   **Formalization Note** The definition is total in $k$; every statement assumes $k\ge1$.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.6, §1.2 (R_{k,1}), with p.5 (0ᵏ, 1ᵏ) and p.3 (R_{1,1})

import Mathlib
import Definitions.Def_ResistantSets_reflProd

namespace ResistantSets

/-- **The sets `R_{k,1}`** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.2, p.6): `R_{k,1} := {0^{k+1}, 1^{k+1}} ∗ {0}` (`k ≥ 1`),
where `0^{k+1}, 1^{k+1}` are the all-zeros and all-ones vectors of length `k + 1` (p.5) and
`{0} ⊆ {0,1}¹`. So `R_{k,1} ⊆ {0,1}^{k+2}` consists of `(0^{k+1}, 0)`, `(1^{k+1}, 0)` and every
`(x, 1)` with `x ∉ {0^{k+1}, 1^{k+1}}`; for example `R_{1,1} = {000, 110, 101, 011}` (p.3).

**Formalization Note** The definition is total in `k`; the paper uses `k ≥ 1`, and every
statement says so. -/
def Rk1 (k : ℕ) : Finset (Fin (k + 2) → Bool) :=
  reflProd (n₁ := k + 1) (n₂ := 1) ({fun _ => false, fun _ => true} : Finset (Fin (k + 1) → Bool))
    ({fun _ => false} : Finset (Fin 1 → Bool))

end ResistantSets


