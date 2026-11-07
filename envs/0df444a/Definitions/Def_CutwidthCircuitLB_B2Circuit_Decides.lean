-- Prove2me | Definitions.Def_CutwidthCircuitLB_B2Circuit_Decides
-- name    : CutwidthCircuitLB_B2Circuit_Decides
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:36.792609+00:00
-- url     : https://prove2.me/theorems/81ea27db-40d1-484e-aeb3-276af028162d
-- title:
--   A $B_2$-circuit decides $L$ on inputs of length $n$
-- statement:
--   A $B_2$-circuit $C$ on $n$ inputs **decides the language** $L \subseteq \{0,1\}^\star$ **on inputs of length $n$** if, for every $x \in \{0,1\}^n$,
--   $$
--   C(x) = 1 \iff x \in L .
--   $$
--
--   **Formalization Note** The string $x$ of length $n$ is the list of the values $x_1, \dots, x_n$; the language is a single set of binary strings of all lengths.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 1, p.1

import Mathlib
import Definitions.Def_CutwidthCircuitLB_B2Circuit
import Definitions.Def_CutwidthCircuitLB_B2Circuit_eval

namespace CutwidthCircuitLB

/-- A B₂-circuit `C` on `n` inputs **decides the language `L` on inputs of length `n`**
(McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §1, p.1): for every `x ∈ {0,1}ⁿ`, `C(x) = 1` iff the string `x` belongs to `L`.

**Formalization Note** A string of length `n` is `List.ofFn x` for `x : Fin n → Bool`; the
language is one set of binary strings of all lengths. -/
def B2Circuit.Decides {n : ℕ} (C : B2Circuit n) (L : Language Bool) : Prop :=
  ∀ x : Fin n → Bool, C.eval x = true ↔ List.ofFn x ∈ L

end CutwidthCircuitLB


