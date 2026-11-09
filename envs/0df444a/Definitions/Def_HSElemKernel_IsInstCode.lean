-- Prove2me | Definitions.Def_HSElemKernel_IsInstCode
-- name    : HSElemKernel_IsInstCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:39.584665+00:00
-- url     : https://prove2.me/theorems/3b5da22c-df15-4ff8-8656-45468e2463fa
-- title:
--   Codes of a Hitting Set instance
-- statement:
--   A list $c$ of natural numbers is a **code** of the instance $(U, \mathcal S, k)$, $U = \{0, \dots, n-1\}$, $m = |\mathcal S|$, if
--   $$c = [\,n,\ m,\ k\,] \mathbin{+\!\!+} \mathrm{block}(A_1) \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \mathrm{block}(A_m),$$
--   where $A_1, \dots, A_m$ lists every set of $\mathcal S$ exactly once, in any order, and $\mathrm{block}(A)$ is $|A|$ followed by the elements of $A$, each once, in any order.
--
--   This is the input format of every kernel and encoding in the mission. A statement quantified over every code holds for every presentation of the instance.
--
--   **Formalization Note** The paper fixes no input format. The strict inverse is `decodeInst`.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3, p.6, and Section 3.1, p.6

import Mathlib
import Definitions.Def_HSElemKernel_HSInstance

namespace HSElemKernel

/-- `c` is a code of the instance `I = (Fin n, S, k)` (Sheng–Xiao, arXiv:2609.06512, held
version sha256 aca9c70e…, Section 3, p.6, and Section 3.1, p.6, where the kernel's input is the
instance itself): the list of natural numbers
`[n, m, k] ++ block(A₁) ++ ⋯ ++ block(A_m)`, where `A₁, …, A_m` lists every set of `S` exactly
once, in any order (`m = |S|`), and `block(A) = |A| :: (the elements of A, each once, in any
order)`.

**Formalization Note** The paper fixes no input format. Every listing order of the sets and of
the elements of each set is a code, so a statement quantified over every code holds for every
presentation of the instance. The strict inverse is `decodeInst`. -/
def IsInstCode (I : HSInstance) (c : List ℕ) : Prop :=
  ∃ L : List (List (Fin I.n)),
    (∀ l ∈ L, l.Nodup) ∧ (L.map List.toFinset).Nodup ∧ (L.map List.toFinset).toFinset = I.S ∧
      c = [I.n, L.length, I.k] ++ L.flatMap (fun l => l.length :: l.map Fin.val)

end HSElemKernel


