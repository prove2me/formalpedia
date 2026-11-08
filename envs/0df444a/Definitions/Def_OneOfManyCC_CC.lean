-- Prove2me | Definitions.Def_OneOfManyCC_CC
-- name    : OneOfManyCC_CC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:53.423687+00:00
-- url     : https://prove2.me/theorems/ab2b10a0-f3f1-4e56-91e7-d5299217a6e8
-- title:
--   Communication complexity $\mathrm{CC}(R)$ of a relation
-- statement:
--   For a relation $R\subseteq A\times B\times O$, the **deterministic communication complexity** $\mathrm{CC}(R)$ is the minimum depth of a protocol that solves $R$ on all of $A\times B$:
--
--   $$\mathrm{CC}(R)=\min\{\operatorname{depth}(P) : P\text{ solves }R\}.$$
--
--   It is the quantity compared on both sides of the paper's main theorem.
--
--   **Formalization Note** The minimum is `sInf` on natural numbers, which is $0$ on the empty set. For finite $A$, $O$ nonempty and total $R$ the set is nonempty, so the minimum is attained: Alice sends $x$ and Bob then announces a valid output.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.1, p.7

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol

namespace OneOfManyCC

/-- **Deterministic communication complexity** `CC(R)`.
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.1, p.7:
"We write CC(R) for the minimum depth of a protocol that solves R."

**Formalization Note.** `sInf` on `ℕ` is the minimum of a nonempty set and is `0` on the empty set.
The set is nonempty for finite `A`, `B` and total `R` (the only case the paper uses, and the only
case in this mission's statements), so `CC R` is an attained minimum there; the verification file
proves this. -/
noncomputable def CC {A B O : Type} (R : A → B → O → Prop) : ℕ :=
  sInf {d | ∃ P : Protocol A B O, P.SolvesOn R Set.univ Set.univ ∧ P.depth = d}

end OneOfManyCC


