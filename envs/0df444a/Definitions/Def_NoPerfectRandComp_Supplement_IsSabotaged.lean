-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_IsSabotaged
-- name    : NoPerfectRandComp_Supplement_IsSabotaged
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:12:46.912231+00:00
-- url     : https://prove2.me/theorems/f1b6b825-1b52-4b7d-9215-363fb2f09456
-- title:
--   Sabotaged input $z\in\{0,1,*\}^n\cup\{0,1,\dagger\}^n$
-- statement:
--   Let $h$ be a possibly partial Boolean function on $n$ bits. A **sabotaged input** for $h$ is a string
--   $$
--   z\in\{0,1,*\}^n\cup\{0,1,\dagger\}^n
--   $$
--   (wildcards of one kind only) for which there exist $x, y\in\mathrm{Dom}(h)$ with $h(x)\ne h(y)$, both agreeing with every Boolean coordinate of $z$. The set of wildcard positions may be larger than the set where $x$ and $y$ differ.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.2, p.4

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_NoPerfectRandComp_Supplement_SabSym

namespace NoPerfectRandComp

namespace Supplement

/-- A sabotaged input for `h` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.2, p.4): a string
`z ∈ {0,1,∗}^n ∪ {0,1,†}^n` for which there exist `x, y ∈ Dom(h)` with `h(x) ≠ h(y)`, both
agreeing with every Boolean coordinate of `z`.

**Formalization Note** `z` uses wildcards of one kind only (no `†` anywhere, or no `∗` anywhere).
The wildcard set may be larger than the set where `x` and `y` differ. -/
def IsSabotaged {ι : Type} (h : PartialFn ι) (z : ι → SabSym) : Prop :=
  ((∀ i, z i ≠ SabSym.dagger) ∨ (∀ i, z i ≠ SabSym.star)) ∧
  ∃ x ∈ h.dom, ∃ y ∈ h.dom, h.val x ≠ h.val y ∧
    ∀ i b, z i = SabSym.bit b → x i = b ∧ y i = b

end Supplement

end NoPerfectRandComp


