-- Prove2me | Definitions.Def_Holant3Dich_Ann
-- name    : Holant3Dich_Ann
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:43:35.289257+00:00
-- url     : https://prove2.me/theorems/52ff8be6-7729-4ccd-8641-11d07e845e80
-- title:
--   The annihilator $\mathrm{Ann}(F)$ of a domain-3 signature
-- statement:
--   For a symmetric signature $F$ on the domain $\{\mathsf B,\mathsf G,\mathsf R\}$,
--   $$\mathrm{Ann}(F)=\{u\in\mathbb C^3:\langle F,u\rangle=0\}\qquad\text{(Definition 2.9, p.19)},$$
--   the set of unary signatures whose connection to an input of $F$ gives the zero signature. $F$ **has a nonzero annihilator** ($\mathrm{Ann}(F)\neq 0$) if this set contains a nonzero vector.
--
--   By Proposition 2.11 the annihilator of a nondegenerate symmetric signature is at most one-dimensional. A nonzero annihilator separates the types $\mathfrak A_2,\mathfrak B_2,\mathfrak C^1_2,\mathfrak C^0$ from the other five (Proposition 2.12) and is the hypothesis of the algorithm of Theorem 4.4.
--
--   **Formalization Note** $\langle F,u\rangle$ connects $u$ to the last input of $F$; for symmetric $F$ the choice of input does not matter (p.14).
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Definition 2.9 p.19

import Mathlib
import Definitions.Def_Holant3Dich_Sig

set_option autoImplicit false

namespace Holant3Dich

/-- The **annihilator** `Ann(F) = {u ∈ ℂ³ : ⟨F, u⟩ = 0}` of a domain-3 signature. Cai–Ihm, *Group
Action and Spin Representation Lead to a Holant\* Complexity Dichotomy on Domain Size 3*, STOC 2027
submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Definition 2.9, p.19:
"Let F be a symmetric signature on domain 3. We define Ann(F) = {u ∈ C^3 : ⟨F, u⟩ = 0}."

**Formalization Note.** `⟨F, u⟩` connects `u` to the last input (`contractT`); for the symmetric
signatures this is applied to, the choice of input does not matter (p.14). -/
def Ann (F : Sig 3) : Set (Fin 3 → ℂ) := {u | contractT F.2 u = 0}

/-- `Ann(F) ≠ 0`: `F` has a nonzero annihilator. Cai–Ihm, Prop. 2.12, p.20 and Theorem 4.9,
Item 5, p.48 ("Ann(F) ≠ 0"). -/
def HasAnn (F : Sig 3) : Prop := ∃ u ∈ Ann F, u ≠ 0

end Holant3Dich


