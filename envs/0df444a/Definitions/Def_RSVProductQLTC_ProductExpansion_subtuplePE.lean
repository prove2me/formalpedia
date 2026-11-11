-- Prove2me | Definitions.Def_RSVProductQLTC_ProductExpansion_subtuplePE
-- name    : RSVProductQLTC_ProductExpansion_subtuplePE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:00.510037+00:00
-- url     : https://prove2.me/theorems/7508653e-0741-48a3-b3d0-9832ef8b0e9d
-- title:
--   Product expansion on every nonempty subtuple
-- statement:
--   Let $I$ be a finite index set, $A_i$ finite coordinate sets, $E$ a field, and $C_i\subseteq E^{A_i}$ linear codes. For a positive real $\rho$, this predicate requires
--   $$\text{for every nonempty }J\subseteq I,\quad (C_i)_{i\in J}\text{ is }\rho\text{-product-expanding}.$$
--   Each subtuple uses its own product grid $\prod_{i\in J}A_i$ and the axis-line decomposition of Definition 5.5. Singletons are included. This is the shared condition on primal and dual tuples in Lemmas 5.7 and 5.4.
--
--   **Formalization Note** A finite subset is represented by a `Finset` and its subtype. If $I$ itself is empty, the predicate has no nonempty subtuple and is vacuous; Lemma 5.7 uses $I=\{1,\ldots,r\}$ with $r\ge2$ and separately requires $\rho>0$. No empty subtuple is imposed.
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), Definition 5.5 and Lemma 5.7, printed p.20 (PDF p.21)

import Mathlib
import Definitions.Def_GoodQLTC_IsProductExpanding
set_option autoImplicit false
open Classical

namespace RSVProductQLTC.ProductExpansion

/-- Definition 5.5 applied on each nonempty subtuple's own product grid, including singletons. -/
def allSubtuplePE {E I : Type} [Field E] [Fintype I]
    {A : I → Type} [∀ i, Fintype (A i)] (ρ : ℝ)
    (C : ∀ i, Submodule E (A i → E)) : Prop :=
  ∀ J : Finset I, J.Nonempty →
    GoodQLTC.IsProductExpanding ρ (fun i : J => C i.val)

end RSVProductQLTC.ProductExpansion


