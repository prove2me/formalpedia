-- Prove2me | Definitions.Def_GeoSemialgCSP_HasCousinsHoms
-- name    : GeoSemialgCSP_HasCousinsHoms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:40.019607+00:00
-- url     : https://prove2.me/theorems/f0807437-0e5e-421f-a7ee-6b204f797f20
-- title:
--   Property (2): cousins homomorphisms for all trees
-- statement:
--   The pair $(X,P)$ has **property (2)** if for every height $h$ the complete ordered $k$-ary tree of height $h$ has a cousins homomorphism into $(X,P)$.
--
--   This is the hypothesis of the general hardness theorem (Theorem 6.1); Lemma 3.1 establishes it for geometric semialgebraic predicates.
--
--   **Formalization Note** The paper asks for a homomorphism of every finite ordered $k$-ary tree. Requiring it only for complete trees is implied by that (every finite ordered $k$-ary tree embeds in a complete one, preserving cousins tuples), and complete trees are the only ones the proof uses.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Assumptions, p.7 (PDF p.8); Eq. (2), p.9 (PDF p.10)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_CousinsHom

namespace GeoSemialgCSP

/-- **Property (2).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Assumptions, printed p.7 (PDF p.8), and Eq. (2),
printed p.9 (PDF p.10): for every finite ordered `k`-ary tree there is a cousins homomorphism from
its leaves to `X`.

**Formalization Note.** Required for the complete trees `T_{k^h}` of every height `h`, which are
the only trees the paper's proof uses (Lemma 4.3 item 4: the tree `T_M`, `M = k^H`). Every finite
ordered `k`-ary tree embeds in a complete one preserving cousins tuples, so this is implied by the
printed property. -/
def HasCousinsHoms {k d : ℕ} (X : Set (E d)) (S : Set (Fin k → E d)) : Prop :=
  ∀ h : ℕ, ∃ ψ : (Fin h → Fin k) → E d, CousinsHom X S h ψ

end GeoSemialgCSP


