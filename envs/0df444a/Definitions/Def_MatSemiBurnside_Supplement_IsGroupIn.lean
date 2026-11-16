-- Prove2me | Definitions.Def_MatSemiBurnside_Supplement_IsGroupIn
-- name    : MatSemiBurnside_Supplement_IsGroupIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:44:52.229711+00:00
-- url     : https://prove2.me/theorems/96a51773-9bc2-4a6e-a462-1d41eb385ad8
-- title:
--   A group $G\le T$ inside a semigroup $T$
-- statement:
--   Let $T$ be a subset of a semigroup (for instance $T=\overline{\langle X\rangle}\subseteq\mathrm{Mat}_d(\overline{\mathbb Q})$). A **group** $G\le T$ is a subset $G\subseteq T$ that is a group under the ambient multiplication:
--
--   1. $G$ is closed under multiplication;
--   2. there is $e\in G$ with $eg=ge=g$ for all $g\in G$;
--   3. every $g\in G$ has $h\in G$ with $gh=hg=e$.
--
--   For matrices the identity $e$ is an idempotent, for example the projection onto $\operatorname{im}(a)$ along $\ker(a)$; it need not be the identity matrix. These are the groups whose class counts are bounded in Theorem 3.
--
--   **Formalization Note** $G$ need not consist of invertible matrices, need not be Zariski closed and need not be finitely generated; it is nonempty since it contains $e$.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 3, p.4; §3.3, pp.13–14

import Mathlib
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

/-- **A group G ≤ T inside a semigroup T.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 3, p.4 (restated pp.13, 39): "every group
G ≤ ⟨X⟩‾"; p.13: "every matrix group is a rank-stable subsemigroup"; p.14: the identity of such a group can be
the projection I_im(a) onto im(a) along ker(a).

`IsGroupIn T G` says that G is a subset of T which is a group under the multiplication of the ambient monoid:
G is closed under multiplication, contains an element e with e·g = g·e = g for every g ∈ G, and every g ∈ G has
h ∈ G with g·h = h·g = e. (Associativity is inherited.)

**Formalization Note.** The identity e of G is G's own (for matrices, an idempotent such as a projection), not
necessarily the identity of the ambient monoid; G need not consist of units, need not be closed in any topology
and need not be finitely generated. G is nonempty (it contains e). -/
def IsGroupIn {M : Type} [Mul M] (T G : Set M) : Prop :=
  G ⊆ T ∧ (∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) ∧
    ∃ e ∈ G, (∀ g ∈ G, e * g = g ∧ g * e = g) ∧ ∀ g ∈ G, ∃ h ∈ G, g * h = e ∧ h * g = e

end MatSemiBurnside.Supplement


