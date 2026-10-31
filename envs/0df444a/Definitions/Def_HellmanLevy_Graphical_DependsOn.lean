-- Prove2me | Definitions.Def_HellmanLevy_Graphical_DependsOn
-- name    : HellmanLevy_Graphical_DependsOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:37.277582+00:00
-- url     : https://prove2.me/theorems/9793f8e5-faa0-4826-9a06-57f1711602c1
-- title:
--   Payoffs depending only on a relation $D$
-- statement:
--   A payoff $u:X\times A^X\to\mathbb R$ **depends only on** a relation $D$ on $X$ if for every vertex $g$ and pure profiles $a,a'$ with $a(g)=a'(g)$ and $a(h)=a'(h)$ for every $h$ with $g\,D\,h$, one has $u(g,a)=u(g,a')$.
--
--   With $D=G$ this is the locality condition of a graphical game; Lemma 4.8 produces payoffs depending on a relation with finite sections.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §3.2, p.14; proof of Lemma 4.8, p.24

import Mathlib

namespace HellmanLevy.Graphical

/-- The payoff `u : X → (X → A) → ℝ` **depends only on `D`**: the payoff `u g a` of each vertex
`g` under the pure profile `a` depends only on `g`'s own action and on the actions of the
vertices `h` with `D g h`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §3.2, p.14 ("(Formally, if g ∈ Ω and a, a′ : Ω → A are two action profiles such that
a(g) = a′(g), and a(h) = a′(h) for each h ∈ N(g), then u(g, a) = u(g, a′).)"), with `D = G`;
proof of Lemma 4.8, p.24 ("each player's payoff in u′ depends only on his or her own action and
those of his or her neighbours in G′"). -/
def DependsOn {X A : Type*} (u : X → (X → A) → ℝ) (D : X → X → Prop) : Prop :=
  ∀ g (a a' : X → A), a g = a' g → (∀ h, D g h → a h = a' h) → u g a = u g a'

end HellmanLevy.Graphical


