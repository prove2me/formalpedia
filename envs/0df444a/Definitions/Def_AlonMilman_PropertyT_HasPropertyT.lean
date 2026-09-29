-- Prove2me | Definitions.Def_AlonMilman_PropertyT_HasPropertyT
-- name    : AlonMilman_PropertyT_HasPropertyT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:32:08.974917+00:00
-- url     : https://prove2.me/theorems/2c0a49b1-2595-4d9e-ac09-8424c4a279d4
-- title:
--   Definition 4.6 — property (T) for a discrete group, in Alon–Milman's absolute-value form
-- statement:
--   Let $H$ be a discrete group. $H$ has **property (T)** if there exist $\varepsilon > 0$ and a finite set $K \subseteq H$ such that for every complex Hilbert space $V$, every essentially nontrivial unitary representation $\pi$ of $H$ in $V$, and every unit vector $y \in V$, there is $h \in K$ with
--
--   $$\big|\big(\pi(h)y, y\big)\big| < 1 - \varepsilon .$$
--
--   Here $(\cdot,\cdot)$ is the inner product of $V$. This is Kazhdan's property as Alon and Milman state it (Definition 4.6, following Kazhdan and Zimmer); it is the hypothesis on $H$ in Lemma 4.7, Lemma 4.8 and Theorem 4.9.
--
--   **Formalization Note** Definition 4.6 is stated for locally compact groups with a compact $K$; every group of this mission is discrete, where compact means finite, so $K$ is a finite set and no topology is involved. The Hilbert spaces range over Lean's universe `Type`. The definition keeps the paper's absolute value of the inner product; this differs from the common textbook form $\|\pi(h)y - y\| \ge \varepsilon$. In particular a group with a nontrivial one-dimensional unitary character $\chi$ does not satisfy it, since then $|(\chi(h)y, y)| = 1$ for every unit $y$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 84, Definition 4.6

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_EssentiallyNontrivial

namespace AlonMilman.PropertyT

/-- Definition 4.6 (Alon–Milman 1985, p. 84), for a discrete group `H` (compact subsets are
finite): `H` has property (T) if there exist `ε > 0` and a finite `K ⊆ H` such that for every
essentially nontrivial unitary representation `π` of `H` in a complex Hilbert space `V` and
every unit vector `y ∈ V` there is an `h ∈ K` with `|(π(h) y, y)| < 1 − ε`.  The Hilbert spaces
range over `Type` (universe 0).  The absolute value of the inner product is the paper's; it is
not the textbook form `‖π(h) y − y‖ ≥ ε`. -/
def HasPropertyT (H : Type) [Group H] : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ K : Finset H,
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (π : H →* unitary (V →L[ℂ] V)), EssentiallyNontrivial π →
      ∀ y : V, ‖y‖ = 1 → ∃ h ∈ K, ‖inner ℂ ((π h : V →L[ℂ] V) y) y‖ < 1 - ε

end AlonMilman.PropertyT


