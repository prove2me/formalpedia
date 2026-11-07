-- Prove2me | Definitions.Def_SteinerAPX_tube
-- name    : SteinerAPX_tube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:06.199709+00:00
-- url     : https://prove2.me/theorems/911a4403-8d67-4aef-9fa7-2413b6fdc6be
-- title:
--   Middle segments and tubes of radius $\rho$
-- statement:
--   Let $[p,q]$ be a cable segment and $0<\rho\le1/100$. A **middle segment** of $[p,q]$ is a pair $(a,b)$ of sampled terminals of $[p,q]$ with
--   $$
--   10\rho\le\|a-p\|\le10\rho+\rho^2,\qquad 10\rho\le\|b-q\|\le10\rho+\rho^2 .
--   $$
--   The **tube** around $[a,b]$ is the closed cylinder of radius $\rho$ with flat caps,
--   $$
--   Z=\{x : \exists\, y\in[a,b],\ \langle x-y,\ b-a\rangle=0,\ \|x-y\|\le\rho\},
--   $$
--   i.e. the points whose orthogonal projection onto the line $ab$ lies in $[a,b]$ and whose distance to that line is at most $\rho$.
--
--   Tubes localize a tree on $P_\rho$ near each cable segment; the cable-recovery lemma charges added length to the length of the tree inside the tubes.
--
--   **Formalization Note** The middle segment is not unique; statements quantify over every choice. The first endpoint $p$ of the segment's pair is matched with $a$.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.2, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_SteinerAPX_samples

namespace SteinerAPX

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Middle segments and tubes.** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*,
STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.2, pp.14–15 (PDF pp.16–17): "For each cable
segment e, choose terminals ae and be at distances between 10ρ and 10ρ + ρ2 from its two
endpoints, respectively. We call (ae, be) the middle segment of e and its two remaining parts the
end pieces, each of length at most 10ρ + ρ2. … We surround each middle segment by a closed
cylinder of radius ρ with flat caps, called its tube (Figure 9)."

`tube a b ρ` is the closed cylinder of radius `ρ` with flat caps around `[a, b]`: the points `x`
having a foot point `y ∈ [a, b]` with `x − y ⊥ b − a` and `|x − y| ≤ ρ`. `IsMiddle ρ p q a b`
says that `a, b` are sampled terminals of the segment `[p, q]` with `10ρ ≤ |a − p| ≤ 10ρ + ρ²` and
`10ρ ≤ |b − q| ≤ 10ρ + ρ²`.

**Formalization Note** The choice of `a_e, b_e` is not unique; statements quantify over every
choice satisfying `IsMiddle`. The first endpoint `p` of the segment's pair is matched with `a`. -/
def tube (a b : V) (ρ : ℝ) : Set V :=
  {x | ∃ y ∈ segment ℝ a b, inner ℝ (x - y) (b - a) = 0 ∧ dist x y ≤ ρ}

/-- `(a, b)` is a middle segment of the cable segment `[p, q]`. -/
def IsMiddle (ρ : ℝ) (p q a b : V) : Prop :=
  a ∈ segSamples p q ρ ∧ b ∈ segSamples p q ρ ∧
  10 * ρ ≤ dist a p ∧ dist a p ≤ 10 * ρ + ρ ^ 2 ∧
  10 * ρ ≤ dist b q ∧ dist b q ≤ 10 * ρ + ρ ^ 2

end SteinerAPX


