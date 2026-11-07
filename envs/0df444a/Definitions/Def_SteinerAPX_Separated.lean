-- Prove2me | Definitions.Def_SteinerAPX_Separated
-- name    : SteinerAPX_Separated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:58.143202+00:00
-- url     : https://prove2.me/theorems/5b1a1117-f86e-4b32-a25a-bf7bbf034e57
-- title:
--   Separated cables (Definition 6)
-- statement:
--   The cables of a cable layout in $\mathbb R^D$ are **separated** if the following hold.
--
--   **(S1) Between cables.**
--
--   1. The balls $B_s$ (radius $20$, centre $z_s$) are pairwise more than $20$ apart.
--   2. Inside each ball $B_s$ the cables consist exactly of the straight segments from the ports of $s$ directly away from $z_s$ to the boundary of $B_s$: $\Gamma_i\cap B_s=[p_{s,i},\,z_s+20v_{s,i}]$ when $i$ labels a port of $s$, and $\Gamma_i\cap B_s=\emptyset$ otherwise.
--   3. Any two points on different cables less than $20$ apart lie in a common ball.
--
--   **(S2) Within a cable.**
--
--   4. Every cable segment has length at least $1$.
--   5. Non-incident segments of the same cable are at least $1$ apart.
--   6. Incident segments of the same cable meet at an angle of at least $45^\circ$.
--
--   Separation is the hypothesis of the cable reduction (Theorem 7): it rules out unintended cheap connections between cables away from the gadgets.
--
--   **Formalization Note** "More than 20 apart" is read pointwise for points of two distinct balls. Segments are the elements of the cable's network; incidence is a shared endpoint, tested in both orientations, and the angle is the unoriented angle at the shared endpoint.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Definition 6, §4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_SteinerAPX_CableLayout

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Separated cables (Definition 6).** S. Bartlmae, *Inapproximability of Euclidean Steiner
Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), Definition 6, §4.1, p.14 (PDF p.16):
"The cables are separated if the following conditions hold.
(S1) Between cables. The balls Bs are pairwise more than 20 apart. Inside each ball Bs, the
cables consist exactly of the straight segments extending from the ports of s directly away from
zs to the boundary of Bs. Any two points on different cables less than 20 apart lie in a common
ball.
(S2) Within a cable. Every cable segment has length at least 1. Non-incident segments of the same
cable are at least 1 apart, and incident segments meet at an angle of at least 45°."
and: "Explicitly, the segments in (S1) are (zs + b, zs + 20b) for b ∈ {±b1, ±b2} when s is a
square, and (zs + (2/3)b, zs + 20b) for b ∈ {±b1} when s is a fallback."

Conditions, in order: (S1a) any point of `B_s` and any point of `B_{s'}`, `s ≠ s'`, are more
than 20 apart; (S1b) the part of cable `Γᵢ` inside `B_s` is the radial segment from `p_{s,i}` to
`z_s + 20 · dir` when `i` labels a port of `s`, and empty otherwise; (S1c) two points on different
cables at distance less than 20 lie in a common ball; (S2a) every segment of a cable has length at
least 1; (S2b) two segments of one cable with no common endpoint are at least 1 apart (pointwise);
(S2c) two distinct segments of one cable with a common endpoint `p` and other endpoints `a, a'`
form an angle `∠ a p a' ≥ π/4`.

**Formalization Note** "More than 20 apart" for balls is read pointwise, which for closed balls in
`ℝᴰ` is the distance between the sets. The segments of a cable are the elements of its network;
segments are unordered, so the incidence in (S2c) is tested for both orientations. -/
def Separated {H : Inst3DM} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : CableLayout H V) : Prop :=
  (∀ s s' : Gadget H, s ≠ s' → ∀ x ∈ L.ball s, ∀ y ∈ L.ball s', 20 < dist x y) ∧
  (∀ s : Gadget H, ∀ i : Label H,
    carrier (L.cable i) ∩ L.ball s = if i ∈ labels H s then L.radial s i else ∅) ∧
  (∀ i j : Label H, i ≠ j → ∀ x ∈ carrier (L.cable i), ∀ y ∈ carrier (L.cable j),
    dist x y < 20 → ∃ s : Gadget H, x ∈ L.ball s ∧ y ∈ L.ball s) ∧
  (∀ i : Label H, ∀ e ∈ L.cable i, 1 ≤ dist e.1 e.2) ∧
  (∀ i : Label H, ∀ e ∈ L.cable i, ∀ e' ∈ L.cable i,
    Disjoint ({e.1, e.2} : Set V) {e'.1, e'.2} →
    ∀ x ∈ segment ℝ e.1 e.2, ∀ y ∈ segment ℝ e'.1 e'.2, 1 ≤ dist x y) ∧
  (∀ i : Label H, ∀ e ∈ L.cable i, ∀ e' ∈ L.cable i, e ≠ e' → ∀ p a a' : V,
    ({e.1, e.2} : Set V) = {p, a} → ({e'.1, e'.2} : Set V) = {p, a'} →
    Real.pi / 4 ≤ InnerProductGeometry.angle (a - p) (a' - p))

end SteinerAPX


