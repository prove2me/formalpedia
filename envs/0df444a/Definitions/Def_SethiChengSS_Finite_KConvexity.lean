-- Prove2me | Definitions.Def_SethiChengSS_Finite_KConvexity
-- name    : SethiChengSS_Finite_KConvexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:01.740724+00:00
-- url     : https://prove2.me/theorems/cf6d7dbf-5aba-4efb-a7d4-b786676d43fc
-- title:
--   Definition 4.2 and Proposition 4.2, p. 934 — δ, K-convexity on a set, g(−∞), g*, S, s and h(x)
-- statement:
--   This file fixes the one-dimensional objects of §4 of Sethi and Cheng (1997) that do not depend on the inventory model.
--
--   **The step function.** $\delta(z) = 0$ for $z \le 0$ and $\delta(z) = 1$ for $z > 0$ (§2, p. 932).
--
--   **$K$-convexity on a set (Definition 4.2).** Let $K \ge 0$ and $D \subseteq \mathbb R$. A function $g$ is *$K$-convex on $D$* if
--
--   $$K + g(z+y) \;\ge\; g(y) + z\,\frac{g(y) - g(y-b)}{b}$$
--
--   for all $z \ge 0$, $b > 0$ and $y$ such that $y+z$, $y$ and $y-b$ all lie in $D$. For $D = \mathbb R$ this is Definition 4.1, inequality (4.3), which is the published definition `BertsekasKConvex`.
--
--   **The objects of Proposition 4.2.** Let $g:\mathbb R \to \mathbb R$ and let $A \le B$ be extended real numbers; the interval $[A,B]$ is open at an infinite endpoint, so only its real points are used.
--
--   1. $g(-\infty) = \liminf_{x\to-\infty} g(x)$, an extended real number; $g$ is extended to $\mathbb R \cup \{-\infty\}$ by this value.
--   2. $g^* = \inf_{A \le x \le B} g(x)$, the infimum over real $x$ in $[A,B]$ (4.4).
--   3. $S = \min\{x \in \mathbb R \cup \{-\infty\} \mid g(x) = g^*,\ A \le x \le B\}$ (4.5).
--   4. $s = \min\{x \in \mathbb R \cup \{-\infty\} \mid g(x) \le K + g(S),\ A \le x \le S\}$ (4.6).
--   5. $h(x) = \inf_{y \ge x,\ A \le y \le B}\,[K\delta(y-x) + g(y)]$ for real $x$.
--
--   $h(x)$ is the least cost of moving from level $x$ to some level $y \ge x$ in $[A,B]$ when a move costs $K$. Proposition 4.2 shows that $s$ and $S$ form the reorder point and order-up-to level of an $(s,S)$ rule for this problem.
--
--   **Formalization Note** The minima in (4.5) and (4.6) are taken as infima in the extended reals `EReal` of the sets described, with $+\infty$ excluded; that these infima are attained is part of the statement of Proposition 4.2 in this mission, not part of the definition. The value of the extension of $g$ at $+\infty$ is a junk value ($+\infty$) and never used. $g^*$ and $h$ are `EReal`-valued infima, so an empty range gives $+\infty$ and an unbounded one $-\infty$; Proposition 4.2 assumes $g^* > -\infty$ and proves $h$ finite on $(-\infty, B]$.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 932 (δ), p. 934, Definition 4.2, Proposition 4.2 (4.4)–(4.6) and (iii)

import Mathlib
import Definitions.Def_BertsekasKConvex

namespace SethiChengSS.Finite

open Filter

/-- The step function of Sethi–Cheng (1997), §2, p. 932: `δ(z) = 0` when `z ≤ 0` and `1` when
`z > 0`. -/
noncomputable def delta (z : ℝ) : ℝ := if 0 < z then 1 else 0

/-- Definition 4.2 of Sethi–Cheng (1997), p. 934: a function `g` is `K`-convex on a (convex) set
`D ⊆ ℝ` if inequality (4.3), `K + g(z + y) ≥ g(y) + z (g(y) − g(y − b)) / b` for `z ≥ 0`, `b > 0`,
holds whenever `y + z`, `y` and `y − b` all lie in `D`. (The paper writes `g : R → D`; the
function is read as defined at least on `D`.) With `D = univ` this is `BertsekasKConvex K g`,
Definition 4.1 / (4.3). -/
def KConvexOn (K : ℝ) (D : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ z b y : ℝ, 0 ≤ z → 0 < b → y + z ∈ D → y ∈ D → y - b ∈ D →
    g y + (z / b) * (g y - g (y - b)) ≤ K + g (z + y)

/-- `g(−∞)`, Proposition 4.2, p. 934: the extended real number `liminf_{x → −∞} g(x)`. -/
noncomputable def gNegInf (g : ℝ → ℝ) : EReal :=
  liminf (fun x : ℝ => (g x : EReal)) atBot

/-- `g` extended to `ℝ ∪ {−∞}` as in Proposition 4.2: `g(−∞) = liminf_{x→−∞} g(x)`, `g(x)` at a
real `x`; the value at `+∞` is a junk value `+∞` and is never used. -/
noncomputable def gExt (g : ℝ → ℝ) (x : EReal) : EReal :=
  if x = ⊥ then gNegInf g else if x = ⊤ then ⊤ else (g x.toReal : EReal)

/-- The real points of the extended interval `[A, B]`; the interval is open at `A` if `A = −∞`
and at `B` if `B = +∞` (Proposition 4.2). -/
def IccE (A B : EReal) : Set ℝ := {x : ℝ | A ≤ (x : EReal) ∧ (x : EReal) ≤ B}

/-- The real points of `(−∞, B]` (the whole line when `B = +∞`). -/
def IicE (B : EReal) : Set ℝ := {x : ℝ | (x : EReal) ≤ B}

/-- (4.4): `g* = inf_{A ≤ x ≤ B} g(x)`, an extended real number. -/
noncomputable def gStar (g : ℝ → ℝ) (A B : EReal) : EReal :=
  ⨅ x ∈ IccE A B, (g x : EReal)

/-- (4.5): `S = min{x ∈ ℝ ∪ {−∞} | g(x) = g*, A ≤ x ≤ B}`, taken as the infimum of that set in
`EReal` (`+∞` is excluded from the set). -/
noncomputable def bigS (g : ℝ → ℝ) (A B : EReal) : EReal :=
  sInf {x : EReal | x ≠ ⊤ ∧ A ≤ x ∧ x ≤ B ∧ gExt g x = gStar g A B}

/-- (4.6): `s = min{x ∈ ℝ ∪ {−∞} | g(x) ≤ K + g(S), A ≤ x ≤ S}`, taken as the infimum of that set
in `EReal`. -/
noncomputable def smallS (g : ℝ → ℝ) (K : ℝ) (A B : EReal) : EReal :=
  sInf {x : EReal | x ≠ ⊤ ∧ A ≤ x ∧ x ≤ bigS g A B ∧
    gExt g x ≤ (K : EReal) + gExt g (bigS g A B)}

/-- Proposition 4.2(iii): `h(x) = inf_{y ≥ x, A ≤ y ≤ B} [K δ(y − x) + g(y)]`, valued in `EReal`
(an empty range gives `+∞`). -/
noncomputable def hFun (g : ℝ → ℝ) (K : ℝ) (A B : EReal) (x : ℝ) : EReal :=
  ⨅ y ∈ {y : ℝ | x ≤ y ∧ A ≤ (y : EReal) ∧ (y : EReal) ≤ B},
    ((K * delta (y - x) + g y : ℝ) : EReal)

end SethiChengSS.Finite


