-- Prove2me | Definitions.Def_DelaunayStretch_DiskChain
-- name    : DelaunayStretch_DiskChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:32.33621+00:00
-- url     : https://prove2.me/theorems/6c09dbb3-bd8f-462b-9ae2-8bc7fd0bad22
-- title:
--   Disk chains $(O_1,\dots,O_n;u,v)$, conditions (C1)–(C4)
-- statement:
--   Let $n\ge1$. A **disk chain** $(O_1,\dots,O_n;u,v)$ consists of closed disks $O_1,\dots,O_n$ with centers $o_i$ and radii $r_i>0$, together with two points $u,v$ on the $x$-axis with $u\in\partial O_1$, $v\in\partial O_n$ and $x(u)<x(v)$, such that:
--
--   1. (C1) for every $1\le i\le n-1$, the circles $\partial O_i$ and $\partial O_{i+1}$ meet in exactly two points $a_i$ and $b_i$, where $y(a_i)>0>y(b_i)$; the segment $G_i=[a_i,b_i]$ is the $i$-th gate and $c_i$ is the point where the $x$-axis crosses $G_i$;
--   2. (C2) $x(o_1)<x(o_2)<\dots<x(o_n)$;
--   3. (C3) $x(u)<x(c_1)<\dots<x(c_{n-1})<x(v)$;
--   4. (C4) for every $2\le i\le n-1$, on the upper arc of $O_i$ the point $a_{i-1}$ does not come after $a_i$, and on the lower arc of $O_i$ the point $b_{i-1}$ does not come after $b_i$.
--
--   The conventions $a_0=b_0=u$, $a_n=b_n=v$, $c_0=u$, $c_n=v$ and $|G_i|=\|a_i-b_i\|$ (so $|G_0|=|G_n|=0$) are part of the definition.
--
--   Disk chains abstract the circumdisks of the Delaunay triangles crossed by a segment $[u,v]$; the whole upper-bound proof works with them.
--
--   **Formalization Note** Disks and gate ends are indexed by natural numbers with the paper's indices ($O_i$ for $1\le i\le n$, $a_i,b_i$ for $1\le i\le n-1$); other indices are never read. "Meet in exactly two points" is the set equality $\partial O_i\cap\partial O_{i+1}=\{a_i,b_i\}$. (C3) is stated as $x(c_i)<x(c_{i+1})$ for $0\le i\le n-1$. Arc order uses the angle parameters of the disk definition.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Definition 2.1, p.12; conventions of Definition 2.2, p.12, and §3.1, p.15

import Mathlib
import Definitions.Def_DelaunayStretch_Disk

namespace DelaunayStretch

/-- The data of a **disk chain** `(O₁, …, Oₙ; u, v)` (Definition 2.1, p.12): the number `n` of
disks, the disks `O i` (`1 ≤ i ≤ n`), the two ends `u, v`, and the ends `a i`, `b i` of the
gates `Gᵢ = [aᵢ, bᵢ]` (`1 ≤ i ≤ n − 1`). The conditions are `DiskChain.IsDiskChain`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026),
Definition 2.1, p.12.

**Formalization Note** Indices are the paper's: `O : ℕ → Disk` is read at `1, …, n` and
`a b : ℕ → ℂ` at `1, …, n − 1`; values at other indices are never used. The gate ends `aᵢ, bᵢ`
are data, but condition (C1) determines them (they are the two common points of `∂Oᵢ` and
`∂Oᵢ₊₁`, `aᵢ` the upper one). -/
structure DiskChain where
  /-- the number of disks `n` -/
  n : ℕ
  /-- the disks `O₁, …, Oₙ` -/
  O : ℕ → Disk
  /-- the left end `u` -/
  u : ℂ
  /-- the right end `v` -/
  v : ℂ
  /-- the upper gate ends `a₁, …, aₙ₋₁` -/
  a : ℕ → ℂ
  /-- the lower gate ends `b₁, …, bₙ₋₁` -/
  b : ℕ → ℂ

namespace DiskChain

/-- The upper end `aᵢ` of the `i`-th gate, with the convention `a₀ = u`, `aₙ = v`
(Definition 2.2, p.12). -/
noncomputable def A (C : DiskChain) (i : ℕ) : ℂ :=
  if i = 0 then C.u else if i = C.n then C.v else C.a i

/-- The lower end `bᵢ` of the `i`-th gate, with the convention `b₀ = u`, `bₙ = v`
(Definition 2.2, p.12). -/
noncomputable def B (C : DiskChain) (i : ℕ) : ℂ :=
  if i = 0 then C.u else if i = C.n then C.v else C.b i

/-- The point `cᵢ` where the `x`-axis crosses the gate `Gᵢ` (condition (C1), p.12), with the
convention `c₀ = u`, `cₙ = v` (§3.1, p.15). -/
noncomputable def c (C : DiskChain) (i : ℕ) : ℂ :=
  if i = 0 then C.u else if i = C.n then C.v else axisCrossing (C.a i) (C.b i)

/-- The length `|Gᵢ| = ‖aᵢ − bᵢ‖` of the `i`-th gate; `|G₀| = |Gₙ| = 0` (p.12, p.15). -/
noncomputable def gateLength (C : DiskChain) (i : ℕ) : ℝ := dist (C.A i) (C.B i)

/-- **Disk chain** (Definition 2.1, p.12). Let `n ≥ 1`. A disk chain `(O₁, …, Oₙ; u, v)`
consists of closed disks `O₁, …, Oₙ` with centers `oᵢ` and radii `rᵢ > 0`, and two points
`u, v` on the `x`-axis with `u ∈ ∂O₁`, `v ∈ ∂Oₙ` and `x(u) < x(v)`, such that

* (C1) for `1 ≤ i ≤ n − 1`, the circles `∂Oᵢ` and `∂Oᵢ₊₁` meet in exactly the two points `aᵢ`,
  `bᵢ`, where `y(aᵢ) > 0 > y(bᵢ)`;
* (C2) `x(o₁) < ⋯ < x(oₙ)`;
* (C3) `x(u) < x(c₁) < ⋯ < x(cₙ₋₁) < x(v)`;
* (C4) for `2 ≤ i ≤ n − 1`, on the upper arc of `Oᵢ` the point `aᵢ₋₁` does not come after
  `aᵢ`, and on the lower arc of `Oᵢ` the point `bᵢ₋₁` does not come after `bᵢ`.

**Formalization Note** "Meet in exactly two points" is the set equality
`∂Oᵢ ∩ ∂Oᵢ₊₁ = {aᵢ, bᵢ}`. (C3) is written as `x(cᵢ) < x(cᵢ₊₁)` for `0 ≤ i ≤ n − 1` with
`c₀ = u`, `cₙ = v`; for `n = 1` it is `x(u) < x(v)`. The order on the arcs is through the angle
parameters of `Disk.upperAngle`, `Disk.lowerAngle`. -/
def IsDiskChain (C : DiskChain) : Prop :=
  1 ≤ C.n ∧
  (∀ i, 1 ≤ i → i ≤ C.n → 0 < (C.O i).radius) ∧
  C.u.im = 0 ∧ C.v.im = 0 ∧
  C.u ∈ (C.O 1).boundary ∧ C.v ∈ (C.O C.n).boundary ∧ C.u.re < C.v.re ∧
  -- (C1)
  (∀ i, 1 ≤ i → i + 1 ≤ C.n →
    (C.O i).boundary ∩ (C.O (i + 1)).boundary = {C.a i, C.b i} ∧
      0 < (C.a i).im ∧ (C.b i).im < 0) ∧
  -- (C2)
  (∀ i, 1 ≤ i → i + 1 ≤ C.n → (C.O i).center.re < (C.O (i + 1)).center.re) ∧
  -- (C3)
  (∀ i, i + 1 ≤ C.n → (C.c i).re < (C.c (i + 1)).re) ∧
  -- (C4)
  (∀ i, 2 ≤ i → i + 1 ≤ C.n →
    (C.O i).UpperNotAfter (C.a (i - 1)) (C.a i) ∧ (C.O i).LowerNotAfter (C.b (i - 1)) (C.b i))

end DiskChain

end DelaunayStretch


