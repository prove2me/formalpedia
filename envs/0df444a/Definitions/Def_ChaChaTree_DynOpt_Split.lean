-- Prove2me | Definitions.Def_ChaChaTree_DynOpt_Split
-- name    : ChaChaTree_DynOpt_Split
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:21:46.554799+00:00
-- url     : https://prove2.me/theorems/bd91de50-8e79-4396-9b1a-7b8878a4ac61
-- title:
--   Splits (Def. 5), DepthAlt_S (Def. 6), doubleswitches_S and mixedturns_S
-- statement:
--   **Definition 5.** A partition $S = (S_1,\dots,S_k)$ of $[N]$ into disjoint contiguous intervals ordered from left to right is encoded by its segment map: `IsSegmentation N k seg` says that `seg` maps $[N]$ monotonically onto $[k]$, and $S_i = \{x \in [N] \mid \mathrm{seg}(x) = i\}$. For $p = (x,t)$, $s(p) = (\mathrm{seg}(x), t)$. The split of $P$ consists of the **contracted instance** $\hat P = s(P)$ and the **filtered instances** $\check P_i = P \cap (S_i \times [T])$. For $\Phi$ on instances, $\Delta_S\Phi(P) = \Phi(P) - (\Phi(\hat P) + \sum_{i\in[k]} \Phi(\check P_i))$ (`deltaS`).
--
--   **Definition 6.** The active direction after $p \in P$ (with $p.x \in S_i$) is DOWN if $\mathrm{pd}(p) \neq \bot$ and $\mathrm{pd}(p).x \in S_i$, and UP otherwise. $\mathrm{DepthAlt}_S(P)$ counts the changes from DOWN to UP: the points $q$ whose predecessor $\mathrm{pre}(q)$ exists with direction DOWN while the direction after $q$ is UP.
--
--   $\mathrm{doubleswitches}_S(P)$ (Lemma 8) counts the points $p$ that are a switch in $\check P_i$ for $S_i \ni p.x$ and whose image $s(p)$ is a switch in $\hat P$.
--
--   $\mathrm{mixedturns}_S(P)$ (Lemma 9) counts the points $p \in P$ such that (1) $p' = \mathrm{nd}_P(p)$ exists and lies in the segment $S_i \ni p.x$; (2) some $q \in P \setminus \check P_i$ makes $(p, p', q)$ a turn with $q.y \in (p.y, h.y)$, where $h$ is the next point after $p$ for which $h' = \mathrm{nd}_P(h)$ exists and $h.x, h'.x \in S_i$; if no such $h$ exists, $q.y \in (p.y, \infty)$ suffices.
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Definitions 5–6, pp. 12 (PDF 13); Lemmas 8–9, pp. 12–13 (PDF 13–14)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-! # Splits (Definition 5), `DepthAlt_S` (Definition 6), `doubleswitches_S`, `mixedturns_S`

Čech et al., *Dynamic Optimality to within O(log log log n)*, STOC 2027 submission (manuscript,
sha256 9316fbfd…), §4.2, pp. 12–13 (PDF 13–14).

A partition `S = (S₁, …, S_k)` of `[N]` into disjoint contiguous intervals ordered from left to
right is encoded by its **segment map** `seg : ℕ → ℕ`, `seg x = i` iff `x ∈ S_i`: a monotone map
from `[N]` onto `[k]` (`IsSegmentation N k seg`). Monotone and onto is exactly "contiguous,
nonempty, ordered left to right"; values of `seg` outside `[N]` are never used. -/

/-- `seg` encodes a partition `S = (S₁, …, S_k)` of `[N]` into `k` nonempty contiguous intervals
ordered from left to right (`S_i = {x ∈ [N] | seg x = i}`). -/
def IsSegmentation (N k : ℕ) (seg : ℕ → ℕ) : Prop :=
  (∀ x ∈ Finset.Icc 1 N, seg x ∈ Finset.Icc 1 k) ∧
    (∀ x ∈ Finset.Icc 1 N, ∀ y ∈ Finset.Icc 1 N, x ≤ y → seg x ≤ seg y) ∧
    ∀ i ∈ Finset.Icc 1 k, ∃ x ∈ Finset.Icc 1 N, seg x = i

/-- `s(p) = (i, t)` for a point `p = (x, t)` with `x ∈ S_i`. -/
def segPoint (seg : ℕ → ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (seg p.1, p.2)

/-- The **contracted instance** `P̂ := s(P)`: every segment is contracted to a single key. -/
def contracted (seg : ℕ → ℕ) (P : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  P.image (segPoint seg)

/-- The **filtered instance** `P̌_i := P ∩ (S_i × [T])`: the points of `P` with key in `S_i`
(original keys and times are kept). -/
def filtered (seg : ℕ → ℕ) (P : Finset (ℕ × ℕ)) (i : ℕ) : Finset (ℕ × ℕ) :=
  P.filter fun p => seg p.1 = i

/-- `Δ_S Φ(P) := Φ(P) − (Φ(P̂) + Σ_{i ∈ [k]} Φ(P̌_i))` (Lemma 7). -/
def deltaS (Φ : Finset (ℕ × ℕ) → ℤ) (k : ℕ) (seg : ℕ → ℕ) (P : Finset (ℕ × ℕ)) : ℤ :=
  Φ P - (Φ (contracted seg P) + ∑ i ∈ Finset.Icc 1 k, Φ (filtered seg P i))

/-- The **active direction after `p`** is DOWN: `pd(p) ≠ ⊥` and `pd(p).x` lies in the segment of
`p.x` (Definition 6). Otherwise (`pd(p) = ⊥` or `pd(p).x ∉ S_i`) it is UP. -/
abbrev ActiveDown (P : Finset (ℕ × ℕ)) (seg : ℕ → ℕ) (p : ℕ × ℕ) : Prop :=
  ∃ r ∈ P, IsPd P r p ∧ seg r.1 = seg p.1

instance (P : Finset (ℕ × ℕ)) (seg : ℕ → ℕ) (p : ℕ × ℕ) : Decidable (ActiveDown P seg p) := by
  unfold ActiveDown IsPd; infer_instance

/-- **Definition 6.** `DepthAlt_S(P)`: the number of times the active direction changes from
DOWN to UP, i.e. the number of points `q ∈ P` such that `p = pre(q)` exists, the active direction
after `p` is DOWN and the active direction after `q` is UP. -/
def depthAltS (seg : ℕ → ℕ) (P : Finset (ℕ × ℕ)) : ℕ :=
  (P.filter fun q => ∃ p ∈ P, IsPre P p q ∧ ActiveDown P seg p ∧ ¬ ActiveDown P seg q).card

/-- `doubleswitches_S(P)` (Lemma 8): the number of points `p ∈ P` such that `p` is a switch in
the filtered instance `P̌_i` of the segment `S_i ∋ p.x`, and `s(p)` is a switch in the
contracted instance `P̂`. -/
def doubleswitches (seg : ℕ → ℕ) (P : Finset (ℕ × ℕ)) : ℕ :=
  (P.filter fun p =>
    IsSwitch (filtered seg P (seg p.1)) p ∧ IsSwitch (contracted seg P) (segPoint seg p)).card

/-- `h` qualifies as an `h` of Lemma 9 for the segment `S_i`: `h' = nd_P(h)` exists and
`h.x, h'.x ∈ S_i`. -/
abbrev HasNdInSegment (P : Finset (ℕ × ℕ)) (seg : ℕ → ℕ) (i : ℕ) (h : ℕ × ℕ) : Prop :=
  ∃ h' ∈ P, IsNd P h h' ∧ seg h.1 = i ∧ seg h'.1 = i

instance (P : Finset (ℕ × ℕ)) (seg : ℕ → ℕ) (i : ℕ) (h : ℕ × ℕ) :
    Decidable (HasNdInSegment P seg i h) := by
  unfold HasNdInSegment IsNd; infer_instance

/-- `h` is **the next point after `p`** (time `> p.y`, minimal) for which `h' = nd_P(h)` exists
and `h.x, h'.x ∈ S_i`, where `S_i ∋ p.x`. -/
abbrev IsNextHPoint (P : Finset (ℕ × ℕ)) (seg : ℕ → ℕ) (p h : ℕ × ℕ) : Prop :=
  h ∈ P ∧ p.2 < h.2 ∧ HasNdInSegment P seg (seg p.1) h ∧
    ∀ r ∈ P, p.2 < r.2 → HasNdInSegment P seg (seg p.1) r → h.2 ≤ r.2

instance (P : Finset (ℕ × ℕ)) (seg : ℕ → ℕ) (p h : ℕ × ℕ) : Decidable (IsNextHPoint P seg p h) := by
  unfold IsNextHPoint; infer_instance

/-- `p` counts in `mixedturns_S(P)` (Lemma 9): (1) `p' := nd_P(p)` exists and shares the segment
`S_i ∋ p.x`; (2) some `q ∈ P ∖ P̌_i` (key outside `S_i`) makes `(p, p', q)` a turn with
`q.y ∈ (p.y, h.y)`, where `h` is the next point after `p` with `h' = nd_P(h)` existing and
`h.x, h'.x ∈ S_i`; if no such `h` exists, `q.y ∈ (p.y, ∞)` suffices. -/
abbrev IsMixedTurnPoint (P : Finset (ℕ × ℕ)) (seg : ℕ → ℕ) (p : ℕ × ℕ) : Prop :=
  ∃ p' ∈ P, IsNd P p p' ∧ seg p'.1 = seg p.1 ∧
    ∃ q ∈ P, seg q.1 ≠ seg p.1 ∧ IsTurn p p' q ∧ p.2 < q.2 ∧
      ∀ h ∈ P, IsNextHPoint P seg p h → q.2 < h.2

instance (P : Finset (ℕ × ℕ)) (seg : ℕ → ℕ) (p : ℕ × ℕ) : Decidable (IsMixedTurnPoint P seg p) := by
  unfold IsMixedTurnPoint IsNd IsTurn IsLeftPair IsRightPair; infer_instance

/-- `mixedturns_S(P)`: the number of points `p ∈ P` satisfying `IsMixedTurnPoint`. -/
def mixedturns (seg : ℕ → ℕ) (P : Finset (ℕ × ℕ)) : ℕ :=
  (P.filter fun p => IsMixedTurnPoint P seg p).card

end ChaChaTree.DynOpt


