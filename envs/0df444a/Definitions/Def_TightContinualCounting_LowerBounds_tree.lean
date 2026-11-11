-- Prove2me | Definitions.Def_TightContinualCounting_LowerBounds_tree
-- name    : TightContinualCounting_LowerBounds_tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:11.231117+00:00
-- url     : https://prove2.me/theorems/7849fe9b-1f8f-44d5-ab32-7bd285915988
-- title:
--   Ordered four-ary tree, repeated inputs, centered scores, and shifted residuals
-- statement:
--   For positive $H,k$ let $m=4^H$ and $q=km\le n$. The expansion $E_k(x)$ repeats each of the $m$ bits $k$ times and pads the rest of the length-$n$ stream with zero. Flip $x$ at coordinate $j$ to obtain $x\oplus e_j$. A tree node numbered $v$ at zero-based depth $h$ represents the consecutive leaf interval starting at $v4^{H-h}$ of length $4^{H-h}$, and the corresponding stream interval of length $k4^{H-h}$. Its children, numbered $0,1,2,3$, are the consecutive quarters.
--
--   For a probe $\phi$ and a vector $y\in\mathbb R^q$, set $d^{02}=\phi_{u_2}(y)-\phi_{u_0}(y)$ and $d^{13}=\phi_{u_3}(y)-\phi_{u_1}(y)$. With $\operatorname{clip}_a(z)=\max\{-a,\min\{a,z\}\}$ and $\tau\in\{-1,1\}$, the four child weights are
--
--   $$
--   (-\operatorname{clip}_a(\tau d^{13}-1/2),\ \operatorname{clip}_a(\tau d^{02}-1/2),\ \operatorname{clip}_a(\tau d^{13}-1/2),\ -\operatorname{clip}_a(\tau d^{02}-1/2)).
--   $$
--
--   The partial path score sums the first $t$ edges on the root-to-$j$ path. The final score $S_\phi(j,y)$ is the maximum of the two complete path sums for $\tau=\pm1$. For a fixed input $x$ and any $W\in\mathbb R^n$, define
--
--   $$
--   Y_j=(W-A_nE_k(x\oplus e_j))_{[q]}/k,\quad
--   R=\|W-A_nE_k(x)\|_\infty,\quad
--   Q=\frac1q\sum_{t\in[q]}(W-A_nE_k(x))_t^2.
--   $$
--
--   The general path sum also accepts arbitrary real edge weights for Lemma 10. All tree intervals, scores and residuals are computed from these data, without assuming accuracy or privacy conclusions.
--
--   **Formalization Note** Tree addresses and coordinates are zero-based. On valid depths $h<H$ node indices satisfy $v<4^h$; arbitrary function values at other addresses are unused. Partial paths are truncated at $H$. Expansion and division are used only with $k\ge1$ in source results.
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), §3.2 pp.8–9; Lemma 11 p.10, definitions of Y, R, Q

import Mathlib
import Definitions.Def_ContinualCounting_prefixSum
import Definitions.Def_TightContinualCounting_LowerBounds_probes

namespace TightContinualCounting.LowerBounds

/-- Flip exactly the selected bit. -/
def flip {m : ℕ} (x : Fin m → Bool) (j : Fin m) : Fin m → Bool :=
  fun i => if i = j then !(x i) else x i

/-- Repeat each bit k times, then pad with zero (p.8); the test also handles bad dimensions. -/
def expand {m : ℕ} (n k : ℕ) (x : Fin m → Bool) : Fin n → Bool :=
  fun t => if h : t.val / k < m then x ⟨t.val / k, h⟩ else false

/-- Node v at depth h is the consecutive interval of 4^(H-h) leaves numbered from v*4^(H-h). -/
def nodeCoordinates (H k h v : ℕ) : Finset (Fin (k * 4 ^ H)) :=
  Finset.univ.filter fun t =>
    k * (v * 4 ^ (H - h)) ≤ t.val ∧ t.val < k * ((v + 1) * 4 ^ (H - h))

/-- The ancestor of leaf j at depth h, for 0 ≤ h ≤ H. -/
def ancestor (H : ℕ) (j : Fin (4 ^ H)) (h : ℕ) : ℕ :=
  j.val / 4 ^ (H - h)

/-- Child index for the edge at depth h+1. -/
def pathChild (H : ℕ) (j : Fin (4 ^ H)) (h : ℕ) : Fin 4 :=
  ⟨(j.val / 4 ^ (H - (h + 1))) % 4, Nat.mod_lt _ (by decide)⟩

/-- A completely arbitrary edge weighting, with only valid h<H, v<4^h used by paths. -/
def pathSum (H : ℕ) (w : ℕ → ℕ → Fin 4 → ℝ)
    (t : ℕ) (j : Fin (4 ^ H)) : ℝ :=
  ∑ h ∈ Finset.range (min t H), w h (ancestor H j h) (pathChild H j h)

noncomputable def clip (a z : ℝ) : ℝ := max (-a) (min a z)

/-- Cross-parity centered weights in child order (-13,+02,+13,-02), p.9. -/
noncomputable def scoreWeight (H k : ℕ) (a : ℝ) (φ : ProbeRule)
    (τ : ℝ) (y : Fin (k * 4 ^ H) → ℝ) (h v : ℕ) (i : Fin 4) : ℝ :=
  let p := fun c => probe φ (nodeCoordinates H k (h + 1) (4 * v + c)) y
  let d02 := p 2 - p 0
  let d13 := p 3 - p 1
  if i.val = 0 then -clip a (τ * d13 - 1 / 2)
  else if i.val = 1 then clip a (τ * d02 - 1 / 2)
  else if i.val = 2 then clip a (τ * d13 - 1 / 2)
  else -clip a (τ * d02 - 1 / 2)

noncomputable def score (H k : ℕ) (a : ℝ) (φ : ProbeRule)
    (j : Fin (4 ^ H)) (y : Fin (k * 4 ^ H) → ℝ) : ℝ :=
  max (pathSum H (scoreWeight H k a φ (-1) y) H j)
      (pathSum H (scoreWeight H k a φ 1 y) H j)

/-- Shifted residual: mechanism output on x, truth on the flipped input, restricted to q (p.10). -/
noncomputable def shiftedResidual {n : ℕ} (H k : ℕ) (hq : k * 4 ^ H ≤ n)
    (x : Fin (4 ^ H) → Bool) (W : Fin n → ℝ) (j : Fin (4 ^ H)) :
    Fin (k * 4 ^ H) → ℝ :=
  fun t => (W ⟨t.val, lt_of_lt_of_le t.isLt hq⟩ -
    ContinualCounting.prefixSum (ContinualCounting.bitVec (expand n k (flip x j)))
      ⟨t.val, lt_of_lt_of_le t.isLt hq⟩) / (k : ℝ)

/-- R uses the entire n-vector. -/
noncomputable def residualMax {n m : ℕ} (k : ℕ)
    (x : Fin m → Bool) (W : Fin n → ℝ) : ℝ :=
  ‖W - ContinualCounting.prefixSum (ContinualCounting.bitVec (expand n k x))‖

/-- Q averages squared unshifted error over just the active q coordinates. -/
noncomputable def residualMeanSquare {n : ℕ} (H k : ℕ) (hq : k * 4 ^ H ≤ n)
    (x : Fin (4 ^ H) → Bool) (W : Fin n → ℝ) : ℝ :=
  (∑ t : Fin (k * 4 ^ H),
    (W ⟨t.val, lt_of_lt_of_le t.isLt hq⟩ -
      ContinualCounting.prefixSum (ContinualCounting.bitVec (expand n k x))
        ⟨t.val, lt_of_lt_of_le t.isLt hq⟩) ^ 2) / (k * 4 ^ H : ℕ)

end TightContinualCounting.LowerBounds


