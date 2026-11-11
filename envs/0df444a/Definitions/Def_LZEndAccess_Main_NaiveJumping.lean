-- Prove2me | Definitions.Def_LZEndAccess_Main_NaiveJumping
-- name    : LZEndAccess_Main_NaiveJumping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:33:57.718279+00:00
-- url     : https://prove2.me/theorems/a3758818-fe0d-4340-ae69-e5c37a55c9bd
-- title:
--   Halved canonical partition, k-bad jumps, k-bad parents, the forests $T_k$, $(x,k)$-bad jumps and $\delta_x$
-- statement:
--   Integer intervals are sets of integers; $[u..v]$ with real endpoints is the set of integers in $[u,v]$.
--
--   - The **canonical partition** of $[a..b]$ consists of, for every integer $i\ge 0$ with $2^i\le (b-a)/2$ (i.e. $i\in[0..\lfloor\log((b-a)/2)\rfloor]$), the intervals $[a+2^i-1\,..\,\min(a+2^{i+1}-2,\tfrac{a+b}2)]$ and $[\max(b-2^{i+1}+2,\tfrac{a+b}2)\,..\,b-2^i+1]$.
--   - The **halved canonical partition** replaces each such interval $I=[x..y]$ with $|I|>1$ by $[x]$, $(x..x+|I|/2)$, $[x+|I|/2]$ and $(x+|I|/2..y]$; intervals of size at most one are kept.
--   - For a marked phrase $P=S[a..b]$ and $i\in P$, $M(i)=i-\delta\text{-}\mathrm{pre}(x,y)$ where $[x..y]$ is the interval of the halved canonical partition of $[a..b]$ containing $i$.
--   - For $k\in\mathbb K$, an index $i$ is a **k-bad jump** if $r_i\in[k,1.5k)$, $J(i)$ is defined and $r_{J(i)}\ge k$.
--   - The **k-bad parent** of a phrase $P$ is the unique phrase $P'$ such that $J(i)\in P'$ for every k-bad jump $i$ in $P$; $P$ has none if it has no k-bad jump. These parents form the forest $T_k$; $\pi_k^{(x)}(P)$ is the $x$-th ancestor of $P$ ($\pi_k^{(0)}(P)=P$).
--   - $i$ is an **$(x,k)$-bad jump** of $P$ if $J^y(i)\in\pi_k^{(y)}(P)$ for every $y\in[0..x]$, and $\delta_x(P)=\sum_{y=0}^{x}\delta_{\pi_k^{(y)}(P)}$.
--
--   **Formalization Note.** Definition 4.11 is transcribed as printed, including the real midpoint $\tfrac{a+b}2$ and the range $2^i\le(b-a)/2$; the set can leave indices uncovered or cover one twice (finding I4), and statements about "the interval containing $i$" quantify over every interval of the set that contains $i$. A missing ancestor contributes $0$ to $\delta_x$; it is used only where all ancestors exist.
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 14, Definitions 4.11, 4.12; pp. 16–18, Definition 4.17, k-bad parent and T_k, Definition 4.20, δ_x

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd

set_option autoImplicit false

namespace LZEndAccess.Main

open Classical

/-!
# Naive jumping: halved canonical partition, `M`, k-bad jumps, the forests `T_k`

Boneh, Gawrychowski, *Random Access to LZ-End: Faster and Deterministic*, arXiv:2607.14923
(sha256 3c96c6ff…), §4.2 p. 14 (Definitions 4.11, 4.12), §4.3 pp. 16–18 (Definitions 4.17,
4.20, the k-bad parent, `T_k`, `π_k^{(x)}`, `δ_x`).

**Formalization Note.**
* An integer interval is a set of naturals. Definition 4.11 is transcribed literally: interval
  endpoints such as `(a+b)/2` are real numbers and `[u..v]` is the set of integers in `[u, v]`;
  `i ∈ [0..⌊log((b−a)/2)⌋]` is written `2^i ≤ (b−a)/2` (no index when `(b−a)/2 < 1`). An
  interval `I = [x..y]` of the canonical partition with `|I| > 1` is replaced by `[x]`,
  `(x..x+|I|/2)`, `[x+|I|/2]`, `(x+|I|/2..y]` (again integers in real intervals).
* `M(i) = i − δ-pre(x, y)` for the interval `[x..y]` of the halved canonical partition of the
  marked phrase containing `i` (Definition 4.12) is used through `IsHalvedCanon`, which says that
  `[x..y]` is such an interval.
* `IsKBadJump Z k i`: `r_i ∈ [k, 1.5k)` and `J(i)` is defined with `r_{J(i)} ≥ k`
  (Definition 4.17).
* `kBadParent Z k t` is "the unique phrase `P'` such that every k-bad jump `i` of `P_t` has
  `J(i) ∈ P'`" (p. 16), `none` when `P_t` has no k-bad jump (or no such phrase exists). The
  forest `T_k` is given by this parent map; `kAnc Z k t x = π_k^{(x)}(P_t)` (`none` above the
  root).
* `deltaX Z k x t = δ_x(P_t) = Σ_{y=0}^{x} δ_{π_k^{(y)}(P_t)}` (p. 18); a missing ancestor
  contributes `0` (it is only used where all ancestors exist).
-/

/-- The canonical partition of `[a..b]` (Definition 4.11, items 1 and 2). -/
def canonIntervals (a b : ℕ) : Set (Set ℕ) :=
  {I | ∃ e : ℕ, (2 : ℝ) ^ e ≤ ((b : ℝ) - a) / 2 ∧
    (I = {i : ℕ | (a : ℝ) + 2 ^ e - 1 ≤ i ∧
              (i : ℝ) ≤ min ((a : ℝ) + 2 ^ (e + 1) - 2) (((a : ℝ) + b) / 2)} ∨
     I = {i : ℕ | max ((b : ℝ) - 2 ^ (e + 1) + 2) (((a : ℝ) + b) / 2) ≤ i ∧
              (i : ℝ) ≤ (b : ℝ) - 2 ^ e + 1})}

/-- The halved canonical partition of `[a..b]` (Definition 4.11): every interval `I = [x..y]`
of the canonical partition with `|I| > 1` is split into `[x]`, `(x..x+|I|/2)`, `[x+|I|/2]` and
`(x+|I|/2..y]`; intervals of size at most one are kept. -/
def halvedCanon (a b : ℕ) : Set (Set ℕ) :=
  {K | ∃ I ∈ canonIntervals a b,
    (I.ncard ≤ 1 ∧ K = I) ∨
    (∃ x y : ℕ, x < y ∧ I = {i | x ≤ i ∧ i ≤ y} ∧
      (K = {x} ∨
       K = {i : ℕ | x < i ∧ (i : ℝ) < (x : ℝ) + ((y + 1 - x : ℕ) : ℝ) / 2} ∨
       K = {i : ℕ | (i : ℝ) = (x : ℝ) + ((y + 1 - x : ℕ) : ℝ) / 2} ∨
       K = {i : ℕ | (x : ℝ) + ((y + 1 - x : ℕ) : ℝ) / 2 < i ∧ i ≤ y}))}

/-- `[x..y]` is an interval of the halved canonical partition of the phrase `P_t`. -/
def IsHalvedCanon (Z : List Phrase) (t x y : ℕ) : Prop :=
  {i | x ≤ i ∧ i ≤ y} ∈ halvedCanon (ph Z t).a (ph Z t).b

/-- `i` is a k-bad jump (Definition 4.17): `r_i ∈ [k..1.5k)` and `r_{J(i)} ≥ k`. -/
def IsKBadJump (Z : List Phrase) (k : ℝ) (i : ℕ) : Prop :=
  k ≤ (rVal Z i : ℝ) ∧ (rVal Z i : ℝ) < 3 / 2 * k ∧
    ∃ j, J Z i = some j ∧ k ≤ (rVal Z j : ℝ)

/-- The k-bad parent of `P_t` (p. 16): the unique phrase `P'` such that every k-bad jump `i` in
`P_t` has `J(i) ∈ P'`; `none` if `P_t` has no k-bad jump. -/
noncomputable def kBadParent (Z : List Phrase) (k : ℝ) (t : ℕ) : Option ℕ :=
  if h : ∃ t', (∃ i, InPhrase Z t i ∧ IsKBadJump Z k i) ∧
      ∀ i, InPhrase Z t i → IsKBadJump Z k i → ∀ j, J Z i = some j → InPhrase Z t' j then
    some (Classical.choose h)
  else none

/-- The `x`-th ancestor `π_k^{(x)}(P_t)` of `P_t` in the forest `T_k` (p. 18). -/
noncomputable def kAnc (Z : List Phrase) (k : ℝ) (t : ℕ) : ℕ → Option ℕ
  | 0 => some t
  | x + 1 => (kAnc Z k t x).bind (kBadParent Z k)

/-- `i` is an `(x, k)`-bad jump of `P_t` (Definition 4.20): for every `y ∈ [0..x]`, `J^y(i)` is
contained in `π_k^{(y)}(P_t)`. -/
def IsXKBadJump (Z : List Phrase) (k : ℝ) (x t i : ℕ) : Prop :=
  ∀ y, y ≤ x → ∃ Q j, kAnc Z k t y = some Q ∧ Jiter Z y i = some j ∧ InPhrase Z Q j

/-- `δ_x(P_t) = Σ_{y=0}^{x} δ_{π_k^{(y)}(P_t)}` (p. 18). -/
noncomputable def deltaX (Z : List Phrase) (k : ℝ) (x t : ℕ) : ℕ :=
  ∑ y ∈ Finset.range (x + 1), (match kAnc Z k t y with
    | some Q => delta Z Q
    | none => 0)

end LZEndAccess.Main


