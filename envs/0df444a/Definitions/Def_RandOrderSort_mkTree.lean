-- Prove2me | Definitions.Def_RandOrderSort_mkTree
-- name    : RandOrderSort_mkTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:03:08.829935+00:00
-- url     : https://prove2.me/theorems/1147eb95-5e3e-4db3-b2c7-39e72752766c
-- title:
--   Empirical partition trees, display (7)
-- statement:
--   Given a prefix of $m$ observed keys in the order $y_1<\dots<y_m$ and a power of two $b\le m$, the empirical partition tree has internal boundaries
--   $$y_{\lfloor mj/b\rfloor},\qquad 1\le j<b,$$
--   and the outer boundaries $-\infty,+\infty$. Its leaves are the $b$ intervals between consecutive boundaries, left-closed and right-open, except that the last also includes $+\infty$; the interval containing a key or label is its canonical leaf. The tree distance between two leaves is twice the height of their least common ancestor (`lcaH`).
--
--   The module also defines node intervals, the cut $\beta$ on extended keys with $\beta(-\infty)=0$, $\beta(+\infty)=1$, the leaf containing a cut (`cutLeaf`), the clipped length $|I\cap[0,1]|$ (`clipLen`), the count of a key set in a node (`countIn`), and the uniform law of a $t$-subset of a fixed population (`subsetProb`).
--
--   **Formalization Note** Keys are arrival indices compared by a strict order `lt`. A node is a pair (height $h$, index $\mathrm{idx}$), meaning the $2^h$ leaves $\ell$ with $\lfloor\ell/2^h\rfloor=\mathrm{idx}$.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §3.1, p.12, display (7); §4.1.2, p.21 (span); §4.2, p.23 (|I|)

import Mathlib

namespace RandOrderSort

/-! # Empirical partition trees (§3.1, p.12, display (7))

Kang, Fan, arXiv:2610.15438 (version of 2026-11-01), §3.1, p.12: "Given a prefix of m observed
keys, sort pointers to them in the order y_1 < · · · < y_m. For a power of two b ≤ m, choose the
internal boundaries y_{⌊mj/b⌋}, 1 ≤ j < b, (7) and the outer boundaries −∞, +∞. … Intervals are
left-closed and right-open, except that the last also includes its virtual right endpoint. In
particular, the first interval contains the label −∞. Repeatedly pairing adjacent intervals gives
a perfect binary partition tree. … The interval containing a key is its canonical leaf." "Buckets
are indexed from left to right in key order, and the distance between two buckets is the number of
tree edges between their leaves."

**Formalization Note.**
* Keys are arrival indices `a : ℕ`, compared by a strict order `lt` (the key order of the run);
  `Ext` adds the virtual endpoints `−∞` (`ninf`) and `+∞` (`pinf`). Labels and keys share `Ext`.
* A tree is its number of leaves `b` and its internal boundaries `bd j` (`1 ≤ j < b`), each an
  observed key; `mkTree lt P b` builds (7) from the observed set `P` (`y_r` is the element of `P`
  with exactly `r − 1` elements of `P` below it). Leaves are `0, …, b − 1`; leaf `ℓ` is
  `[bd ℓ, bd (ℓ+1))` with `bd 0 = −∞`, and the last leaf includes `+∞`.
* A node is a pair `(h, idx)` (height `h`, index `idx`): the `2^h` leaves `ℓ` with
  `ℓ / 2^h = idx`. The tree distance between leaves `u, v` is `2·lcaH u v`, where `lcaH u v` is
  the height of their least common ancestor.
* A cut is a predicate `β` on keys ("above the cut", `β_q(x) = 1[x > q]` of p.20), extended by
  `β(−∞) = 0`, `β(+∞) = 1`. For a cut that is upward closed in the key order, `cutLeaf` is the leaf
  containing the cut (left endpoint below it, right endpoint above it), and the node of height `h`
  containing the cut ("selected", span one, p.21) is `cutLeaf / 2^h`.
* `clipLen` is the length `|I ∩ [0,1]|` of a node interval for real values `val` of the keys, with
  virtual endpoints clipped to `0` and `1` (p.23).
-/

/-- Extended keys: the virtual endpoint `−∞`, the key of arrival `a`, and `+∞`. -/
inductive Ext where
  | ninf
  | key (a : ℕ)
  | pinf
  deriving DecidableEq

/-- The strict order on extended keys induced by `lt`. -/
def extLt (lt : ℕ → ℕ → Bool) : Ext → Ext → Bool
  | .ninf, .ninf => false
  | .ninf, _ => true
  | .key _, .ninf => false
  | .key a, .key b => lt a b
  | .key _, .pinf => true
  | .pinf, _ => false

/-- `z` lies in the interval from `e₁` to `e₂`: left-closed, right-open, except that `+∞` belongs
to an interval whose right endpoint is `+∞`. -/
def inIvl (lt : ℕ → ℕ → Bool) (e₁ e₂ z : Ext) : Bool :=
  !(extLt lt z e₁) && (extLt lt z e₂ || (e₂ == .pinf && z == .pinf))

/-- An empirical partition tree: `leaves` buckets and internal boundaries `bd j`, `1 ≤ j < leaves`. -/
structure Tree where
  leaves : ℕ
  bd : ℕ → ℕ

/-- The number of elements of `P` strictly below `a` in the order `lt`. -/
def rankIn (lt : ℕ → ℕ → Bool) (P : Finset ℕ) (a : ℕ) : ℕ :=
  (P.filter (fun a' => lt a' a)).card

/-- `y_r` (`r` 1-based): the element of `P` with exactly `r − 1` elements of `P` below it. -/
def elemOfRank (lt : ℕ → ℕ → Bool) (P : Finset ℕ) (r : ℕ) : ℕ :=
  ((P.sort (· ≤ ·)).find? (fun e => rankIn lt P e + 1 = r)).getD 0

/-- **The empirical partition tree (7)** with `b` leaves built from the observed keys `P`:
internal boundary `j` is `y_{⌊|P| j / b⌋}`. -/
def mkTree (lt : ℕ → ℕ → Bool) (P : Finset ℕ) (b : ℕ) : Tree :=
  ⟨b, fun j => elemOfRank lt P (P.card * j / b)⟩

/-- The canonical leaf of an extended key: the number of internal boundaries at or below it
(`−∞` lies in leaf `0`, `+∞` in the last leaf). -/
def canonLeaf (lt : ℕ → ℕ → Bool) (tr : Tree) : Ext → ℕ
  | .ninf => 0
  | .key a => ((Finset.Ico 1 tr.leaves).filter (fun j => !(lt a (tr.bd j)))).card
  | .pinf => tr.leaves - 1

/-- The left endpoint of leaf `ℓ` (the label given to the cells of bucket `ℓ`). -/
def leftEnd (tr : Tree) (ℓ : ℕ) : Ext := if ℓ = 0 then .ninf else .key (tr.bd ℓ)

/-- The left endpoint `ℓ(v)` of node `(h, idx)`. -/
def nodeLeft (tr : Tree) (h idx : ℕ) : Ext := leftEnd tr (idx * 2 ^ h)

/-- The right endpoint `r(v)` of node `(h, idx)` (`+∞` for the last node of its level). -/
def nodeRight (tr : Tree) (h idx : ℕ) : Ext :=
  if tr.leaves ≤ (idx + 1) * 2 ^ h then .pinf else .key (tr.bd ((idx + 1) * 2 ^ h))

/-- The height of the least common ancestor of leaves `u` and `v` in a perfect binary tree
(half their tree distance). -/
def lcaH (u v : ℕ) : ℕ :=
  if h : u = v then 0 else lcaH (u / 2) (v / 2) + 1
termination_by u + v
decreasing_by omega

/-- A cut extended to the virtual endpoints: `β(−∞) = 0`, `β(+∞) = 1`. -/
def betaE (β : ℕ → Bool) : Ext → Bool
  | .ninf => false
  | .key a => β a
  | .pinf => true

/-- `span_q(v) = β_q(r(v)) − β_q(ℓ(v))` (p.21), as a Boolean "the node contains the cut". -/
def span (β : ℕ → Bool) (tr : Tree) (h idx : ℕ) : Bool :=
  !(betaE β (nodeLeft tr h idx)) && betaE β (nodeRight tr h idx)

/-- The leaf containing the cut `β`: the number of internal boundaries below the cut. -/
def cutLeaf (β : ℕ → Bool) (tr : Tree) : ℕ :=
  ((Finset.Ico 1 tr.leaves).filter (fun j => !(β (tr.bd j)))).card

/-- Endpoint values clipped to `[0,1]`, for the lower end of `I ∩ [0,1]`. -/
def loClip (val : ℕ → ℝ) : Ext → ℝ
  | .ninf => 0
  | .key a => max 0 (val a)
  | .pinf => 1

/-- Endpoint values clipped to `[0,1]`, for the upper end of `I ∩ [0,1]`. -/
def hiClip (val : ℕ → ℝ) : Ext → ℝ
  | .ninf => 0
  | .key a => min 1 (val a)
  | .pinf => 1

/-- `|I| = |I ∩ [0,1]|` (p.23) for the node `(h, idx)`, the keys having real values `val`. -/
noncomputable def clipLen (val : ℕ → ℝ) (tr : Tree) (h idx : ℕ) : ℝ :=
  max 0 (hiClip val (nodeRight tr h idx) - loClip val (nodeLeft tr h idx))

/-- The number of keys of the set `P` whose canonical leaf lies below the node `(h, idx)`. -/
def countIn (lt : ℕ → ℕ → Bool) (tr : Tree) (P : Finset ℕ) (h idx : ℕ) : ℕ :=
  (P.filter (fun a => canonLeaf lt tr (.key a) / 2 ^ h = idx)).card

/-- The uniform probability of an event on the `t`-subsets of `{0, …, P − 1}` (a uniformly chosen
`t`-subset, as in the reverse exposure of §4.3). -/
noncomputable def subsetProb (P t : ℕ) (E : Finset ℕ → Prop) : ℝ :=
  by classical exact
    (((Finset.range P).powersetCard t).filter E).card / ((Finset.range P).powersetCard t).card

/-- The natural order of population elements `0, 1, 2, …` (a fixed strictly ordered population). -/
def natLt (a b : ℕ) : Bool := decide (a < b)

end RandOrderSort


