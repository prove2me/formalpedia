-- Prove2me | Definitions.Def_WeakStrongMSR_Estimates
-- name    : WeakStrongMSR_Estimates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:32.899296+00:00
-- url     : https://prove2.me/theorems/76c05dad-1732-40c0-91c8-75d1ae16fd8a
-- title:
--   The witness count $h$, corrupt points, and the median estimates $\mathrm{md}(x,s)$ and $\mathrm{md}(x,J)$
-- statement:
--   Fix an absolute constant $c$ and $\gamma=\tfrac12-\delta$.
--
--   1. The **witness count** is $h=32\lceil c\log n/(32\gamma^2)\rceil$ (natural logarithm). This is App. A, Eq. (20); the main text's $h=32\lceil c\log n/32\rceil$ is the case $\delta=1/3$.
--   2. For a set $W$ and a corruption set $C$, a point $x\notin W$ is **corrupt for $W$** if at least $|W|/2$ of the pairs $\{x,w\}$, $w\in W$, are corrupted (Definition 3.2). $E_W$ denotes the set of such points.
--   3. The **witness radius** of a centre $s$ with witness set $W$ is $r_s=\max_{w\in W}d(s,w)$ (Eq. (2)).
--   4. With strong set $S$, the estimate of Eq. (3) is
--   $$\mathrm{md}(x,s)=\begin{cases}d(x,s) & x\in S,\\ \max\{0,\ \operatorname{median}_{w\in W}\tilde d(x,w)\}+r_s & x\notin S.\end{cases}$$
--   5. For a component root $c_J$ with fresh witnesses $W_J$, Eq. (14) is $\mathrm{md}(x,J)=\operatorname{median}_{w\in W_J}\big(\tilde d(x,w)+d(c_J,w)\big)$.
--
--   **Formalization Note** The median of an even number of values is the **lower median**, the $\lceil N/2\rceil$-th smallest of $N$ values. The paper does not fix which middle value it means.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), §2.3, p.5 (PDF 6); Eq. (20), p.34 (PDF 35); Definition 3.2, p.10 (PDF 11); Eqs. (2), (3), p.8 (PDF 9); Eq. (14), p.21 (PDF 22)

import Mathlib
import Definitions.Def_WeakStrongMSR_Model

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# Witness parameters, corrupt points and median distance estimates

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0): §2.3, p.5 and Eq. (20), p.34 (the witness count `h`);
Definition 3.2, p.10 (corrupt points); Eqs. (2), (3), p.8 (witness radius and estimate
`md(x, s)`); Eq. (14), p.21 (the component estimate `md(x, J)`).

This module bundles these small, tightly coupled definitions.

**Formalization Note.**
* `hParam c δ n = 32 ⌈c log n / (32 γ²)⌉` with `γ = 1/2 − δ` and the natural logarithm is the
  witness count of App. A, Eq. (20); the main text's `32 ⌈c log n / 32⌉` is its case `δ = 1/3` with
  `c` renamed.
* `h` is even, and the paper does not say which middle value "the median" of `h` values is; the
  algorithm uses the **lower median**, the `⌈h/2⌉`-th smallest value (R9). It is the entry of
  index `(h − 1)/2` of the sorted list.
* The witness radius of an empty set is `0` (witness sets have `h ≥ 1` points in the algorithm). -/

/-- The witness count `h = 32 ⌈c log n / (32 (1/2 − δ)²)⌉` of Eq. (20). -/
noncomputable def hParam (c : ℕ) (δ : ℝ) (n : ℕ) : ℕ :=
  32 * ⌈(c : ℝ) * Real.log n / (32 * (1 / 2 - δ) ^ 2)⌉₊

/-- Definition 3.2: a point `x ∉ W` is corrupt for `W` if at least `|W|/2` of its pairs to `W` are
in the corruption set `C`. -/
def IsCorruptFor {n : ℕ} (C : Finset (Sym2 (Fin n))) (W : Finset (Fin n)) (x : Fin n) : Prop :=
  x ∉ W ∧ (W.card : ℝ) / 2 ≤ ((W.filter (fun v => s(x, v) ∈ C)).card : ℝ)

/-- `E_W`: the set of points corrupt for `W` (Definition 3.2). -/
noncomputable def corruptSet {n : ℕ} (C : Finset (Sym2 (Fin n))) (W : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter (IsCorruptFor C W)

/-- The lower median of a finite multiset of reals: the entry of index `(N − 1)/2` of its sorted
list (`N` the number of values); `0` for the empty multiset. -/
noncomputable def lowerMedian (m : Multiset ℝ) : ℝ :=
  (m.sort (· ≤ ·)).getD ((m.card - 1) / 2) 0

/-- The witness radius `r_s = max_{w ∈ W} d(s, w)` of Eq. (2) (`0` for `W = ∅`). -/
noncomputable def witnessRadius {n : ℕ} (d : Fin n → Fin n → ℝ) (s : Fin n) (W : Finset (Fin n)) :
    ℝ :=
  if h : W.Nonempty then W.sup' h (d s) else 0

/-- The estimate `md(x, s)` of Eq. (3) for the centre `s` with witness set `W`, the strong set `S`
and the weak table `w`: `d(x, s)` for `x ∈ S`, and
`max {0, median_{v ∈ W} w(x, v)} + r_s` otherwise. -/
noncomputable def mdEst {n : ℕ} (d w : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (s : Fin n)
    (W : Finset (Fin n)) (x : Fin n) : ℝ :=
  if x ∈ S then d x s else max 0 (lowerMedian (W.val.map (w x))) + witnessRadius d s W

/-- The component estimate `md(x, J) = median_{v ∈ W_J} (w(x, v) + d(c_J, v))` of Eq. (14), for
the root `cJ` and the fresh witness set `W`. -/
noncomputable def mdComp {n : ℕ} (d w : Fin n → Fin n → ℝ) (cJ : Fin n) (W : Finset (Fin n))
    (x : Fin n) : ℝ :=
  lowerMedian (W.val.map (fun v => w x v + d cJ v))

end WeakStrongMSR


