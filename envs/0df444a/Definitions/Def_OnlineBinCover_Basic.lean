-- Prove2me | Definitions.Def_OnlineBinCover_Basic
-- name    : OnlineBinCover_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:49.61+00:00
-- url     : https://prove2.me/theorems/ad35ed3b-091d-4e60-bfe4-714bc79e71d3
-- title:
--   Bin covering instances, covered bins, $\mathrm{OPT}$, volume and ranks
-- statement:
--   An **instance** with $n$ items is a vector of sizes $s=(s_0,\dots,s_{n-1})$, item $i$ carrying the label $i$; it is **valid** when every size lies in $(0,1]$. For a set $J$ of items, $\mathrm{vol}(J)=\sum_{i\in J}s_i$ and $\mathrm{vol}(I)=\sum_i s_i$.
--
--   An assignment of items to bins is a label map $b$ from items to bin names. Bin $\ell$ is **covered** when the items of $J$ carrying label $\ell$ have total size at least $1$, and $\mathrm{covered}_J(b)$ counts the covered bins. The optimum is
--
--   $$\mathrm{OPT}(J)=\max_{a:\{0,\dots,n-1\}\to\{0,\dots,n-1\}}\mathrm{covered}_J(a),\qquad \mathrm{OPT}(I)=\mathrm{OPT}(\text{all items}).$$
--
--   Since a covered bin holds at least one item, $n$ bin names suffice, so this is the maximum number of bins the items can cover.
--
--   The **rank** of an item in $J$ is its position in decreasing order of size; ties are broken by the smaller label, the same rule in $I$ and in every subset (the paper's "Ties are resolved consistently across $I$ and its subsets").
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** `OPTon s J` is a finite supremum of natural numbers over label maps `Fin n → Fin n`; `rankIn s J i` is the $1$-based rank, computed from the strict order `before s`.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §1, p.1 (PDF p.2); §2, p.6 (PDF p.7)

import Mathlib

namespace OnlineBinCover

/-!
# Bin covering instances, covered bins, OPT, volume and ranks

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §1 p.1 (instances, OPT, vol) and §2 p.6
(notation for subsets, ranks).

**Formalization Note.**
* An instance with `n` items is a size vector `s : Fin n → ℝ`; the multiset `I` is `s` with its
  items labelled by `Fin n`. `ValidSizes s` says every size lies in `(0, 1]`.
* An assignment of items to bins is a label map `b : Fin n → α` (bins are the labels). A bin is
  covered when the items carrying its label have total size at least `1`. `coveredOn s J b` counts
  the covered bins when only the items of `J` are assigned (the items outside `J` are ignored).
* `OPTon s J` is the maximum number of covered bins over label maps `Fin n → Fin n`; `n` labels
  suffice because a covered bin holds at least one item, so this is the maximum over all
  assignments. `OPT s := OPTon s univ`. Both are finite suprema of natural numbers (no `sSup`).
* Ranks are positions in decreasing order of size; ties are resolved by the item label, the same
  rule in `I` and in every subset (p.6: "Ties are resolved consistently across I and its
  subsets"). `before s i j` says that `i` precedes `j`; `rankIn s J i` is the `1`-based rank of `i`
  among the items of `J`.
-/

open Finset

/-- Every item size lies in `(0, 1]` (§1, p.1). -/
def ValidSizes {n : ℕ} (s : Fin n → ℝ) : Prop := ∀ i, 0 < s i ∧ s i ≤ 1

/-- `vol(J) = ∑_{i ∈ J} s_i`, the volume of the items of `J` (§2, p.6). -/
noncomputable def volOn {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) : ℝ := ∑ i ∈ J, s i

/-- `vol(I) = ∑_i s_i`, the total volume (§1, p.1). -/
noncomputable def vol {n : ℕ} (s : Fin n → ℝ) : ℝ := ∑ i, s i

/-- The load of bin `ℓ`: the total size of the items of `J` carrying label `ℓ`. -/
noncomputable def binLoadOn {n : ℕ} {α : Type*} [DecidableEq α] (s : Fin n → ℝ)
    (J : Finset (Fin n)) (b : Fin n → α) (ℓ : α) : ℝ :=
  ∑ t ∈ J.filter (fun t => b t = ℓ), s t

/-- The number of covered bins (load at least `1`) when the items of `J` are assigned by `b`. -/
noncomputable def coveredOn {n : ℕ} {α : Type*} [DecidableEq α] (s : Fin n → ℝ)
    (J : Finset (Fin n)) (b : Fin n → α) : ℕ :=
  ((J.image b).filter (fun ℓ => 1 ≤ binLoadOn s J b ℓ)).card

/-- The number of covered bins when all items are assigned by `b`. -/
noncomputable def covered {n : ℕ} {α : Type*} [DecidableEq α] (s : Fin n → ℝ)
    (b : Fin n → α) : ℕ :=
  coveredOn s Finset.univ b

/-- `OPT(J)`: the maximum number of bins the items of `J` can cover (§2, p.6). -/
noncomputable def OPTon {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) : ℕ :=
  Finset.univ.sup (fun a : Fin n → Fin n => coveredOn s J a)

/-- `OPT(I)`: the maximum number of covered bins (§1, p.1). -/
noncomputable def OPT {n : ℕ} (s : Fin n → ℝ) : ℕ := OPTon s Finset.univ

/-- `i` precedes `j` in decreasing order of size, ties broken by the smaller label. -/
def before {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) : Prop := s j < s i ∨ (s i = s j ∧ i < j)

/-- The `1`-based rank of item `i` among the items of `J`, in decreasing order of size with ties
by label (§2, p.6). -/
noncomputable def rankIn {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (i : Fin n) : ℕ :=
  by classical exact (J.filter (fun j => before s j i)).card + 1

end OnlineBinCover


