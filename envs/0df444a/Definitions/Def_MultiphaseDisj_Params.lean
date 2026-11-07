-- Prove2me | Definitions.Def_MultiphaseDisj_Params
-- name    : MultiphaseDisj_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:41.935195+00:00
-- url     : https://prove2.me/theorems/68357847-cfbd-4728-91c0-d914a50f172a
-- title:
--   Parameters of the hard distribution: $\beta$, $\ell$, $n_i$, $s_i$, the epochs $I$ and the blocks $B_i$
-- statement:
--   Fix $n$ and $t=t_uw$. The hard distribution of the main proof uses the parameters
--   $$
--   \beta=t^4,\qquad \ell=\max\Big\{\ell\ge1:\ \ell\sum_{i=1}^{\ell}\beta^i\le n\Big\},\qquad n_i=\ell\beta^i,\qquad s_i=\sqrt{n_i/\ell}=\beta^{i/2}=t^{2i},
--   $$
--   for the epochs $i\in[\ell]=\{1,\dots,\ell\}$, the **Chronogram epochs**
--   $$
--   I=\{i\in[\ell]:\ i\ge 2(\ell+2)/3\},
--   $$
--   and pairwise disjoint **blocks** $B_1,\dots,B_\ell\subseteq[n]$ with $|B_i|=n_i$; the remaining coordinates are unused.
--
--   **Formalization Note** $\ell$ is computed as the largest admissible value below $n$; it is $0$ when no $\ell\ge1$ is admissible, a case excluded by the regime $t_uw\le n^{1/95}$ in which the paper works. The blocks are the consecutive intervals of lengths $n_1,\dots,n_\ell$ starting at coordinate $0$ (coordinates are 0-based); since $\sum_i n_i\le n$ they are pairwise disjoint subsets of $[n]$ of the required sizes, which is all the paper asks of its choice. The condition $i\ge2(\ell+2)/3$ is written $3i\ge2(\ell+2)$.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), §3.1 The hard distribution, p.15

import Mathlib

set_option autoImplicit false

namespace MultiphaseDisj

/-- `β := (tu w)⁴`, written as a function of `t = tu · w` (Ko, *Unconditional Boolean Dynamic Lower
Bounds from Disjointness*, arXiv:2610.10904, held version sha256 ba26649b…, §3.1, p.15). -/
def beta (t : ℕ) : ℕ := t ^ 4

/-- The number of epochs `ℓ` (§3.1, p.15): the largest integer `ℓ ≥ 1` with
`ℓ · Σ_{i=1}^{ℓ} βⁱ ≤ n`, where `t = tu · w`.

**Formalization Note** Computed by `Nat.findGreatest` below `n` (for `t ≥ 1` every admissible `ℓ`
is at most `n`); the value is `0` when no `ℓ ≥ 1` is admissible, a case the paper excludes
("in particular, such an ℓ exists", in the regime `tu w ≤ n^{1/95}`). -/
def ell (n t : ℕ) : ℕ :=
  Nat.findGreatest (fun l => 1 ≤ l ∧ l * ∑ i ∈ Finset.Icc 1 l, beta t ^ i ≤ n) n

/-- The block size `nᵢ := ℓ βⁱ` (§3.1, p.15). -/
def blockSize (n t i : ℕ) : ℕ := ell n t * beta t ^ i

/-- The per-block set size `sᵢ := √(nᵢ/ℓ) = β^{i/2} = (tu w)^{2i}` (§3.1, p.15; p.9 "si = (tuw)2i"),
an integer since `tu` and `w` are integers. -/
def setSize (t i : ℕ) : ℕ := t ^ (2 * i)

/-- The Chronogram epochs `I := {i ∈ [ℓ] : i ≥ 2(ℓ + 2)/3}` (§3.1, p.15). Epochs are `1`-based,
`[ℓ] = {1, …, ℓ}`. -/
def epochSet (n t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (ell n t)).filter (fun i => 2 * (ell n t + 2) ≤ 3 * i)

/-- The first coordinate of block `Bᵢ`: blocks are consecutive, `B₁` first. -/
def blockStart (n t i : ℕ) : ℕ := ∑ j ∈ Finset.Ico 1 i, blockSize n t j

/-- The block `Bᵢ ⊆ [n]` for `i ∈ [ℓ]` (§3.1, p.15: "Choose pairwise disjoint blocks
B1, . . . , Bℓ ⊆ [n] with |Bi| = ni").

**Formalization Note** The blocks are the consecutive intervals of lengths `n₁, n₂, …, n_ℓ`
starting at coordinate `0` (coordinates of `[n]` are `0`-based); since `Σᵢ nᵢ ≤ n` they are
pairwise disjoint subsets of `Fin n` with `|Bᵢ| = nᵢ`. The remaining coordinates are unused. -/
def block (n t i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n =>
    blockStart n t i ≤ x.val ∧ x.val < blockStart n t i + blockSize n t i)

end MultiphaseDisj


