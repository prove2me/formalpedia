-- Prove2me | Definitions.Def_BilateralProfit_SellerTree
-- name    : BilateralProfit_SellerTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:44.632183+00:00
-- url     : https://prove2.me/theorems/36194446-6ff3-47d6-9f47-4ade7af2e925
-- title:
--   Proof of Lemma 4.8, Steps 1–4 — the measure $\nu$ (16), the seller tree, Algorithm 3 and the representatives (19)
-- statement:
--   Let $\rho$ be a distribution on $G_K\times\mathcal A$, $P_0$ its trade function, $P_{P_0}$ the valuation marginal of $\rho$, and $\varepsilon>0$.
--
--   1. **The measure $\nu$** (eq. (16)): for a valuation law $P$ on $[0,1]^2$ with seller and buyer marginals $P_s,P_b$, $\nu=L\otimes P_b+P_s\otimes L+P$, with $L$ the Lebesgue measure on $[0,1]$. The construction uses $P=P_{P_0}$.
--   2. **The seller tree** (Step 1): the seller grid $G_{K,s}=\{0,1/K,\dots,1\}$ is split recursively; a node $I$ with $|I|\ge2$ gives its first $\lfloor |I|/2\rfloor$ elements (in increasing order) to the left child and the rest to the right child. For a seller price $p$ the root-to-leaf path is $I_0=G_{K,s}\supseteq I_1\supseteq\dots\supseteq I_h=\{p\}$.
--   3. **Algorithm 3** (buyer blocks of a node $I$): start with $D_1=\{\min G_{K,b}\}$; for each buyer price $q$ in increasing order, add $q$ to the current block $D_\ell$ if $\nu((\min I,\max I]\times[\min D_\ell,q))\le\varepsilon$, otherwise open a new block $D_{\ell+1}=\{q\}$.
--   4. **Representatives** (eq. (19)): for a node $I$ and a block $D$, $p_{I,D}=\min\arg\max_{p\in I}\{(\min D-p)P_0(p,\min D)\}$.
--   5. For a target $(p,q)$ and each node $I_j$ on the path of $p$, $D_j$ is the block of $I_j$ containing $q$; the prices $(p_{I_j,D_j},q)$ are those of the telescoping decomposition (21).
--
--   **Formalization Note** Coordinates are indices $0,\dots,K$ (value index$/K$). A node is a block of consecutive indices $lo,\dots,lo+len-1$; the root is $(0,K+1)$. A block is recorded by its least index. The representative is the first maximizer in increasing order.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), proof of Lemma 4.8, Steps 1–4, pp.24–25 (PDF 26–27): eq. (16), Algorithm 3, eq. (19), eq. (21)

import Mathlib
import Definitions.Def_BilateralProfit_Analysis

namespace BilateralProfit

open MeasureTheory

/-! # The construction in the proof of Lemma 4.8: the measure `ν`, the seller tree, the buyer
blocks (Algorithm 3) and the representatives (19)

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), proof of Lemma 4.8,
Steps 1–4, pp.24–25 (PDF 26–27): the seller tree (Step 1), `ν` (16), Algorithm 3, the
representatives `p_{I,D}` (19), and the root-to-leaf path of Step 4.

**Formalization Note.** Seller and buyer grid coordinates are indices `0, …, K` (value
`i/K`). A node `I` of the seller tree is a block of consecutive indices `lo, …, lo + len − 1`,
written `(lo, len)`; the root is `(0, K + 1)`, and a node with `len ≥ 2` has left child
`(lo, ⌊len/2⌋)` and right child `(lo + ⌊len/2⌋, len − ⌊len/2⌋)` (Step 1).
`min I = lo/K`, `max I = (lo + len − 1)/K`. Algorithm 3 is run over the buyer indices in
increasing order; its output partition is recorded by `blockStart`, the least index of the block
containing a buyer index, so `min D = blockStart/K`. The measure `ν` of (16) is built from the
valuation law `P_{P0}` of `ρ` (the marginal of `ρ` on `G_K`), with Lebesgue measure `L`
restricted to `[0, 1]`. The representative (19) is the smallest maximizer, found by a scan in
increasing order that only moves on a strict improvement. -/

/-- The measure `ν = L ⊗ P_b + P_s ⊗ L + P` (16) built from a valuation law `P` on `[0,1]²`, with
`L` the Lebesgue measure on `[0, 1]` and `P_s`, `P_b` the seller and buyer marginals. -/
noncomputable def nuMeas (μ : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (μ.map Prod.snd) +
    (μ.map Prod.fst).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) + μ

variable {K : ℕ}

/-- The valuation marginal `P_{P0}` of `ρ`: the law of `V` when `(V, A) ∼ ρ`, as a measure on
`ℝ × ℝ` (its trade function is `P0 ρ`). -/
noncomputable def margLaw (ρ : Grid K × Act K → ℝ) : Measure (ℝ × ℝ) :=
  ∑ x, ENNReal.ofReal (ρ x) • Measure.dirac (pt K x.1)

/-- The root-to-leaf path of the seller tree towards the seller index `i`, starting at the node
`(lo, len)`: nodes are split while `len ≥ 2`, the left child taking the first `⌊len/2⌋`
indices. The fuel `n` bounds the depth (fuel `K + 1` always reaches the leaf). -/
def descend : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, lo, len, _ => [(lo, len)]
  | n + 1, lo, len, i =>
    if len ≤ 1 then [(lo, len)]
    else (lo, len) :: (if i < lo + len / 2 then descend n lo (len / 2) i
      else descend n (lo + len / 2) (len - len / 2) i)

/-- The path `I_0 ⊇ I_1 ⊇ ⋯ ⊇ I_h = {p}` of Step 4 for the seller index `i` of `p`. -/
def sellerPath (K i : ℕ) : List (ℕ × ℕ) := descend (K + 1) 0 (K + 1) i

/-- Algorithm 3 for the node `I = (lo, len)`, threshold `ε`: the least index of the buyer block
containing the buyer index `j`. Scanning `q = 0, 1, …` the block of `q` is the current block if
`ν((min I, max I] × [min D_ℓ, q)) ≤ ε`, else a new block `{q}` starts. -/
noncomputable def blockStart (ρ : Grid K × Act K → ℝ) (ε : ℝ) (lo len : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
    let s := blockStart ρ ε lo len j
    if (nuMeas (margLaw ρ) (Set.Ioc ((lo : ℝ) / K) (((lo + len - 1 : ℕ) : ℝ) / K) ×ˢ
        Set.Ico ((s : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K))).toReal ≤ ε then s else j + 1

/-- The first maximizer of `f` along the list `l` (the smallest one, for an increasing list). -/
noncomputable def argmaxFirst (l : List ℕ) (f : ℕ → ℝ) : ℕ :=
  l.foldl (fun b i => if f b < f i then i else b) (l.headD 0)

/-- The representative (19) of the node `I = (lo, len)` and the buyer block with least index
`s`: `p_{I,D} = min argmax_{p ∈ I} (min D − p) P0(p, min D)`, as a seller index. -/
noncomputable def rep (ρ : Grid K × Act K → ℝ) (lo len s : ℕ) : ℕ :=
  argmaxFirst (List.range' lo len) fun i =>
    ((s : ℝ) / K - (i : ℝ) / K) * P0 ρ ((i : ℝ) / K, (s : ℝ) / K)

/-- The seller index `p_{I,D}` used in the telescoping decomposition (21) at node `I = (lo, len)`
for the target buyer index `j`: `D` is the block of `I` containing `j`. -/
noncomputable def repAt (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : ℕ × ℕ) (j : ℕ) : ℕ :=
  rep ρ I.1 I.2 (blockStart ρ ε I.1 I.2 j)

end BilateralProfit


