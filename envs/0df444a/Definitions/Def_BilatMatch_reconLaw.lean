-- Prove2me | Definitions.Def_BilatMatch_reconLaw
-- name    : BilatMatch_reconLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:12:33.670093+00:00
-- url     : https://prove2.me/theorems/9038600b-48c0-4798-b042-a0bb33b7e9fe
-- title:
--   Seller reconstruction $\hat F_S$ and the regularized market $\hat{\mathcal I}^\alpha$
-- statement:
--   Fix a seller with costs $c_1<\dots<c_m$ and masses $f_S(c_k)$, $F_S(c_k)=\sum_{h\le k}f_S(c_h)$, and let $\Phi$ be the greatest convex minorant of the curve through $(F_S(c_k),\Phi_k)$, $\Phi_k=\sum_{h\le k}f_S(c_h)\tau^\alpha_S(c_h)$. The **reconstructed costs** $\hat c_k$ solve
--   $$\hat C_k+\alpha F_S(c_k)\hat c_k=\Phi(F_S(c_k)),\qquad \hat C_k=\sum_{h\le k}f_S(c_h)\hat c_h,$$
--   and the reconstructed prior $\hat F_S$ puts mass $f_S(c_k)$ on $\hat c_k$. **Regularization** replaces every finitely supported seller prior by its reconstruction and leaves other priors unchanged; $\hat{\mathcal I}^\alpha$ is the market with every seller prior regularized.
--
--   **Formalization Note** Atoms are indexed from $0$. The coefficient $f_S(c_k)+\alpha F_S(c_k)$ of $\hat c_k$ is positive for $\alpha\ge0$, so the recursion is a division by a positive number.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), App. B.1 Seller Regularization, p.31 (pdf p.33), Proposition 3.7, p.14 (pdf p.16)

import Mathlib
import Definitions.Def_BilatMatch_iron

open MeasureTheory

namespace BilatMatch

/-!
# Seller reconstruction (regularization)

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), App. B.1 "Seller Regularization", p.31
(pdf p.33), and Proposition 3.7, p.14 (pdf p.16).

**Formalization Note**
* The atoms of a finitely supported prior are listed increasingly as `sortedAtom μ 0 < ⋯ <
  sortedAtom μ (m − 1)`, `m = nAtoms μ` (indices start at `0`, the paper's start at `1`).
* With `f_k`, `F_k` the mass and the cumulative mass of the `k`-th atom and `Φ` the greatest convex
  minorant of the points `(F_S(c_k), Φ_k)`, the reconstructed costs solve
  `Ĉ_k + α F_S(c_k) ĉ_k = Φ(F_S(c_k))`, `Ĉ_k = ∑_{h ≤ k} f_S(c_h) ĉ_h`, i.e.
  `ĉ_k = (Φ(F_k) − Ĉ_{k−1}) / (f_k + α F_k)`; `reconCum μ k` is `Ĉ_{k−1}` (sum over `h < k`).
* `reconLaw α μ` puts the original mass `f_k` on `ĉ_k`. `regularize α μ` is `reconLaw α μ` for a
  finitely supported prior and `μ` itself otherwise (sellers with interval support are left
  unchanged, p.14).
-/

open Classical in
/-- The atoms of `μ` in increasing order (empty if there are infinitely many). -/
noncomputable def sortedAtoms (μ : Measure ℝ) : List ℝ :=
  if h : (atoms μ).Finite then h.toFinset.sort (· ≤ ·) else []

/-- The number of atoms. -/
noncomputable def nAtoms (μ : Measure ℝ) : ℕ := (sortedAtoms μ).length

/-- The `k`-th smallest atom (`0`-indexed). -/
noncomputable def sortedAtom (μ : Measure ℝ) (k : ℕ) : ℝ := (sortedAtoms μ).getD k 0

/-- The mass `f_k = Pr(X = c_k)` of the `k`-th atom. -/
noncomputable def atomMass (μ : Measure ℝ) (k : ℕ) : ℝ := (μ {sortedAtom μ k}).toReal

/-- The cumulative mass `F_k = Pr(X ≤ c_k)` of the `k`-th atom. -/
noncomputable def atomCum (μ : Measure ℝ) (k : ℕ) : ℝ := (μ (Set.Iic (sortedAtom μ k))).toReal

/-- `Φ(F_S(c_k))`: the greatest convex minorant of the seller's cumulative `α`-virtual-cost curve
at the cumulative mass of the `k`-th atom. -/
noncomputable def minorantAt (α : ℝ) (μ : Measure ℝ) (k : ℕ) : ℝ :=
  gcm (cumCurve μ (alphaVirtualCost α μ)) (atomCum μ k)

/-- `reconCum α μ k = Ĉ_{k−1} = ∑_{h < k} f_h ĉ_h`, by recursion on `k`. -/
noncomputable def reconCum (α : ℝ) (μ : Measure ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => reconCum α μ k + atomMass μ k *
      ((minorantAt α μ k - reconCum α μ k) / (atomMass μ k + α * atomCum μ k))

/-- The reconstructed cost `ĉ_k = (Φ(F_k) − Ĉ_{k−1}) / (f_k + α F_k)` (p.31). -/
noncomputable def reconCost (α : ℝ) (μ : Measure ℝ) (k : ℕ) : ℝ :=
  (minorantAt α μ k - reconCum α μ k) / (atomMass μ k + α * atomCum μ k)

/-- The reconstructed seller prior `F̂_S`: mass `f_S(c_k)` at `ĉ_k`. -/
noncomputable def reconLaw (α : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  ∑ k ∈ Finset.range (nAtoms μ), μ {sortedAtom μ k} • Measure.dirac (reconCost α μ k)

open Classical in
/-- Full-prior regularization: a finitely supported prior is replaced by its reconstruction; any
other prior is left unchanged. -/
noncomputable def regularize (α : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  if IsFiniteSupport μ then reconLaw α μ else μ

variable {B S : Type*}

/-- The market `Î^α` (Proposition 3.7): every seller prior regularized, everything else kept. -/
noncomputable def regularizedMarket (α : ℝ) (I : Market B S) : Market B S :=
  { I with sellerLaw := fun j => regularize α (I.sellerLaw j) }

end BilatMatch


