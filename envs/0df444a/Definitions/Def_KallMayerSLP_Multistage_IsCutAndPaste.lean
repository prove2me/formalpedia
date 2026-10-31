-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_IsCutAndPaste
-- name    : KallMayerSLP_Multistage_IsCutAndPaste
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:16:55.742995+00:00
-- url     : https://prove2.me/theorems/cdc8b7cb-329a-4cb7-be13-1f504f8c62d3
-- title:
--   The cut and paste procedure S1–S4
-- statement:
--   A scenario tree $\mathcal T^+$ arises from $\mathcal T$ by **cut and paste** at a node $i$ of a stage $s\ge2$ if a parent-preserving map from the nodes of $\mathcal T^+$ to those of $\mathcal T$ exhibits the following:
--
--   1. the nodes over $i$ are exactly two distinct nodes $i_1,i_2$, and $\Xi^s_i$ is the disjoint union of their cells (step S1);
--   2. every proper descendant of $i$ has exactly one copy below each of $i_1$ and $i_2$, with the same cell (steps S2, S4);
--   3. every other node has exactly one copy, with the same cell.
--
--   **Formalization Note** The steps S1 and S3 also assign probabilities and right-hand sides to the new tree. Here these are not data: the optimal value on $\mathcal T^+$ computes them by (3.13) from the cells of $\mathcal T^+$, which is what S1 and S3 prescribe.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, "Cut and paste", steps S1–S4, p.268 (PDF 277)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ScenarioTree_anc

namespace KallMayerSLP.Multistage

/-- `𝒯p` arises from `𝒯` by the **cut and paste** node splitting procedure S1–S4 (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, p.268, PDF 277): a node `i` of a stage `s ≥ 2`
is split into `i₁` and `i₂`, its cell being partitioned into theirs, and the subtree below `i` is
duplicated, one copy below each of `i₁`, `i₂`. The map `φ` sends each node of `𝒯p` to the node of
`𝒯` it comes from, respecting parents. Precisely:

* the nodes over `i` are exactly `i₁ ≠ i₂`, and `Ξ^s_i` is the disjoint union of their cells (S1);
* every proper descendant `m` of `i` has exactly one copy below each of `i₁`, `i₂` (S2, S4), with
  the same cell as `m`;
* every node outside the subtree of `i` is kept: it has a single copy, with the same cell (the
  root, which is always outside, has no cell in the book, so its `cell` value is not compared).

**Formalization Note.** The steps S1 and S3 assign probabilities and right-hand sides to the new
tree. These are not data here: in `aggValue` they are computed by (3.13) from the cells of `𝒯p`,
which is what S1 and S3 prescribe, since `p_{i_ν} = r_ν p_i`, and the right-hand sides of the
copies are `b_{t_n}(ζ̂^n)` for the new histories. -/
structure IsCutAndPaste {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 𝒯p : ScenarioTree D Ξ)
    {s : ℕ} (i : 𝒯.Node s) (i₁ i₂ : 𝒯p.Node s) (φ : ∀ t, 𝒯p.Node t → 𝒯.Node t) : Prop where
  two_le : 2 ≤ s
  le_T : s ≤ D.T
  map_parent : ∀ t, 1 ≤ t → t < D.T → ∀ n : 𝒯p.Node (t + 1),
    φ t (𝒯p.parent t n) = 𝒯.parent t (φ (t + 1) n)
  ne : i₁ ≠ i₂
  map_left : φ s i₁ = i
  map_right : φ s i₂ = i
  fiber : ∀ n, φ s n = i → n = i₁ ∨ n = i₂
  cell_union : 𝒯p.cell s i₁ ∪ 𝒯p.cell s i₂ = 𝒯.cell s i
  cell_disjoint : Disjoint (𝒯p.cell s i₁) (𝒯p.cell s i₂)
  outside_unique : ∀ t, 1 ≤ t → t ≤ D.T → ∀ m : 𝒯.Node t, (∀ h : s ≤ t, 𝒯.anc h m ≠ i) →
    ∃! n, φ t n = m
  outside_cell : ∀ t, 2 ≤ t → t ≤ D.T → ∀ m : 𝒯.Node t, (∀ h : s ≤ t, 𝒯.anc h m ≠ i) →
    ∀ n, φ t n = m → 𝒯p.cell t n = 𝒯.cell t m
  below_unique : ∀ t (h : s ≤ t), t ≤ D.T → ∀ m : 𝒯.Node t, 𝒯.anc h m = i →
    ∀ b, (b = i₁ ∨ b = i₂) → ∃! n, φ t n = m ∧ 𝒯p.anc h n = b
  below_cell : ∀ t (h : s ≤ t), s < t → t ≤ D.T → ∀ m : 𝒯.Node t, 𝒯.anc h m = i →
    ∀ n, φ t n = m → 𝒯p.cell t n = 𝒯.cell t m

end KallMayerSLP.Multistage


