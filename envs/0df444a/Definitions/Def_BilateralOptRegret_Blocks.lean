-- Prove2me | Definitions.Def_BilateralOptRegret_Blocks
-- name    : BilateralOptRegret_Blocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:41.359298+00:00
-- url     : https://prove2.me/theorems/1b870492-0c8f-49ef-8195-960986194e67
-- title:
--   §6.2 — mapped columns, fixed-endpoint blocks, $C$ (12), $V$, and the mapped reconstruction (19)
-- statement:
--   Given maps $v_j$, a **dyadic mapped column** has endpoints $(v_j(a),v_j(b))$ for $(a,b)\in\mathcal I^\star$, and a **correction mapped column** has endpoints $(v_j(i),i)$ for an index $i$. A **fixed-endpoint block** $\rho$ is a maximal consecutive set of rows on which the endpoints $(a_\rho,b_\rho)$ of a column are constant; the collection of blocks is $\mathcal P$. Its **eligible rows** $W_\rho$ are those of the block on which both endpoints are in $G_{\mathrm{qry}}$; ineligible rows do not split a block. The number of mapped-column changes is
--   $$C=\sum_{j=0}^{K-2}\Big(\sum_{(a,b)\in\mathcal I^\star}\mathbb 1\{(v_j(a),v_j(b))\ne(v_{j+1}(a),v_{j+1}(b))\}+\sum_{i=0}^{K-1}\mathbb 1\{v_j(i)\ne v_{j+1}(i)\}\Big).$$
--   For a block with distinct endpoints and $W_\rho\neq\emptyset$, the **region** is $R_\rho=(z_{a_\rho},z_{b_\rho}]\times(z_{\min W_\rho},z_{\max W_\rho}]$ with sorted endpoints, and the **cumulative mass** is $V=\sum_\rho\mathbb P(X\in R_\rho)$ over these blocks.
--
--   The loop over the blocks runs BinS on sorted endpoints and restores the sign. Its estimates are combined by the mapped decomposition (19) into estimates $\hat D_j(a,b)$ of $D_j(a,b)$.
--
--   **Formalization Note** Rows of $v$ are natural numbers. A table holds the estimate for each column and row, with default $0$. Blocks are processed in an unspecified order (`Finset.toList`), as the page does not fix one.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), §6.2, pp.22–24, (12), (13); Algorithm 3, p.40; (19), p.29

import Mathlib
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program
import Definitions.Def_BilateralOptRegret_Dyadic
import Definitions.Def_BilateralOptRegret_BinS

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-! # Mapped columns, fixed-endpoint blocks, `C` (12), `V`, and the loop of BinS calls

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…), §6.2, pp.22–24; Algorithm 3, lines 4–14, p.40.

**Formalization Note.** A family of mappings is `v : ℕ → Idx n → Idx n`, with `v j` the map `v_j` of row `j`.
A mapped column `Col n` is a pair `(a, b) ∈ I⋆` (`Sum.inl`) with endpoints `(v_j(a), v_j(b))`, or an index `i` (`Sum.inr`)
with endpoints `(v_j(i), i)` (p.37); `cols n` has all `i ∈ {0, …, K − 1}` (p.23). A block is `(c, r₁, r₂)`: a maximal
consecutive set of rows on which the endpoints of `c` are constant. Ineligible rows do not split a block (p.23). A table
`Table n` holds the estimate of `F(x_{b_ρ,j}) − F(x_{a_ρ,j})` for each column `c` and row `j`, with default `0`. Blocks
are processed in the order of `Finset.toList`, an unspecified order, as on p.40. -/

/-- The mapped columns: dyadic ones (`Sum.inl`) and correction ones (`Sum.inr`). -/
abbrev Col (n : ℕ) : Type := (Idx n × Idx n) ⊕ Idx n

/-- A block: a column and its first and last rows. -/
abbrev Block (n : ℕ) : Type := Col n × Idx n × Idx n

/-- A table of estimates per mapped column and row. -/
abbrev Table (n : ℕ) : Type := Col n → Idx n → ℝ

/-- All mapped columns (p.23). -/
def cols (n : ℕ) : Finset (Col n) :=
  (Istar n).map Function.Embedding.inl ∪ Finset.univ.map Function.Embedding.inr

/-- The endpoints of a mapped column at row `j`: `(v_j(a), v_j(b))` or `(v_j(i), i)`. -/
def colEnds {n : ℕ} (v : ℕ → Idx n → Idx n) (j : ℕ) : Col n → Idx n × Idx n
  | .inl p => (v j p.1, v j p.2)
  | .inr i => (v j i, i)

/-- `(c, r₁, r₂)` is a maximal consecutive set of rows on which the endpoints of `c` are constant (p.23). -/
def IsMaxBlock {n : ℕ} (v : ℕ → Idx n → Idx n) (ρ : Block n) : Prop :=
  ρ.2.1 ≤ ρ.2.2 ∧
  (∀ j : Idx n, ρ.2.1 ≤ j → j ≤ ρ.2.2 → colEnds v j.val ρ.1 = colEnds v ρ.2.1.val ρ.1) ∧
  (ρ.2.1.val = 0 ∨ colEnds v (ρ.2.1.val - 1) ρ.1 ≠ colEnds v ρ.2.1.val ρ.1) ∧
  (ρ.2.2.val = 2 ^ n ∨ colEnds v (ρ.2.2.val + 1) ρ.1 ≠ colEnds v ρ.2.2.val ρ.1)

instance {n : ℕ} (v : ℕ → Idx n → Idx n) (ρ : Block n) : Decidable (IsMaxBlock v ρ) := by
  unfold IsMaxBlock; infer_instance

/-- The collection `P` of fixed-endpoint blocks (p.23). -/
def blocks {n : ℕ} (v : ℕ → Idx n → Idx n) : Finset (Block n) :=
  Finset.univ.filter fun ρ => ρ.1 ∈ cols n ∧ IsMaxBlock v ρ

/-- The endpoints `(a_ρ, b_ρ)` of a block (p.23). -/
def blockEnds {n : ℕ} (v : ℕ → Idx n → Idx n) (ρ : Block n) : Idx n × Idx n :=
  colEnds v ρ.2.1.val ρ.1

/-- The eligible rows `W_ρ`: the rows of the block on which both endpoints are in `G_qry` (p.23). -/
def eligible {n : ℕ} (v : ℕ → Idx n → Idx n) (Gqry : Finset (Act n)) (ρ : Block n) :
    Finset (Idx n) :=
  Finset.univ.filter fun w =>
    ρ.2.1 ≤ w ∧ w ≤ ρ.2.2 ∧ ((blockEnds v ρ).1, w) ∈ Gqry ∧ ((blockEnds v ρ).2, w) ∈ Gqry

/-- The blocks requiring a BinS call: distinct endpoints and at least one eligible row (p.24; Algorithm 3,
line 10). -/
def callBlocks {n : ℕ} (v : ℕ → Idx n → Idx n) (Gqry : Finset (Act n)) : Finset (Block n) :=
  (blocks v).filter fun ρ => (eligible v Gqry ρ).Nonempty ∧ (blockEnds v ρ).1 ≠ (blockEnds v ρ).2

/-- The number of mapped-column changes `C`, (12), p.23. -/
def changeCount {n : ℕ} (v : ℕ → Idx n → Idx n) : ℕ :=
  ∑ j ∈ Finset.range (2 ^ n),
    (((Istar n).filter fun p => (v j p.1, v j p.2) ≠ (v (j + 1) p.1, v (j + 1) p.2)).card +
      (Finset.univ.filter fun i : Idx n => v j i ≠ v (j + 1) i).card)

/-- The block mass `P(X ∈ R_ρ)`, with `R_ρ` as in (13), p.24, with sorted endpoints (p.24). -/
noncomputable def blockMass {n : ℕ} (L : Measure (ℝ × ℝ)) (v : ℕ → Idx n → Idx n)
    (Gqry : Finset (Act n)) (ρ : Block n) : ℝ :=
  if h : (eligible v Gqry ρ).Nonempty then
    (L (region (Kof n) (min (blockEnds v ρ).1 (blockEnds v ρ).2)
      (max (blockEnds v ρ).1 (blockEnds v ρ).2)
      ((eligible v Gqry ρ).min' h) ((eligible v Gqry ρ).max' h))).toReal
  else
    0

/-- The cumulative probability mass `V`, over the blocks requiring a BinS call (p.24). -/
noncomputable def massV {n : ℕ} (L : Measure (ℝ × ℝ)) (v : ℕ → Idx n → Idx n)
    (Gqry : Finset (Act n)) : ℝ :=
  ∑ ρ ∈ callBlocks v Gqry, blockMass L v Gqry ρ

/-- One pass of Algorithm 3, lines 9–13: BinS on sorted endpoints, with the sign restored. -/
noncomputable def blockStep {n : ℕ} (v : ℕ → Idx n → Idx n) (Gqry : Finset (Act n)) (β δ₀ : ℝ)
    (tbl : Table n) (ρ : Block n) : QTree (Act n) (Table n) :=
  if (eligible v Gqry ρ).Nonempty ∧ (blockEnds v ρ).1 ≠ (blockEnds v ρ).2 then
    qBind (binS (min (blockEnds v ρ).1 (blockEnds v ρ).2) (max (blockEnds v ρ).1 (blockEnds v ρ).2)
        β δ₀ (eligible v Gqry ρ)) fun est =>
      .done fun c w =>
        if c = ρ.1 ∧ w ∈ eligible v Gqry ρ then
          (if (blockEnds v ρ).1 < (blockEnds v ρ).2 then est w else - est w)
        else
          tbl c w
  else
    .done tbl

/-- BinS on each fixed-endpoint block (Algorithm 3, lines 8–14; Theorem 6.2, p.24). -/
noncomputable def runBlocks {n : ℕ} (v : ℕ → Idx n → Idx n) (Gqry : Finset (Act n)) (β δ₀ : ℝ) :
    QTree (Act n) (Table n) :=
  (blocks v).toList.foldlM (blockStep v Gqry β δ₀) (fun _ _ => 0)

/-- The estimate of `F(x_{b,j}) − F(x_{a,j})`, `a < b`, reconstructed by the mapped decomposition (19), p.29. -/
noncomputable def chainEst {n : ℕ} (tbl : Table n) (j a b : Idx n) : ℝ :=
  tbl (.inr b) j + ((B n b a).map fun p => tbl (.inl p) j).sum - tbl (.inr a) j

/-- The estimate `D̂_j(a, b)` of `D_j(a, b) = F(x_{a,j}) − F(x_{b,j})`, in any orientation (p.37). -/
noncomputable def Dhat {n : ℕ} (tbl : Table n) (j a b : Idx n) : ℝ :=
  if b < a then chainEst tbl j b a else if a < b then - chainEst tbl j a b else 0

end BilateralOptRegret


