-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
-- name    : OAI_Probability_ThorpCompatibility_ClumpCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:25:50.288984+00:00
-- url     : https://prove2.me/theorems/4add8faf-ca6f-4339-a0f8-9674b42a9f75
-- title:
--   Rows through a cell, clump count, entry clump size and the exposure error
-- statement:
--   Let $I$ and $J$ be finite sets and let $r=(r_i)_{i\in I}$ be a family of permutations of $J$ (the rows). A cell is a pair $(j,k)\in J\times J$.
--
--   1. *Rows through a cell.* $\mathrm{cell}_r(j,k)=\{i\in I: r_i(j)=k\}$, the set of rows whose permutation sends $j$ to $k$.
--   2. *Clump count.* For a real threshold $H$,
--   $$
--   \mathrm{clump}_H(r)=\sum_{(j,k)\in J\times J}\big|\mathrm{cell}_r(j,k)\big|\;\mathbf 1\big[\,|\mathrm{cell}_r(j,k)|>H\,\big],
--   $$
--   the total number of row incidences that lie in cells met by more than $H$ rows.
--   3. *Clump size of an entry.* On the grid $\mathcal G_{A,D}$ (with $I=[A]$ and $J=[D]$), take a column $k\in[D]$, a row $i\in[A]$ and $a=(r,c)$, and let $j=r_i^{-1}(k)$ be the slot that row $i$ sends to column $k$. The clump size of the entry is
--   $$
--   \mathrm{cs}_{k,i}(a)=\big|\mathrm{cell}_r\big(r_i^{-1}(k),\,k\big)\big|,
--   $$
--   the number of rows $h$ with $r_h(j)=k$.
--   4. *Exposure error.* For $A,D\in\mathbb{N}$, $H,K\in\mathbb{R}$ and $i\in[A]$,
--   $$
--   \mathrm{err}_{A,D}(H,K;i)=\frac{1+\log D}{D}+\frac{2KH}{A-i}\,(1+\log D).
--   $$
--
--   In the entropy estimate for the grid, these quantities split the entries into good and bad ones. Consider an entry $c_k(i)$ whose value is light at level $H$, whose light values carry at least half of the predicted mass, and whose clump size is at most $K$. Its column cost, which bounds the entropy saved at that entry from below, is at least $1-\mathrm{err}_{A,D}(H,K;i)$ on average over a uniformly random column order. Entries in clumps larger than $K$ are charged instead to the clump count, because summing the indicators $\mathbf 1[\mathrm{cs}_{k,i}(a)>K]$ over all $k$ and $i$ gives exactly $\mathrm{clump}_K(r)$. The exponential moment of the clump count under uniformly random rows is controlled separately.
--
--   **Formalization Note** The definitions are `cellRows`, `clumpCount`, `entryClumpSize` and `exposureError`. `clumpCount` is a natural number, and the comparison of a cardinality with $H$ is made in $\mathbb{R}$. In `exposureError`, $A-i$ is a natural-number subtraction cast to $\mathbb{R}$, which equals $A-i\ge 1$ because $i<A$. For $D=0$ the conventions $\log 0=0$ and $x/0=0$ would apply, but the estimates use $D\ge 2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ClumpCost.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ClumpCost.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
noncomputable def cellRows {α β : Type*} [Fintype α]
    (r : α → Equiv.Perm β) (b : β × β) : Finset α :=
  Finset.univ.filter (fun i => r i b.1 = b.2)

noncomputable def clumpCount {α β : Type*} [Fintype α] [Fintype β]
    (H : ℝ) (r : α → Equiv.Perm β) : ℕ :=
  ∑ b : β × β, if H < (cellRows r b).card then (cellRows r b).card else 0

noncomputable def entryClumpSize {A D : ℕ} (k : Fin D) (i : Fin A) (a : Grid A D) : ℕ :=
  (cellRows a.1 ((a.1 i).symm k, k)).card

noncomputable def exposureError (A D : ℕ) (H K : ℝ) (i : Fin A) : ℝ :=
  (1 + Real.log (D : ℝ)) / D +
    (2 * K * H / ((A - (i : ℕ) : ℕ) : ℝ)) * (1 + Real.log (D : ℝ))

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI


