-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment
-- name    : OAI_Probability_ThorpShuffle_FirstMoment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:09:06.287902+00:00
-- url     : https://prove2.me/theorems/631474f9-0090-4f91-a500-b94a11456db6
-- title:
--   Defect slices of the reciprocal Specht-degree sum
-- statement:
--   This module groups the reciprocal Specht degrees of the partitions of $n$ according to their defect.
--
--   Fix $n\in\mathbb{N}$. For a partition $p$ of $n$ (written $p\vdash n$), let $D_p$ be its Young diagram, $\lambda_1(p)$ its largest part (the length of the first row) and $\ell(p)$ its number of parts (the length of the first column). Let $\deg(p)$ be the dimension of the Specht module of shape $p$, i.e. of the complex span of the $S_n$-translates of the polytabloid of a fixed bijection $\{0,\dots,n-1\}\to D_p$; it is a positive integer. The defect of $p$ is
--   $$
--   \operatorname{defect}(p)=n-\max\big(\lambda_1(p),\ell(p)\big);
--   $$
--   for $n\ge 1$ it vanishes exactly for the one-row partition $(n)$ and the one-column partition $(1,\dots,1)$.
--
--   1. *Reciprocal degree.* $\mathrm{inv}(p)=1/\deg(p)\in\mathbb{R}$.
--   2. *Slice of defect $u$.* For $u\in\mathbb{N}$,
--   $$
--   \mathrm{slice}(n,u)=\sum_{p\vdash n:\ \operatorname{defect}(p)=u}\frac{1}{\deg(p)} .
--   $$
--   3. *Small slice.*
--   $$
--   \mathrm{smallSlice}(n,u)=\begin{cases}\mathrm{slice}(n,u),&0<u\ \text{and}\ 4u\le n,\\ 0,&\text{otherwise.}\end{cases}
--   $$
--
--   The quantities controlled in this project are the reciprocal-degree sum $\sum_{p\vdash n}1/\deg(p)$ and its exceptional part $\sum_{p\vdash n,\ \operatorname{defect}(p)>0}1/\deg(p)$. The exceptional part equals $\sum_{u}\mathrm{smallSlice}(n,u)$ plus the sum of $1/\deg(p)$ over the partitions with $4\operatorname{defect}(p)>n$. The slices allow each fixed defect to be estimated separately, which is how the exceptional part is shown to tend to $0$ as $n\to\infty$.
--
--   **Formalization Note** The definitions are `inverseFirst`, `slice` and `smallSlice` in `Thorp.Current`. Partitions of $n$ are `NShape n`, i.e. `Nat.Partition (Fintype.card (Fin n))`, and `defect p = n - longest (ofPartition p)` uses truncated subtraction; no truncation occurs because the longer of the first row and the first column has at most $n$ cells. The reciprocal is the real inverse `(degree p : ℝ)⁻¹`, which would be $0$ for a zero degree by Lean's convention, but Specht degrees are positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FirstMoment.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/FirstMoment.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Filter Topology

open Thorp.Specht Thorp.Young
variable {n : ℕ}

def inverseFirst (p : NShape n) : ℝ := (degree p : ℝ)⁻¹

def slice (n u : ℕ) : ℝ := ∑ p : {p : NShape n // defect p = u}, inverseFirst p.val

def smallSlice (n u : ℕ) : ℝ := if 0 < u ∧ 4 * u ≤ n then slice n u else 0

end Thorp.Current

namespace Thorp.Current
open scoped Classical
open Filter Topology Thorp.Young Thorp.Specht

end Thorp.Current

namespace Thorp.Current
open scoped Classical
open Thorp.Specht Filter Topology

end Thorp.Current

end

end OAI


