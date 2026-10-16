-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
-- name    : OAI_NumberTheory_ShortEgyptian_DescentSets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:01:55.032296+00:00
-- url     : https://prove2.me/theorems/d8d3deae-dceb-4d1d-82a8-ee29edf0b900
-- title:
--   Short unit-fraction representations and the bad numerators at each level
-- statement:
--   A *unit-fraction representation* of a rational number $x$ is a finite list $n_1,\dots,n_r$ of natural numbers, each at least $2$, with $\frac1{n_1}+\cdots+\frac1{n_r}=x$ in $\mathbb{Q}$; repetitions are allowed and the order is irrelevant. Its length is $r$.
--
--   1. **Short representations.** For $M,Q,u,k\in\mathbb{N}$, the statement $\mathrm{Short}(M,Q,u,k)$ means
--
--      $$\frac{u}{MQ}\ \text{has a unit-fraction representation of length at most }k .$$
--
--   2. **Bad numerators at level $j$.** Let $S\in\mathbb{R}$ and $M,C,K,j\in\mathbb{N}$. Write $\log$ for the natural logarithm, $\lfloor\cdot\rfloor_+$ and $\lceil\cdot\rceil_+$ for floor and ceiling truncated at $0$, $D_X=204206$, $m(S)=\lfloor S/\log S\rfloor_+$, $X_j(S)=\exp\big(D_XS-m(S)j/10000\big)$ for the levels, $J(S)=\lceil (D_XS-m(S))/(m(S)/10000)\rceil_+$ for the depth, and $L_j(S,C)$ for the level multiplier, equal to $C$ if $e^S<X_j(S)$ and to $1$ otherwise. Then
--
--      $$\mathcal B_j(S,M,C,K)=\Big\{u\in\mathbb{N}:\ 1\le u\le\lfloor X_j(S)\rfloor_+\ \text{ and not }\ \mathrm{Short}\big(M,\,L_j(S,C),\,u,\,K+\max\{J(S)-j,0\}\big)\Big\}.$$
--
--   Thus $\mathcal B_j$ consists of the numerators $u$ up to the $j$-th level for which $u/(ML_j)$ cannot be written with at most $K$ unit fractions plus one further unit fraction for each remaining level. In the descent, $K$ is the terminal length: the bad set at the last level $J(S)$ is empty because of the terminal stage, and one greedy step against a good divisor moves a numerator from level $j$ to level $j+1$ at the cost of one unit fraction. Bounding the proportion of bad numerators level by level then shows that most numerators up to $X_0(S)=e^{D_XS}$ have short representations.
--
--   **Formalization Note** $\mathrm{Short}$ is `HasUnitSum M Q u k`, defined through `IsUnitSum x ns` (all entries at least $2$ and `unitSum ns = x`); the fraction $u/(MQ)$ is computed in $\mathbb{Q}$, so it equals $0$ when $MQ=0$ by Lean's convention. The bad set is `levelBad S M C K j`, a `Finset` obtained by filtering `Finset.Icc 1 (Nat.floor (level S j))`, and `depth S - j` is truncated natural subtraction, written $\max\{J(S)-j,0\}$ above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DescentSets.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DescentSets.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

def HasUnitSum (M Q u k : ℕ) : Prop :=
  ∃ ns, IsUnitSum ((u:ℚ)/(M*Q)) ns ∧ ns.length ≤ k

noncomputable def levelBad (S : ℝ) (M C K j : ℕ) : Finset ℕ :=
  (Icc 1 ⌊level S j⌋₊).filter fun u => ¬HasUnitSum M (levelMultiplier S C j) u (K+(depth S-j))

end ShortEgyptian

end OAI


