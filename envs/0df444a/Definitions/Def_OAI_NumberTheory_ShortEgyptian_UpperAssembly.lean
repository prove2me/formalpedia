-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_UpperAssembly
-- name    : OAI_NumberTheory_ShortEgyptian_UpperAssembly
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:13:09.517442+00:00
-- url     : https://prove2.me/theorems/7f0d5af3-f35f-485d-a122-09a6c61165cd
-- title:
--   The constant in the $O(\log\log b)$ upper bound for Egyptian fraction length
-- statement:
--   Let $\log$ be the natural logarithm and put $D_X=204206$ and $D_C=4D_X=816824$. The *upper-bound constant* is the positive real number
--
--   $$c_{\mathrm{up}}=c_{\mathrm{gr}}+2\,c_{\mathrm{dens}},$$
--
--   where
--
--   $$c_{\mathrm{gr}}=\frac{D_C}{(\log 2)^2}+\frac{1}{\log 2}+2,\qquad c_{\mathrm{dens}}=\frac{100000}{\log 2}+\frac{1}{\log(10000/9999)}+3+3\cdot D_X\cdot 10000 .$$
--
--   For a fraction $a/b$ with $1\le a<b$ and $b=e^S$, at most $c_{\mathrm{gr}}\log S$ unit fractions are split off by greedy preparation, and at most $2c_{\mathrm{dens}}\log S$ more represent the remaining fraction, whose numerator is split into two good numerators over a common modulus. Hence, for all sufficiently large $b$ and all $1\le a<b$, the fraction $a/b$ has an Egyptian fraction expansion (distinct denominators, all at least $2$) with at most $c_{\mathrm{up}}\log\log b$ terms; $c_{\mathrm{up}}$ is the constant $c_2$ of the upper half of the main theorem.
--
--   **Formalization Note** The constant is `upperConstant`, defined as `greedyConstant + 2 * densityConstant`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/UpperAssembly.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/UpperAssembly.lean by skeleton subtraction
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

noncomputable def upperConstant : ℝ := greedyConstant+2*densityConstant

end ShortEgyptian

end OAI


