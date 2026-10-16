-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
-- name    : OAI_NumberTheory_ShortEgyptian_ScaleBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:55:57.339603+00:00
-- url     : https://prove2.me/theorems/8a73d03f-ee0a-4d12-a37c-f475f79367e9
-- title:
--   Admissible large scales for the list construction
-- statement:
--   This file packages, as a single predicate on the scale parameter $S\in\mathbb{R}$, all the numerical largeness conditions that the construction of residue systems needs. Notation: $\log$ is the natural logarithm, $\lfloor\cdot\rfloor_+$ and $\lceil\cdot\rceil_+$ are floor and ceiling truncated at $0$, $m(S)=\lfloor S/\log S\rfloor_+$, $D_X=204206$, $D_C=4D_X=816824$, and
--
--   $$J(S)=\Big\lceil\frac{D_XS-m(S)}{m(S)/10000}\Big\rceil_+$$
--
--   is the depth of the level ladder $X_j(S)=\exp\big(D_XS-m(S)j/10000\big)$. For $r\in\mathbb{N}$ let
--
--   $$P(r)=2^r(2r+4),\qquad K(r)=\big(18\cdot3^{r+3}\big)^4\,\big((r+2)!\big)^2\,2^{2r}$$
--
--   be the exponent and the constant of an estimate, used elsewhere in the argument, for exponential sums $\sum_{n}e(Z/n)$ over intervals, where $e(x)=\exp(2\pi i x)$.
--
--   A real number $S$ is an *admissible list scale* if all of the following hold:
--
--   1. $S\ge 2$;
--   2. $\log S\ge 100$;
--   3. $100001\,\log S\le S$;
--   4. $10^6\log S\le m(S)$;
--   5. $P(3D_C)\le\log S$;
--   6. $K(3D_C)\cdot 32^{P(3D_C)}\le e^{S/4}$;
--   7. $J(S)\,e^{-m(S)/250}<\tfrac12$.
--
--   Each condition holds for all sufficiently large $S$, so admissibility holds eventually as $S\to\infty$. Collecting the conditions in one predicate lets the subsequent lemmas use simple numerical consequences, such as $m(S)\ge 100$ or $\rho(S)=e^{-m(S)/10000}\le 1/256$, without repeating asymptotic arguments.
--
--   **Formalization Note** The predicate is the structure `ListScale S`, a proposition with one field per condition (`two_le`, `log_large`, `log_bound`, `m_large`, `reciprocal_power`, `reciprocal_const`, `depth_tail`); $P$ and $K$ are `reciprocalPower` and `reciprocalConstantNat`. The file also declares `scaleFinDecidableEq S`, a classical decidable-equality instance on `Fin (scaleM S)`; it is pure plumbing for forming finite sets of Boolean vectors of length $m(S)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ScaleBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ScaleBounds.lean by skeleton subtraction
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

namespace OAI

namespace ShortEgyptian

@[instance_reducible] noncomputable def scaleFinDecidableEq (S : ℝ) : DecidableEq (Fin (scaleM S)) := Classical.decEq _
attribute [local instance] scaleFinDecidableEq

open Filter Topology

structure ListScale (S : ℝ) : Prop where
  two_le : 2 ≤ S
  log_large : 100 ≤ Real.log S
  log_bound : 100001*Real.log S ≤ S
  m_large : 1000000*Real.log S ≤ (scaleM S:ℝ)
  reciprocal_power : (reciprocalPower (3*dimC):ℝ) ≤ Real.log S
  reciprocal_const : (reciprocalConstantNat (3*dimC):ℝ)*32^reciprocalPower (3*dimC) ≤ Real.exp (S/4)
  depth_tail : (depth S:ℝ)*Real.exp (-(1/250:ℝ)*scaleM S) < 1/2

end ShortEgyptian

end OAI


