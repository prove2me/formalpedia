-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison
-- name    : OAI_InformationTheory_BooleanNoise_Comparison
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:51:57.640306+00:00
-- url     : https://prove2.me/theorems/cacde2e5-ac6f-47f9-aeea-22694d2719ab
-- title:
--   The comparison kernel $1/(s^2\operatorname{artanh}s)$ and related functions
-- statement:
--   Let $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$ and $h(v)=\log2-\psi(v)$. The file defines the following functions.
--
--   1. **Kernel and its integral.**
--   $$
--   k(s)=\frac{1}{s^2\operatorname{artanh}s},\qquad V(u)=2u\operatorname{artanh}(u)\int_u^1k(s)\,ds,\qquad V_{\mathrm{time}}(t)=V(e^{-t}).
--   $$
--   With Lean's conventions, $k(1)=0$.
--   2. **Rational approximation gap.** $\frac{u}{1-u^2/2}-\operatorname{artanh}u$.
--   3. **Model kernel and primitive.** $\frac{1-s^2/2}{s^3}$, with primitive $-\frac{1}{2s^2}-\frac{\log s}{2}$.
--   4. **Bias.** $m^2\log2-\psi(m)$.
--   5. **Lower comparison function.** $A\,h(e^{-t})+B\,V_{\mathrm{time}}(t)$ for constants $A,B$.
--
--   These functions compare the information deficit along the noise semigroup ($u=e^{-t}$) with explicit lower bounds. The model kernel approximates $k$ for small $s$ and has an explicit primitive.
--
--   **Formalization Note** The integral is the interval integral $\int_u^1$. Lean's conventions $\operatorname{artanh}1=0$ and $x/0=0$ apply.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Comparison.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Comparison.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality

namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def comparisonKernel (s : ℝ) : ℝ := 1 / (s ^ 2 * Real.artanh s)

def comparisonV (u : ℝ) : ℝ :=
  2 * u * Real.artanh u * ∫ s in u..1, comparisonKernel s

def comparisonVTime (t : ℝ) : ℝ := comparisonV (Real.exp (-t))

@[simp] theorem comparisonKernel_one : comparisonKernel 1 = 0 := by
  norm_num [comparisonKernel, Real.artanh]

def rationalArtanhGap (u : ℝ) : ℝ := u / (1 - u ^ 2 / 2) - Real.artanh u

def comparisonModelKernel (s : ℝ) : ℝ := (1 - s ^ 2 / 2) / s ^ 3

def comparisonPrimitive (s : ℝ) : ℝ := -(1 / (2 * s ^ 2)) - Real.log s / 2

def comparisonBias (m : ℝ) : ℝ := m ^ 2 * ell - psi m

def comparisonLower (A B t : ℝ) : ℝ :=
  A * entropy (Real.exp (-t)) + B * comparisonVTime t

end LeanBlast.CourtadeKumar

end

end OAI


