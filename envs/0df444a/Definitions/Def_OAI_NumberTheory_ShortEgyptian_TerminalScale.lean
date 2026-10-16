-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
-- name    : OAI_NumberTheory_ShortEgyptian_TerminalScale
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:00:35.990267+00:00
-- url     : https://prove2.me/theorems/26535874-4648-44e1-abbe-ee5a9f1c2dd5
-- title:
--   Step count, length and constant for the terminal stage of the descent
-- statement:
--   This file defines the number of unit fractions spent in the last stage of a residue descent producing short Egyptian fraction expansions, as a function of the scale $S\in\mathbb{R}$. Here $\log$ is the natural logarithm and $\lceil\cdot\rceil_+$ is the ceiling truncated at $0$.
--
--   1. **Terminal steps.**
--
--      $$k(S)=\Big\lceil\frac{\log S}{\log(10000/9999)}\Big\rceil_+ ,$$
--
--      the least natural number $k$ with $\log S\le k\log(10000/9999)$; for $S>0$ this means $S\le(10000/9999)^k$.
--
--   2. **Terminal length.** $\ell(S)=\beta(S)+1+k(S)$, where $\beta(S)=\lceil 100000\log S/\log 2\rceil_+$ is the binary exponent.
--
--   3. **Terminal constant.**
--
--      $$c_{\mathrm{term}}=\frac{100000}{\log 2}+\frac{1}{\log(10000/9999)}+3 .$$
--
--   In the terminal stage a numerator $u\le e^{m(S)}$, where $m(S)=\lfloor S/\log S\rfloor_+$, is expanded over a modulus $M$ divisible by $2^{\beta(S)}$. As long as $u>2^{\beta(S)}$, one greedy step against a suitable divisor of $M$ replaces $u$ by a residue at most $u^{9999/10000}$, so that $\log u$ shrinks by the factor $9999/10000$; once $u\le 2^{\beta(S)}$, the fraction $u/M$ is finished by a binary expansion with at most $\beta(S)+1$ terms. Altogether $u/M$ becomes a sum of at most $\ell(S)$ unit fractions, and $\ell(S)\le c_{\mathrm{term}}\log S$ whenever $\log S\ge 1$.
--
--   **Formalization Note** The Lean names are `terminalSteps`, `terminalLength` and `terminalConstant`; the ceilings are `Nat.ceil` and $\log$ is `Real.log`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/TerminalScale.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/TerminalScale.lean by skeleton subtraction
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

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

noncomputable def terminalSteps (S : ℝ) : ℕ := ⌈Real.log S/Real.log (10000/9999:ℝ)⌉₊
noncomputable def terminalLength (S : ℝ) : ℕ := binaryExponent S+1+terminalSteps S
noncomputable def terminalConstant : ℝ := 100000/Real.log 2+1/Real.log (10000/9999:ℝ)+3

end ShortEgyptian

end OAI


