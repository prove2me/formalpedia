-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
-- name    : OAI_NumberTheory_ShortEgyptian_LevelSelection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:47:02.130418+00:00
-- url     : https://prove2.me/theorems/cf958ff1-ca1a-47c2-be4f-3256c972acb0
-- title:
--   Scale intervals and Fourier-bad numerators at a level
-- statement:
--   This file introduces two finite sets of natural numbers used to select numerators at a given scale in an exponential-sum argument. Throughout, $\lfloor y\rfloor_+$ denotes the floor of a real number $y$ truncated at $0$ (so $\lfloor y\rfloor_+=0$ for $y<0$), and $e(x)=\exp(2\pi i x)$ for $x\in\mathbb{R}$.
--
--   1. **Scale interval.** For real numbers $X$ and $\delta$,
--
--      $$\mathcal I(X,\delta)=\{\,n\in\mathbb{N}:\ \lfloor X\delta\rfloor_+ +1\le n\le \lfloor X\rfloor_+\,\}.$$
--
--      When $X\ge 0$ and $\delta\ge 0$ this is the set of positive integers in the half-open interval $(X\delta,X]$.
--
--   2. **Bad numerators at a level.** Let $I$ be a finite index set, $t=(t_i)_{i\in I}$ a family of natural numbers, $Q\in\mathbb{N}$ and $X,\delta\in\mathbb{R}$. For $u,l\in\mathbb{N}$ consider the phase average
--
--      $$A_{t,Q}(u,l)=\frac{1}{|I|}\sum_{i\in I} e\Big(\frac{l\,Q\,t_i}{u}\Big),$$
--
--      and call $u$ *Fourier-bad* (for $t,Q,\delta$) if there is an integer $l$ with $1\le l\le\lfloor\delta^{-4}\rfloor_+$ and $|A_{t,Q}(u,l)|>\delta^3$. The bad set at scale $X$ is
--
--      $$\mathcal B(t,Q,X,\delta)=\{\,u\in\mathcal I(X,\delta):\ u\text{ is Fourier-bad for }t,Q,\delta\,\}.$$
--
--   The averages $A_{t,Q}(u,l)$ are the Fourier coefficients, at the low frequencies $l$, of the empirical distribution of the residues $Qt_i \bmod u$. If $I$ is nonempty, $Q$, $u$ and all $t_i$ are positive, $0<\delta\le 1/256$, and $u$ is not Fourier-bad, a discrepancy argument shows that at least a proportion $\delta/2$ of the indices $i$ have $-Qt_i \bmod u$ smaller than $\delta u$; this is what allows a greedy step against the divisor $t_i$ to shrink the numerator $u$. The set $\mathcal B$ collects the exceptional numerators in the window $(X\delta,X]$, and the construction of residue systems chooses the family $t$ (at random, or deterministically from distinct primes) so that $|\mathcal B|$ is a tiny fraction of $X$ at every level of the descent.
--
--   **Formalization Note** The definitions are `scaleInterval X δ` (a `Finset` given by `Finset.Icc`) and `badLevel t Q X δ`, which filters it by `FourierBad t Q u δ`; the average $A_{t,Q}(u,l)$ is `phaseAverage t Q u l` from an earlier module. The fraction $lQt_i/u$ is computed in the reals, and the average divides by the cardinality of $I$, so Lean's convention that division by zero gives $0$ applies when $u=0$ or $I$ is empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/LevelSelection.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/LevelSelection.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uΩ uJ uA uD

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

noncomputable def scaleInterval (X δ : ℝ) : Finset ℕ := Icc (⌊X*δ⌋₊+1) ⌊X⌋₊

noncomputable def badLevel {I : Type uI} [Fintype I] (t : I → ℕ) (Q : ℕ) (X δ : ℝ) : Finset ℕ :=
  (scaleInterval X δ).filter (fun u => FourierBad t Q u δ)

end ShortEgyptian

end OAI


