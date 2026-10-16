-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
-- name    : OAI_NumberTheory_ShortEgyptian_MomentRecurrence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:05:31.375686+00:00
-- url     : https://prove2.me/theorems/088a068f-158a-4d1f-858e-f75e794ed9ee
-- title:
--   Divisor-moment hypothesis, descent exponents and densities of bad numerators
-- statement:
--   Notation: $\log$ is the natural logarithm, $\lfloor\cdot\rfloor_+$ and $\lceil\cdot\rceil_+$ are floor and ceiling truncated at $0$, $D_M=204204$, $D_X=204206$, $D_C=816824$, $m(S)=\lfloor S/\log S\rfloor_+$ and $X_j(S)=\exp\big(D_XS-m(S)j/10000\big)$. For $X\in\mathbb{R}$ and $n\in\mathbb{N}$ let
--
--   $$\tau_X(n)=\#\{d\in\mathbb{N}:\ d\mid n,\ d\le X\}$$
--
--   be the number of divisors of $n$ not exceeding $X$.
--
--   1. **Moment dimension.** $D_{\mathrm{mom}}=2D_C+D_M+1=1837853$.
--
--   2. **Moment exponent.** $R=49009440000$, which equals $24\cdot D_X\cdot 10000$.
--
--   3. **Descent exponent.** $\alpha=1-1/R$.
--
--   4. **Moment hypothesis at scale $S$.** $\mathrm{Mom}(S)$ holds if for all real $v,Y$ and all $N\in\mathbb{N}$ with
--
--      $$\frac{S}{2\log S}\le v\le D_{\mathrm{mom}}S,\qquad e^{v/2}\le Y\le e^{v},\qquad N\le e^{D_{\mathrm{mom}}S},$$
--
--      one has
--
--      $$\sum_{N<n\le N+\lfloor Y\rfloor_+}\tau_{e^{v}}(n)^{R}\ \le\ Y\exp\big(S^{1/4}\big).$$
--
--   5. **Level density.** For $M,C,j\in\mathbb{N}$,
--
--      $$\delta_j(S,M,C)=\frac{\big|\mathcal B_j\big(S,M,C,\ell(S)\big)\big|}{X_j(S)} .$$
--
--      Here $\ell(S)=\lceil 100000\log S/\log 2\rceil_+ +1+\lceil \log S/\log(10000/9999)\rceil_+$ is the terminal length, and $\mathcal B_j(S,M,C,K)$ is the set of integers $u$ with $1\le u\le\lfloor X_j(S)\rfloor_+$ for which $u/(M L_j)$ is not a sum of at most $K+\max\{J(S)-j,0\}$ unit fractions with denominators at least $2$; $L_j$ equals $C$ if $e^S<X_j(S)$ and $1$ otherwise, and $J(S)=\lceil (D_XS-m(S))/(m(S)/10000)\rceil_+$ is the depth.
--
--   The hypothesis $\mathrm{Mom}(S)$ is a uniform bound for very high moments of truncated divisor counts in short intervals, and it holds for all sufficiently large $S$. Combined with Hölder's inequality with exponents $R$ and $R/(R-1)$, it yields a recurrence of the form $\delta_j\le e^{-m/1000}+\rho\,\delta_{j+1}+2e^{S^{1/4}/R}\,\delta_{j+1}^{\alpha}$ for $j<J(S)$, with $\rho=e^{-m/10000}$; unrolled from the last level, where the density vanishes, it shows that the density $\delta_0$ at the top level is small.
--
--   **Formalization Note** The Lean names are `momentDimension` and `descentR` (irreducible natural-number constants), `descentAlpha`, `MomentScale S` and `levelDensity S M C j`; $\tau_X(n)$ is `truncatedDivisorCount X n`, $S^{1/4}$ is the real power `Real.rpow`, and the bad sets are `levelBad`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/MomentRecurrence.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/MomentRecurrence.lean by skeleton subtraction
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

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter

@[irreducible] def momentDimension : ℕ := 2*dimC+dimM+1
@[irreducible] def descentR : ℕ := 49009440000
noncomputable def descentAlpha : ℝ := 1-1/(descentR:ℝ)

def MomentScale (S : ℝ) : Prop := ∀ (v Y : ℝ) (N : ℕ),
  S/(2*Real.log S) ≤ v → v ≤ (momentDimension:ℝ)*S →
  Real.exp (v/2) ≤ Y → Y ≤ Real.exp v → (N:ℝ) ≤ Real.exp ((momentDimension:ℝ)*S) →
  ∑ n ∈ Ioc N (N+⌊Y⌋₊), (truncatedDivisorCount (Real.exp v) n:ℝ)^descentR ≤ Y*Real.exp (S^(1/4:ℝ))

noncomputable def levelDensity (S : ℝ) (M C j : ℕ) : ℝ :=
  (levelBad S M C (terminalLength S) j).card/level S j

end ShortEgyptian

end OAI


