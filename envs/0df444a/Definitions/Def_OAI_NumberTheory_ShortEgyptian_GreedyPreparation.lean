-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation
-- name    : OAI_NumberTheory_ShortEgyptian_GreedyPreparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:12:07.484994+00:00
-- url     : https://prove2.me/theorems/975e6707-5a1a-4591-8f40-a4a47ee24d84
-- title:
--   Greedy preparation of a fraction to a denominator of prescribed size
-- statement:
--   Notation: $\log$ is the natural logarithm, $\lceil\cdot\rceil_+$ is the ceiling truncated at $0$, and $D_C=816824$.
--
--   1. **Prepared fractions.** For $a,b,k\in\mathbb{N}$ and $T\in\mathbb{R}$, the fraction $a/b$ is *$(T,k)$-prepared* if there are a list $n_1,\dots,n_r$ of natural numbers and natural numbers $A,C$ such that
--      - $n_i\ge 2$ for all $i$, and $r\le k$;
--      - $A\le a$ and $A<C$;
--      - in $\mathbb{Q}$, $$\frac ab=\sum_{i=1}^{r}\frac1{n_i}+\frac AC ;$$
--      - $A=0$, or $T\le C<T^2$.
--
--   2. **Number of greedy steps.** For $S\in\mathbb{R}$,
--
--      $$g(S)=\Big\lceil\frac{\log\big(D_CS/\log 2\big)}{\log 2}\Big\rceil_+ .$$
--
--   3. **Greedy constant.**
--
--      $$c_{\mathrm{gr}}=\frac{D_C}{(\log 2)^2}+\frac{1}{\log 2}+2 .$$
--
--   A prepared fraction is one from which at most $k$ unit fractions have been split off so that the remainder $A/C$ is either zero or has its denominator in the window $[T,T^2)$. The greedy (Fibonacci–Sylvester) step replaces $A/C$ by $\big(A\lceil C/A\rceil-C\big)/\big(C\lceil C/A\rceil\big)$ and at most squares the denominator, so it reaches such a window. With $T=e^{D_CS}$ and $b<T$, at most $g(S)+1$ steps are needed, because $2^{2^{g(S)}}\ge e^{D_CS}$ for $S>0$; and $g(S)+1\le c_{\mathrm{gr}}\log S$ whenever $S\ge1$ and $\log S\ge 1$.
--
--   **Formalization Note** The Lean names are `Prepared a b T k`, `greedySteps` and `greedyConstant`. The sum of reciprocals is `unitSum ns`, the fractions are rational numbers (with Lean's convention that division by zero gives $0$), and the window condition compares real casts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean by skeleton subtraction
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

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

def Prepared (a b : ℕ) (T : ℝ) (k : ℕ) : Prop :=
  ∃ ns : List ℕ, ∃ A C : ℕ, (∀ n ∈ ns, 2 ≤ n) ∧ ns.length ≤ k ∧
    A ≤ a ∧ A < C ∧ (a:ℚ)/b = unitSum ns+(A:ℚ)/C ∧
    (A=0 ∨ T ≤ (C:ℝ) ∧ (C:ℝ)<T^2)

noncomputable def greedySteps (S : ℝ) : ℕ :=
  ⌈Real.log ((dimC:ℝ)*S/Real.log 2)/Real.log 2⌉₊

noncomputable def greedyConstant : ℝ := (dimC:ℝ)/(Real.log 2)^2+1/Real.log 2+2

end ShortEgyptian

end OAI


