-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
-- name    : OAI_NumberTheory_ShortEgyptian_ListSelection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:45:18.367741+00:00
-- url     : https://prove2.me/theorems/9ec1e122-99f2-4b81-8ff4-e4c313aa59bc
-- title:
--   Phase averages of a scaled family and the Fourier-bad condition
-- statement:
--   Let $I$ be a finite index set with $|I|$ elements, $t=(t_i)_{i\in I}$ a family of natural numbers, $Q,u,l\in\mathbb{N}$ and $\delta\in\mathbb{R}$, and write $e(x)=\exp(2\pi i x)$.
--
--   1. **Phase average.**
--
--      $$\Phi_{t,Q,u}(l)=\frac{1}{|I|}\sum_{i\in I}e\Bigl(\frac{l\,Q\,t_i}{u}\Bigr).$$
--
--   2. **Fourier-bad families.** The family $t$ is Fourier-bad for $(Q,u)$ at level $\delta$ if some frequency in the range $1\le l\le\lfloor\delta^{-4}\rfloor$ has a large phase average:
--
--      $$\exists\, l\in\mathbb{N},\ 1\le l\le\bigl\lfloor\delta^{-4}\bigr\rfloor:\qquad\bigl|\Phi_{t,Q,u}(l)\bigr|>\delta^{3},$$
--
--      where $\lfloor\cdot\rfloor$ is the floor rounded to a natural number.
--
--   Since $e(lQt_i/u)$ depends only on $Qt_i$ modulo $u$, the phase average is the average of the additive character of $\mathbb{Z}/u\mathbb{Z}$ at frequency $l$ over the residues $Qt_i \bmod u$. Not being Fourier-bad is exactly the hypothesis of the residue-discrepancy step: in the surrounding development it is shown that if $Q\ge 1$, $u\ge 1$, all $t_i\ge 1$, $I$ is nonempty, $0<\delta\le 1/256$ and $t$ is not Fourier-bad for $(Q,u)$ at level $\delta$, then at least $\delta|I|/2$ indices $i$ satisfy $u\lceil Qt_i/u\rceil-Qt_i<\delta u$; that is, the greedy step for the fraction $u/(Qt_i)$ leaves a remainder numerator below $\delta u$. The construction therefore selects random lists $t$ for which few moduli $u$ are Fourier-bad.
--
--   **Formalization Note** The Lean names are `phaseAverage t Q u l` and the proposition `FourierBad t Q u δ`, whose frequency range is the integer interval from 1 to the natural floor of 1/δ^4. By Lean's conventions an empty index set gives average 0, $u=0$ makes every phase equal to 1, and $\delta=0$ makes the frequency range empty, so that no family is Fourier-bad at level 0.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uΩ uJ uA uE uD uU

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

noncomputable def phaseAverage {I : Type uI} [Fintype I]
    (t : I → ℕ) (Q u l : ℕ) : ℂ :=
  (∑ i, phase ((l:ℝ)*Q*t i/u))/(Fintype.card I:ℂ)

noncomputable def FourierBad {I : Type uI} [Fintype I]
    (t : I → ℕ) (Q u : ℕ) (δ : ℝ) : Prop :=
  ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage t Q u l‖

end ShortEgyptian

end OAI


