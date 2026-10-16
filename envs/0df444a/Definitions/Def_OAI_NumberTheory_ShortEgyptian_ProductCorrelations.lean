-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
-- name    : OAI_NumberTheory_ShortEgyptian_ProductCorrelations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:42:28.670221+00:00
-- url     : https://prove2.me/theorems/9da40cc1-d887-4fe6-8101-427b7024a01e
-- title:
--   Products of primes selected from a doubled random sample
-- statement:
--   Let $J$ be a finite set, $A$ a set, $p:A\to\mathbb{N}$ a labelling of $A$ by natural numbers (in applications, by distinct primes), $I:J\to\{0,1\}$ a selection, and $f:J\times\{0,1\}\to A$ a doubled sample, which assigns two elements $f(j,0)$ and $f(j,1)$ of $A$ to each coordinate $j\in J$. The file defines the selected product
--
--   $$\Pi_I(f)=\prod_{j\in J}p\bigl(f(j,I(j))\bigr)\in\mathbb{N}.$$
--
--   For a fixed doubled sample $f$, the $2^{|J|}$ selections $I$ produce $2^{|J|}$ products of $|J|$ labels each, all dividing the common multiple $\prod_{j\in J}p(f(j,0))\,p(f(j,1))$. With primes as labels, these products supply the family of divisors of a common denominator on which the residue-descent construction of short expansions draws. When $f$ is chosen uniformly at random, the averages $\mathbb{E}_{I}\,\psi_u\bigl(l\,\Pi_I(f)\bigr)$ over all selections, with $\psi_u(x)=\exp(2\pi i x/u)$, are shown in the surrounding development to have small mean square for suitable moduli $u$ and frequencies $l$, so that for most samples the products are well distributed modulo $u$.
--
--   **Formalization Note** The Lean name is `sampleProduct p I f`; bits are Lean's `Bool`, with 0 and 1 corresponding to `false` and `true`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ProductCorrelations.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ProductCorrelations.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def sampleProduct {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (I : J → Bool) (f : (J × Bool) → A) : ℕ := ∏ j, p (f (j,I j))

end ShortEgyptian

end OAI


