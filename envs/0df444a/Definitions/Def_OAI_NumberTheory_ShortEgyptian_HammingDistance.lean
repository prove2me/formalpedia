-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
-- name    : OAI_NumberTheory_ShortEgyptian_HammingDistance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:37:32.162095+00:00
-- url     : https://prove2.me/theorems/f0c15897-54a9-48b6-89d0-8694b4de175c
-- title:
--   Hamming distance between two Boolean labellings of a finite set
-- statement:
--   Let $J$ be a finite set and let $I,K:J\to\{0,1\}$ be two labellings of $J$ by bits, that is, two points of the cube $\{0,1\}^J$. Their Hamming distance is the number of coordinates at which they differ:
--
--   $$d(I,K)=\#\{\,j\in J:\ I(j)\ne K(j)\,\}.$$
--
--   In the argument, each $I\in\{0,1\}^J$ selects one of two random primes in every coordinate, producing $2^{|J|}$ products, and mean-square bounds for averages over $I$ are obtained by splitting the pairs $(I,K)$ according to their distance. In the surrounding development it is shown, for instance, that if $A$ is a finite nonempty set, $\mathbb{E}$ denotes uniform averages, $F:\{0,1\}^J\times A\to\mathbb{C}$ satisfies $|F|\le 1$, $k\in\mathbb{N}$, $\varepsilon\ge 0$, and $\bigl|\mathbb{E}_{a}F(I,a)\overline{F(K,a)}\bigr|\le\varepsilon$ whenever $d(I,K)\ge k$, then
--
--   $$\mathbb{E}_{a\in A}\Bigl|\mathbb{E}_{I\in\{0,1\}^J}F(I,a)\Bigr|^2\le 2^k\Bigl(\frac34\Bigr)^{|J|}+\varepsilon.$$
--
--   **Formalization Note** The Lean name is `hammingDistance`; bits are Lean's `Bool`, and the distance is the cardinality of a filtered `Finset.univ`, computed with classical decidability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/HammingDistance.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/HammingDistance.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def hammingDistance {J : Type uJ} [Fintype J] (I K : J → Bool) : ℕ :=
  (univ.filter (fun j => I j ≠ K j)).card

end ShortEgyptian

end OAI


