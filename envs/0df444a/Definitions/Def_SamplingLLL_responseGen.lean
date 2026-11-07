-- Prove2me | Definitions.Def_SamplingLLL_responseGen
-- name    : SamplingLLL_responseGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:33.858983+00:00
-- url     : https://prove2.me/theorems/fe243b96-6e3d-442b-867a-86b22f213257
-- title:
--   Generation measures of the aggregate response
-- statement:
--   The generation-$t$ input measures of a recursion from a type-$i$ root: generation $0$ is the declared source measure of type $i$, and generation $t+1$ of type $j$ is the image of generation $t$ under the direct-call responses.
--
--   **Formalization Note** All input spaces are embedded in one finite space, and a scalar task has a one-point source measure.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.7, p.24

import Mathlib

set_option autoImplicit false

namespace SamplingLLL

/-- The generation-`t` input measures of Lemma A.7, p.24: generation `0` is the declared source
measure of the root type `i`, and generation `t+1` of type `j` is the image of generation `t` under
the direct-call responses. All input spaces are embedded in one finite space `Ω` (a scalar task has
a one-point source measure).

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.7, p.24. -/
noncomputable def responseGen {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (σ : ι → Ω → ℝ) (Resp : ι → ι → Ω → Ω → ℝ) (i : ι) : ℕ → ι → Ω → ℝ
  | 0, j, y => if j = i then σ i y else 0
  | t + 1, j, y => ∑ k, ∑ x, responseGen σ Resp i t k x * Resp k j x y

end SamplingLLL


