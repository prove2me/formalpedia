-- Prove2me | Definitions.Def_ChapterFreeFieldBornQuotient
-- name    : ChapterFreeFieldBornQuotient
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T08:45:42.183072+00:00
-- url     : https://prove2.me/theorems/e5ba9484-82eb-4b64-a71f-31294e695250
-- title:
--   ChapterFreeFieldBornQuotient

import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_mem_stdSimplex

import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the Born parametrization of the *whole* sphere is a topological quotient map

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the Introduction's statement (`book.tex` ~line 805) that *"the
wave-function is nothing else than one possible parametrization of any
probability distribution; the parametrization is a surjective map from an
hypersphere to the set of all possible probability distributions"*, together
with the free-field construction of §5 (`book.tex` ~line 1706).

Previous waves on this thread built the Born map `x ↦ (x_k)²`, showed it is a
*continuous surjection* of the unit sphere onto the probability simplex
(`ChapterFreeFieldBornCont`, `ChapterFreeFieldBornSurj`), and — after
quotienting out the `{±1}ⁿ` sign gauge — proved that on the **nonnegative
orthant** of the sphere it is a *homeomorphism* onto the simplex
(`ChapterFreeFieldBornHomeo`).

This wave records the topological status of the parametrization on the *whole*
sphere: the Born map, as a map from the unit sphere onto the probability
simplex, is a **topological quotient map**.  Concretely the simplex carries
exactly the quotient topology induced by the Born map: it is the sphere with the
sign gauge collapsed.  The proof is the standard "continuous surjection from a
compact space to a Hausdorff space is a closed map, hence a quotient map"
argument (`Continuous.isClosedMap`, `IsClosedMap.isQuotientMap`).

## Main results

* `bornMapSphere` — the Born map as a map of subtypes `↥(sphere 0 1) →
  ↥(stdSimplex ℝ (Fin n))`.
* `continuous_bornMapSphere`, `surjective_bornMapSphere`.
* **headline** `isQuotientMap_bornMapSphere` — `bornMapSphere` is a quotient map.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont

namespace BookProof.ChapterFreeFieldBornQuotient

variable {n : ℕ}

/-- The Born map packaged as a map of subtypes: the unit sphere onto the
probability simplex, `x ↦ (x_k)²`. -/
noncomputable def bornMapSphere (n : ℕ) :
    ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) → ↥(stdSimplex ℝ (Fin n)) :=
  fun x => ⟨bornMap x, bornMap_mem_stdSimplex x.2⟩

@[simp] theorem bornMapSphere_coe
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    (bornMapSphere n x : Fin n → ℝ) = bornMap x := rfl







end BookProof.ChapterFreeFieldBornQuotient


