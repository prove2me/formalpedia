-- Prove2me | Definitions.Def_ChapterFreeFieldBornHomeo
-- name    : ChapterFreeFieldBornHomeo
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T08:46:06.864987+00:00
-- url     : https://prove2.me/theorems/d58e2b70-6d31-4994-9a8a-3ea68c47dfca
-- title:
--   ChapterFreeFieldBornHomeo

import Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_bornSection_bornMap

import Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_bornSection_nonneg

import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornMap_bornSection

import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_mem_sphere

import Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_mem_stdSimplex

import Theorems.Thm_BookProof_ChapterFreeFieldBornCont_continuous_bornMap


import Definitions.Def_ChapterFreeFieldBornSectionBij
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the Born parametrization restricts to a *homeomorphism* on the nonnegative orthant

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the Introduction's statement (`book.tex` ~line 805) that *"the
wave-function is nothing else than one possible parametrization of any
probability distribution; the parametrization is a surjective map from an
hypersphere to the set of all possible probability distributions"*, together
with the free-field construction of §5 (`book.tex` ~line 1706).

Previous waves on this thread built the Born map `x ↦ (x_k)²`, showed it is a
*continuous* surjection of the unit sphere onto the probability simplex
(`ChapterFreeFieldBornCont`), and — after quotienting out the `{±1}ⁿ` sign gauge
— proved that on the **nonnegative orthant** of the sphere it is a *bijection*
onto the simplex (`ChapterFreeFieldBornSectionBij`).  This wave upgrades that
set-theoretic bijection to a genuine **homeomorphism**: the nonnegative part of
the unit sphere and the probability simplex are *topologically the same space*.

The proof is the standard "continuous bijection from a compact space to a
Hausdorff space is a homeomorphism" argument
(`Continuous.homeoOfEquivCompactToT2`): the domain
`sphere 0 1 ∩ nonnegOrthant n` is a closed subset of the compact sphere, hence
compact, and the simplex is Hausdorff as a subspace of `Fin n → ℝ`.

## Main results

* `isClosed_nonnegOrthant` — the nonnegative orthant is closed.
* `isCompact_sphere_inter_nonnegOrthant` — the nonnegative part of the unit
  sphere is compact.
* `bornEquiv` — the `Equiv` between the nonnegative part of the sphere and the
  simplex packaging Wave 147's `bornMap_bijOn_nonneg_sphere`.
* **headline** `bornHomeo` — the Born map is a homeomorphism
  `↥(sphere 0 1 ∩ nonnegOrthant n) ≃ₜ ↥(stdSimplex ℝ (Fin n))`.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornSectionBij

namespace BookProof.ChapterFreeFieldBornHomeo

variable {n : ℕ}

/-- The nonnegative orthant is a closed set (an intersection of the closed
half-spaces `{x | 0 ≤ x k}`). -/
theorem isClosed_nonnegOrthant : IsClosed (nonnegOrthant n) := by
  unfold nonnegOrthant
  rw [Set.setOf_forall]
  exact isClosed_iInter (fun k => isClosed_le continuous_const (by fun_prop))

/-- The nonnegative part of the unit sphere is compact: a closed subset of the
compact sphere. -/
theorem isCompact_sphere_inter_nonnegOrthant :
    IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n) :=
  (isCompact_sphere _ _).inter_right isClosed_nonnegOrthant

/-- The set-theoretic **bijection** of Wave 147 packaged as an `Equiv` between the
nonnegative part of the unit sphere and the probability simplex.  Forward is the
Born map `x ↦ (x_k)²`; backward is the square-root section `p ↦ (√ p_k)`. -/
noncomputable def bornEquiv (n : ℕ) :
    ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n) ≃
      ↥(stdSimplex ℝ (Fin n)) where
  toFun x := ⟨bornMap x, bornMap_mem_stdSimplex x.2.1⟩
  invFun p := ⟨bornSection p, bornSection_mem_sphere p.2, bornSection_nonneg p⟩
  left_inv x := Subtype.ext (bornSection_bornMap x.2.2)
  right_inv p := Subtype.ext (bornMap_bornSection p.2)

@[simp] theorem bornEquiv_apply_coe
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n)) :
    (bornEquiv n x : Fin n → ℝ) = bornMap x := rfl

/-- The `Equiv` `bornEquiv` is continuous (its forward map is the Born map,
restricted to the subtype). -/
theorem continuous_bornEquiv : Continuous (bornEquiv n) := by
  apply Continuous.subtype_mk
  exact continuous_bornMap.comp continuous_subtype_val

/-- **Headline.** The Born map is a *homeomorphism* from the nonnegative part of
the unit sphere onto the probability simplex.  Since it is a continuous bijection
(Wave 147) from a compact space (`isCompact_sphere_inter_nonnegOrthant`) to a
Hausdorff space (the simplex, a subspace of `Fin n → ℝ`), it is automatically a
homeomorphism: the nonnegative part of the hypersphere and the space of all
probability distributions are topologically identical. -/
noncomputable def bornHomeo (n : ℕ) :
    ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n) ≃ₜ
      ↥(stdSimplex ℝ (Fin n)) :=
  haveI : CompactSpace
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n) :=
    isCompact_iff_compactSpace.mp isCompact_sphere_inter_nonnegOrthant
  Continuous.homeoOfEquivCompactToT2 (f := bornEquiv n) continuous_bornEquiv

@[simp] theorem bornHomeo_apply_coe
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ nonnegOrthant n)) :
    (bornHomeo n x : Fin n → ℝ) = bornMap x := rfl

end BookProof.ChapterFreeFieldBornHomeo


