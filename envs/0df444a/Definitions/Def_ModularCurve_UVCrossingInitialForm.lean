-- Prove2me | Definitions.Def_ModularCurve_UVCrossingInitialForm
-- name    : ModularCurve_UVCrossingInitialForm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/ec620556-bece-584c-bc7f-2e4631fdf17b
-- title:
--   Unit parts, leading residues and initial forms of Laurent data
-- statement:
--   Over a commutative ring $W$, for elements $\varpi, c$ the declaration `unitPart ϖ c` selects a cofactor witnessing the divisibility $\varpi^{\,\mathrm{multiplicity}(\varpi,c)} \mid c$; `pow_multiplicity_mul_unitPart` records the defining identity $\varpi^{\,\mathrm{multiplicity}(\varpi, c)} \cdot \mathrm{unitPart}(\varpi,c) = c$. Under the standing assumptions that $W$ is a domain and a discrete valuation ring, `leadingResidue ϖ c` is the image of this cofactor in the residue field $\mathrm{ResidueField}\,W$, with the convention $\mathrm{leadingResidue}(\varpi,0)=0$; for $c \ne 0$ and $\varpi$ a uniformiser it is the leading coefficient of $c$ relative to $\varpi$, an element of the residue field.
--
--   For a pair $ab = (a,b)$ of one-variable power series over $W$ and a set $S \subseteq \mathbb{Z}$, `initialFormOfSet ϖ S ab` is the Laurent polynomial over the residue field $\sum_{n \in S} \mathrm{leadingResidue}(\varpi, \mathrm{nfCoeff}(ab)(n))\, T^{n}$ when $S$ is finite, and $0$ otherwise; here $\mathrm{nfCoeff}(ab)(n)$ is the $n$-th coefficient of $a$ for $n \ge 0$ and the $|n|$-th coefficient of $b$ for $n < 0$. The lemma `initialFormOfSet_apply` gives, for finite $S$, the coefficientwise description: the $n$-th coefficient is $\mathrm{leadingResidue}(\varpi, \mathrm{nfCoeff}(ab)(n))$ if $n \in S$ and $0$ otherwise.
--
--   Finally, given an order function $v : W \to \mathbb{N}\cup\{\infty\}$ and natural numbers $E, t$, the initial form `initialForm ϖ v E t ab` is `initialFormOfSet` taken over the set $\mathrm{dominantIndices}(v,E,t,ab)$ of indices $n$ at which the term order $v(\mathrm{nfCoeff}(ab)(n)) + \mathrm{annulusWeight}\,E\,t\,(\mathrm{nfExponent}\,n)$ attains the Gauss order of $\mathrm{inU}(a) + \mathrm{inV}(b)$; `initialForm_def` states this unfolding. In particular the value is $0$ whenever that set of dominant indices is infinite.
--
--   **Relation to Mathlib.** Multiplicity, the residue field and residue map of a local ring, and Laurent polynomials are Mathlib's; the extraction of a unit part relative to a fixed $\varpi$, the leading residue, and the initial form of a pair of power series along a set of indices are the project's own.
--
--   **Where it is used.** These notions supply the vocabulary for the local analysis of the crossing model $W[[U,V]]/(UV-\pi)$: the initial form at depth $t$ is the reduction, after optimal rescaling, of an element written as $a(U)+b(V)$ on the circle $v(U)=t$, and it is the object through which multiplicativity of the Gauss order and the counting of zeros on such a circle are expressed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_UVCrossingInitialForm.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

open IsLocalRing

variable {W : Type u} [CommRing W]

def unitPart (ϖ c : W) : W :=
  (pow_multiplicity_dvd ϖ c).choose

theorem pow_multiplicity_mul_unitPart (ϖ c : W) : ϖ ^ multiplicity ϖ c * unitPart ϖ c = c :=
  (pow_multiplicity_dvd ϖ c).choose_spec.symm

variable [IsDomain W] [IsDiscreteValuationRing W]

open Classical in

def leadingResidue (ϖ c : W) : ResidueField W :=
  if c = 0 then 0 else residue W (unitPart ϖ c)

open Classical in

def initialFormOfSet (ϖ : W) (S : Set ℤ) (ab : PowerSeries W × PowerSeries W) :
    LaurentPolynomial (ResidueField W) :=
  if hS : S.Finite then
    ∑ n ∈ hS.toFinset, LaurentPolynomial.C (leadingResidue ϖ (nfCoeff ab n)) * LaurentPolynomial.T n
  else 0

open Classical in

theorem initialFormOfSet_apply (ϖ : W) {S : Set ℤ} (hS : S.Finite)
    (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    (initialFormOfSet ϖ S ab).coeff n = if n ∈ S then leadingResidue ϖ (nfCoeff ab n) else 0 := by
  classical
  rw [initialFormOfSet, dif_pos hS]
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single]
  erw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Set.Finite.mem_toFinset]

def initialForm (ϖ : W) (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    LaurentPolynomial (ResidueField W) :=
  initialFormOfSet ϖ (dominantIndices v E t ab) ab

theorem initialForm_def (ϖ : W) (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    initialForm ϖ v E t ab = initialFormOfSet ϖ (dominantIndices v E t ab) ab := rfl

end

end ModularCurve.UVCrossingModel


