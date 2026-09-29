-- Prove2me | Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
-- name    : AlgebraicCurve_RatFuncPlaceInfty
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/95864536-1573-56f9-9f83-efe538f03ec0
-- title:
--   The place at infinity of a rational function field
-- statement:
--   Let $K$ be a field. Mathlib's valuation $v_\infty =$ `RatFunc.inftyValuation K` on $K(t)$ sends $0$ to $0$ and a nonzero $f$ to $\exp(\deg_{\mathrm{int}} f)$, so that $p/q \mapsto \exp(\deg p - \deg q)$; its valuation subring is $\{f : v_\infty(f) \le 1\} = \{p/q : \deg p \le \deg q\}$. The module first records `nontrivial_valueGroup_inftyValuation`: the value group of (the monoid-with-zero-hom class of) $v_\infty$ is nontrivial, witnessed by the image $\exp(1)$ of $t$, which is a nonzero non-identity element of that group.
--
--   The main definition, `placeInfty K`, exhibits this valuation subring as a term of the project's structure `Place K (RatFunc K)`, whose fields are: a valuation subring of the ambient field; the requirement that the image of every element of the base field $K$ lie in it, verified here from triviality of $v_\infty$ on constants; the requirement that the subring be distinct from the whole field, which follows from the nontriviality just proved; and the requirement that it be a principal ideal ring, obtained from discreteness of $v_\infty$ (the `Place` structure then supplies, for any such place, a discrete valuation ring structure, an order function $\mathrm{ord}$, a residue field and a degree). A simp lemma identifies the underlying valuation subring of `placeInfty K` with that of $v_\infty$.
--
--   **Relation to Mathlib.** Mathlib supplies the valuation `RatFunc.inftyValuation` and its valuation subring; the structure `Place` packaging a valuation subring of an extension $F/K$ containing $K$, proper and principal, is the project's own, and this module produces the corresponding term for the place at infinity.
--
--   **Where it is used.** Together with the places `Place.ofHeightOneSpectrum` attached to the height-one primes of $K[t]$, this is the remaining place of $K(t)/K$, so it enters the project's computations of divisors, degrees and degree-zero divisor class groups for the rational function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem nontrivial_valueGroup_inftyValuation :
    Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

def placeInfty : Place K (RatFunc K) :=
  haveI := nontrivial_valueGroup_inftyValuation K
  { toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
    algebraMap_mem' := fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
    ne_top' := by
      simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
      infer_instance
    isPrincipalIdealRing' :=
      (Valuation.valuationSubring_isDiscreteValuationRing
        (RatFunc.inftyValuation K)).toIsPrincipalIdealRing }

@[simp]
theorem placeInfty_toValuationSubring :
    (placeInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl

end RationalFunctionField

end AlgebraicCurve


