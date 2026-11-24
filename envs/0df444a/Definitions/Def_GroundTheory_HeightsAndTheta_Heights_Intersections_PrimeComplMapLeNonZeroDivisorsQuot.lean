-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:28.656933+00:00
-- url     : https://prove2.me/theorems/14cbd785-7e48-426a-9597-081021061939
-- title:
--   Prime Compl Map Le Non Zero Divisors Quot
-- statement:
--   Definitions and structural lemmas for Prime Compl Map Le Non Zero Divisors Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PrimeComplMapLeNonZeroDivisorsQuot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
section Cone
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem primeCompl_map_le_nonZeroDivisors_quot (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) : W.primeCompl.map (Ideal.Quotient.mk P) ≤ nonZeroDivisors (MRing ι ⧸ P) := by
  rintro _ ⟨g, hg, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hg (hPW h)
def coneLocRing (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Subalgebra (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) :=
  Localization.subalgebra.ofField _ _ (primeCompl_map_le_nonZeroDivisors_quot P W hPW)
instance coneLocRing.isLocalization (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) (coneLocRing P W hPW) :=
  Localization.subalgebra.isLocalization_ofField _ _ _
theorem locRing_le_coneLocRing (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    ∀ x ∈ locRing P W, x ∈ coneLocRing P W hPW := by
  intro x hx
  have hle : locRing P W ≤ (coneLocRing P W hPW).toSubring := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨u, v, a, hv, hvW, -, -, rfl⟩
    exact ⟨Ideal.Quotient.mk P u, Ideal.Quotient.mk P v, ⟨v, hvW, rfl⟩,
      by rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv]⟩
  exact hle hx
def locRingToCone (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    locRing P W →+* coneLocRing P W hPW :=
  (locRing P W).subtype.codRestrict (coneLocRing P W hPW)
    (fun x => locRing_le_coneLocRing P W hPW x x.2)
instance locRing.algebraCone (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Algebra (locRing P W) (coneLocRing P W hPW) :=
  (locRingToCone P W hPW).toAlgebra
end Cone
def regularityLocalFlat_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (hP : IsMultiProjPrime P) (hW : IsMultiProjPrime W) (hPW : P ≤ W),
    haveI := hP.1
    haveI := hW.1
    ∃ (_ : IsLocalRing (locRing P W)) (_ : IsLocalRing (coneLocRing P W hPW)),
      Module.Flat (locRing P W) (coneLocRing P W hPW) ∧
        (maximalIdeal (locRing P W)).map (algebraMap (locRing P W) (coneLocRing P W hPW)) =
          maximalIdeal (coneLocRing P W hPW)
end
end GroundTheory.Heights₂.Heights.Inter


