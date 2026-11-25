-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalFlat
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalFlat
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:16.9378+00:00
-- url     : https://prove2.me/theorems/97873035-d47a-4acc-91a7-eb511b2e2d80
-- title:
--   Statements Cone Local Flat
-- statement:
--   Definitions and structural lemmas for Statements Cone Local Flat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsConeLocalFlat.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing
noncomputable section
universe u
section Cone
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
omit [DecidableEq K] in

theorem primeCompl_map_le_nonZeroDivisors (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) :
    W.primeCompl.map (Ideal.Quotient.mk P) ≤ nonZeroDivisors (MRing ι F ⧸ P) := by
  rintro _ ⟨s, hs, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hs (hPW h)
def coneLocal (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Subalgebra (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) :=
  Localization.subalgebra.ofField _ _ (primeCompl_map_le_nonZeroDivisors P W hPW)
omit [DecidableEq K] in

instance coneLocal.isLocalization (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) (coneLocal P W hPW) :=
  Localization.subalgebra.isLocalization_ofField _ _ _
theorem degZeroLoc_le_coneLocal (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    ∀ x ∈ degZeroLoc P {W}, x ∈ coneLocal P W hPW := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨b, f, g, -, -, -, hgW, rfl⟩ := hx
    exact ⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, hgW W rfl, rfl⟩, div_eq_mul_inv _ _⟩
  | algebraMap r =>
    rw [IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P)]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
def degZeroLocToCone (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    degZeroLoc P {W} →+* coneLocal P W hPW :=
  (degZeroLoc P {W}).val.toRingHom.codRestrict (coneLocal P W hPW)
    (fun x => degZeroLoc_le_coneLocal P W hPW x x.2)
instance degZeroLoc.algebraCone (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Algebra (degZeroLoc P {W}) (coneLocal P W hPW) :=
  (degZeroLocToCone P W hPW).toAlgebra
end Cone
def ConeLocalFlat.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W),
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∃ (_ : IsLocalRing (degZeroLoc P {W})) (_ : IsLocalRing (coneLocal P W hPW)),
      Module.Flat (degZeroLoc P {W}) (coneLocal P W hPW) ∧
        (maximalIdeal (degZeroLoc P {W})).map
            (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) =
          maximalIdeal (coneLocal P W hPW)
end
end GroundTheory.Heights₂.Heights.FieldNumbers


