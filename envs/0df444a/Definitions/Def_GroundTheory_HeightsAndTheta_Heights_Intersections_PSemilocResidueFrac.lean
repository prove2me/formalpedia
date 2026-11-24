-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:01.542138+00:00
-- url     : https://prove2.me/theorems/7b171ba2-5eeb-4c88-af7e-acb586ff9d45
-- title:
--   PSemiloc Residue Frac
-- statement:
--   Definitions and structural lemmas for PSemiloc Residue Frac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
namespace SemilocResidueFrac
section Eval
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
theorem aeval_eq_zero_iff (W : Ideal (MRing ι)) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) {f : MRing ι} : aeval x f = 0 ↔ f ∈ W := by
  rw [← hx, RingHom.mem_ker]
def den (P W : Ideal (MRing ι)) [W.IsPrime] : Submonoid (MRing ι ⧸ P) :=
  W.primeCompl.map (Ideal.Quotient.mk P)
theorem den_le (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    den P W ≤ nonZeroDivisors (MRing ι ⧸ P) := by
  rintro _ ⟨w, hw, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h =>
    Ideal.mem_primeCompl_iff.1 hw (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
abbrev locAt (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Subalgebra (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) :=
  Localization.subalgebra (FractionRing (MRing ι ⧸ P)) (den P W) (den_le P W hPW)
def quotEv (P W : Ideal (MRing ι)) (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) : MRing ι ⧸ P →+* Ω :=
  Ideal.Quotient.lift P (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom fun _ hf =>
    (aeval_eq_zero_iff W x hx).2 (hPW hf)
theorem quotEv_den (P W : Ideal (MRing ι)) [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) (t : den P W) : IsUnit (quotEv P W hPW x hx t) := by
  obtain ⟨_, w, hw, rfl⟩ := t
  exact isUnit_iff_ne_zero.2 fun h => Ideal.mem_primeCompl_iff.1 hw ((aeval_eq_zero_iff W x hx).1 h)
def evAt (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) : locAt P W hPW →+* Ω :=
  IsLocalization.lift (M := den P W) (quotEv_den P W hPW x hx)
theorem locRing_le (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    locRing P W ≤ (locAt P W hPW).toSubring := by
  rw [locRing, Subring.closure_le]
  rintro _ ⟨u, w, a, hw, hwW, -, -, rfl⟩
  exact ⟨Ideal.Quotient.mk P u, Ideal.Quotient.mk P w, ⟨w, hwW, rfl⟩, rfl⟩
def evLoc (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) : locRing P W →+* Ω :=
  (evAt P W hPW x hx).comp
    { toFun := fun z => ⟨z, locRing_le P W hPW z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
end Eval
section Field
variable {Ω : Type} [Field Ω]
def rangeSubfield {R : Type*} [CommRing R] (ρ : R →+* Ω) (hinv : ∀ r, ρ r ≠ 0 → ∃ r', ρ r' * ρ r = 1) :
    Subfield Ω :=
  { ρ.range with
    inv_mem' := by
      rintro _ ⟨r, rfl⟩
      by_cases h : ρ r = 0
      · rw [h, inv_zero]
        exact ⟨0, map_zero ρ⟩
      · obtain ⟨r', e⟩ := hinv r h
        exact ⟨r', eq_inv_of_mul_eq_one_left e⟩ }
end Field
end SemilocResidueFrac
end GroundTheory.Heights₂.Heights.Inter


