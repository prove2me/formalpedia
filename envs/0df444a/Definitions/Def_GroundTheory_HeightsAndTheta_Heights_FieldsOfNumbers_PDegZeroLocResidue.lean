-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocResidue
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocResidue
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:28:15.9604+00:00
-- url     : https://prove2.me/theorems/4379b41e-9679-5804-a6e1-2448644be8d3
-- title:
--   PDeg Zero Loc Residue
-- statement:
--   Definitions and structural lemmas for PDeg Zero Loc Residue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocResidue.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_fg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocQuot_proof_f2e3f8a36e28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
set_option synthInstance.maxHeartbeats 400000
namespace DegZeroLocResidue
variable {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
local notation "fr" Q:max h:max =>
  algebraMap (_ ⧸ Q) (FractionRing (_ ⧸ Q)) (Ideal.Quotient.mk Q h)
omit [DecidableEq K] in

theorem fr_ne_zero (Q : Ideal (MRing ι F)) [Q.IsPrime] {h : MRing ι F} (hh : h ∉ Q) :
    fr Q h ≠ 0 := by
  rwa [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
variable {P W : Ideal (MRing ι F)} [P.IsPrime] [W.IsPrime]
omit [DecidableEq K] in

theorem residue_eq (hPW : P ≤ W) {f g f' g' : MRing ι F} (hg : g ∉ W) (hg' : g' ∉ W)
    (h : fr P f / fr P g = fr P f' / fr P g') : fr W f / fr W g = fr W f' / fr W g' := by
  rw [div_eq_div_iff (fr_ne_zero P fun h => hg (hPW h)) (fr_ne_zero P fun h => hg' (hPW h)),
    ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h
  rw [div_eq_div_iff (fr_ne_zero W hg) (fr_ne_zero W hg'), ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, Ideal.Quotient.eq.mpr (hPW (Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h)))]
variable (P W) in
open Classical in

def res (x : FractionRing (MRing ι F ⧸ P)) : FractionRing (MRing ι F ⧸ W) :=
  if h : ∃ fg : MRing ι F × MRing ι F, fg.2 ∉ W ∧ x = fr P fg.1 / fr P fg.2 then
    fr W h.choose.1 / fr W h.choose.2 else 0
omit [DecidableEq K] in

theorem res_eq (hPW : P ≤ W) {x : FractionRing (MRing ι F ⧸ P)} {f g : MRing ι F} (hg : g ∉ W)
    (hx : x = fr P f / fr P g) : res P W x = fr W f / fr W g := by
  have h : ∃ fg : MRing ι F × MRing ι F, fg.2 ∉ W ∧ x = fr P fg.1 / fr P fg.2 := ⟨(f, g), hg, hx⟩
  rw [res, dif_pos h]
  exact residue_eq hPW h.choose_spec.1 hg (h.choose_spec.2.symm.trans hx)
theorem exists_rep (x : degZeroLoc P {W}) : ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
    IsMultiHomog g b ∧ g ∉ W ∧ (x : FractionRing (MRing ι F ⧸ P)) = fr P f / fr P g := by
  obtain ⟨b, f, g, hf, hg, -, hgW, hx⟩ := DegZeroLocQuot.proof F K ι P {W}
    (by rintro _ rfl; infer_instance) x x.2
  exact ⟨b, f, g, hf, hg, hgW W rfl, hx⟩
def ρ (hPW : P ≤ W) : degZeroLoc P {W} →+* FractionRing (MRing ι F ⧸ W) where
  toFun x := res P W x
  map_one' := by
    have h1 : (1 : MRing ι F) ∉ W := (Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top'
    rw [res_eq hPW (f := 1) (g := 1) h1 (by simp)]; simp
  map_mul' x y := by
    obtain ⟨-, f, g, -, -, hg, hx⟩ := exists_rep x
    obtain ⟨-, f', g', -, -, hg', hy⟩ := exists_rep y
    have hgg : g * g' ∉ W := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hg hg'
    rw [res_eq hPW hg hx, res_eq hPW hg' hy, res_eq (f := f * f') hPW hgg
      (by rw [Subalgebra.coe_mul, hx, hy, div_mul_div_comm, map_mul, map_mul, map_mul, map_mul]),
      div_mul_div_comm, map_mul, map_mul, map_mul, map_mul]
  map_zero' := by
    rw [res_eq hPW (f := 0) (g := 1) ((Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top') (by simp)]
    simp
  map_add' x y := by
    obtain ⟨-, f, g, -, -, hg, hx⟩ := exists_rep x
    obtain ⟨-, f', g', -, -, hg', hy⟩ := exists_rep y
    have hgg : g * g' ∉ W := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hg hg'
    rw [res_eq hPW hg hx, res_eq hPW hg' hy, res_eq (f := f * g' + g * f') hPW hgg
      (by rw [Subalgebra.coe_add, hx, hy, div_add_div _ _ (fr_ne_zero P fun h => hg (hPW h))
        (fr_ne_zero P fun h => hg' (hPW h))]; simp only [map_add, map_mul]),
      div_add_div _ _ (fr_ne_zero W hg) (fr_ne_zero W hg')]
    simp only [map_add, map_mul]
end DegZeroLocResidue
end
end GroundTheory.Heights₂.Heights.FieldNumbers


