-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:31.393842+00:00
-- url     : https://prove2.me/theorems/d0476550-91b7-4d5b-ac48-57df2693412a
-- title:
--   Opposite Weyl Subgroup Closed
-- statement:
--   Definitions and structural lemmas for Opposite Weyl Subgroup Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def Grp {k r : ℕ} (U : Set (Mat k r)) (_h : IsClosedSubgroup U) : Type := U
namespace Grp
variable {k r : ℕ} {U : Set (Mat k r)} {h : IsClosedSubgroup U}
def val (a : Grp U h) : Mat k r := Subtype.val a
lemma mem (a : Grp U h) : a.val ∈ U := Subtype.property a
def mk (x : Mat k r) (hx : x ∈ U) : Grp U h := (⟨x, hx⟩ : U)
lemma ext' {a b : Grp U h} (e : a.val = b.val) : a = b := Subtype.ext e
instance : Group (Grp U h) where
  mul a b := mk (a.val * b.val) (h.mul_mem _ a.mem _ b.mem)
  one := mk 1 h.one_mem
  inv a := mk (a.val⁻¹) (h.inv_mem _ a.mem)
  mul_assoc a b c := ext' (Matrix.mul_assoc _ _ _)
  one_mul a := ext' (Matrix.one_mul _)
  mul_one a := ext' (Matrix.mul_one _)
  inv_mul_cancel a := ext' (Matrix.nonsing_inv_mul _ (h.unit _ a.mem))
instance : TopologicalSpace (Grp U h) := inferInstanceAs (TopologicalSpace U)
instance : MeasurableSpace (Grp U h) := borel _
instance : BorelSpace (Grp U h) := ⟨rfl⟩
lemma emb : IsClosedEmbedding (val : Grp U h → Mat k r) := h.closed.isClosedEmbedding_subtypeVal
instance : IsTopologicalGroup (Grp U h) where
  continuous_mul := by
    rw [emb.isInducing.continuous_iff]
    exact Continuous.matrix_mul (emb.continuous.comp continuous_fst) (emb.continuous.comp continuous_snd)
  continuous_inv := by
    rw [emb.isInducing.continuous_iff]
    have : (val ∘ fun a : Grp U h => a⁻¹) = fun a : Grp U h => (a.val.det)⁻¹ • a.val.adjugate := by
      funext a
      show a.val⁻¹ = _
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    have hv : Continuous (val : Grp U h → Mat k r) := emb.continuous
    refine Continuous.smul (Continuous.inv₀ hv.matrix_det fun a => (h.unit _ a.mem).ne_zero) hv.matrix_adjugate
instance : LocallyCompactSpace (Grp U h) :=
  have : LocallyCompactSpace (Mat k r) := inferInstanceAs (LocallyCompactSpace (Mt k r))
  emb.locallyCompactSpace
instance : T2Space (Grp U h) := emb.isEmbedding.t2Space
end Grp
variable {k r : ℕ}
abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k
def midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : Fin (k + 1) := ⟨i.val - r, by have := hi; omega⟩
lemma mid_wI (m : Fin (k + 1)) : mid k r (wI k r m) := by
  have := m.isLt
  constructor <;> simp only [wI] <;> omega
def Em (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (k + 1)) ℂ := fun i m => if i = wI k r m then 1 else 0
def εb (k : ℕ) : Fin (k + 1) → Bool := fun j => decide (j ≠ Fin.last k)
end Formalism.FourierDecayAlt.P.B2x3
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


