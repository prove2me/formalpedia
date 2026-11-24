-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNormRowSubProdMinors
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNormRowSubProdMinors
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:56:25.145808+00:00
-- url     : https://prove2.me/theorems/e92e69f1-7d64-41ff-b204-24126be0f94c
-- title:
--   Sum Norm Row Sub Prod Minors
-- statement:
--   Definitions and structural lemmas for Sum Norm Row Sub Prod Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumNormRowSubProdMinors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open Classical
noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
def smEquivSub (a d : ℕ) : {s : Fin a → Fin d // StrictMono s} ≃ {S : Finset (Fin d) // S.card = a} where
  toFun s := ⟨Finset.univ.map ⟨s.1, s.2.injective⟩, by simp⟩
  invFun S := ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩
  left_inv s := by
    apply Subtype.ext
    symm
    exact Finset.orderEmbOfFin_unique _ (fun x => by simp) s.2
  right_inv S := by
    apply Subtype.ext
    simp only
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
    · intro hx
      have : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
      exact this
end GlobalTheory.MinorFrame
noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix
variable {ι : Type} [Fintype ι]
def xMat (τ : ι) (d a : ℕ) : Matrix (Fin d) (Fin a) (Pol ι d a) := Matrix.of fun i j => X (τ, i, j)
end GlobalTheory.MinorFrame
noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix
end GlobalTheory.MinorFrame
noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix ComplexConjugate
variable {ι : Type} [Fintype ι]
def tupCoef {a d : ℕ} {n : ι → ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) (T T' : Tup ι a d n) : ℂ :=
  ∏ τ, ∏ j, ((κ τ)ᵀ.submatrix (T τ j).1 (T' τ j).1).det
end GlobalTheory.MinorFrame
noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
end GlobalTheory.MinorFrame


