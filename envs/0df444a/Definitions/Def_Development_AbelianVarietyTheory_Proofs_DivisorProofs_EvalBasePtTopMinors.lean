-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EvalBasePtTopMinors
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_EvalBasePtTopMinors
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:49.125636+00:00
-- url     : https://prove2.me/theorems/65b3e7bf-cadc-465c-b056-af9984169feb
-- title:
--   Eval Base Pt Top Minors
-- statement:
--   Definitions and structural lemmas for Eval Base Pt Top Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.MinorFrame.RowIrr
open GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]
def basePt (ι : Type) (d a : ℕ) : Var ι d a → ℂ := fun y => if (y.2.1 : ℕ) = (y.2.2 : ℕ) then 1 else 0
def lowScal (d a : ℕ) (t : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else t
def topRows {a d : ℕ} (h : a ≤ d) : {s : Fin a → Fin d // StrictMono s} :=
  ⟨Fin.castLE h, Fin.strictMono_castLE h⟩
def topMinors {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : Pol ι d a :=
  prodMinors (ι := ι) (n := n) (fun _ _ => topRows h)
end GlobalTheory.MinorFrame.RowIrr


