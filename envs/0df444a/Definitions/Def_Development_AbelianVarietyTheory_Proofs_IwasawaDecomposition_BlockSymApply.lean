-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_BlockSymApply
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_BlockSymApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:16.77435+00:00
-- url     : https://prove2.me/theorems/ac342807-4c80-4521-a281-d0cb9a4aaf2f
-- title:
--   Block Sym Apply
-- statement:
--   Definitions and structural lemmas for Block Sym Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/BlockSymApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.DomainDens
def blockSym {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q,
    X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b))
example : blockSym (ι := Unit) (p := 1) (q := 1) (n := 1) (by simp) () 0 0 = X (0, 0) := by
  simp [blockSym, Subsingleton.elim (Fintype.equivFinOfCardEq _ _) 0]
end GlobalTheory.DomainDens


