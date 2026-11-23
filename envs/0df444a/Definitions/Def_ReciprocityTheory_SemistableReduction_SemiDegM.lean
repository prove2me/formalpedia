-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegM
-- name    : ReciprocityTheory_SemistableReduction_SemiDegM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:57.93892+00:00
-- url     : https://prove2.me/theorems/768ee29b-2f45-4328-b312-84c2a1350599
-- title:
--   Semi Deg M
-- statement:
--   Definitions and structural lemmas for Semi Deg M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegM.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
def colMat {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) K :=
  Matrix.of fun a i => b i a
def midG {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.diagonal fun a => if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0
def midForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := midG r m g
  G_herm a b := by
    by_cases hab : a = b
    · subst hab
      simp only [midG, Matrix.diagonal_apply_eq]
      split_ifs with h
      · exact hfix a h.1 h.2
      · exact map_zero _
    · simp [midG, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
end ReciprocityTheory.MultiplicativeHeights.SemiPt


