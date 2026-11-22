-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_LminorPos
-- name    : Formalism_RealPlaceAnalysis_LminorPos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:24.768873+00:00
-- url     : https://prove2.me/theorems/3c82b6cb-4641-473a-b85a-b56fe741e346
-- title:
--   Lminor Pos
-- statement:
--   Definitions and structural lemmas for Lminor Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/LminorPos.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.REAL
def lminor {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) : ℂ :=
  (Matrix.of fun a b : Fin i => x (Fin.castLE (Nat.lt_succ_iff.mp i.isLt) a)
    (Fin.castLE (Nat.lt_succ_iff.mp i.isLt) b)).det
def LminorPos : Prop :=
  ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Yᴴ = Y → ∀ i : Fin (n + 1),
    (lminor (NormedSpace.exp Y) i).im = 0 ∧ 0 < (lminor (NormedSpace.exp Y) i).re
def DecayPhi : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (g : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ),
    StrictAnti lam →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) →
    Yᴴ = Y → (∀ a b : Fin n, ε a = ε b → Y a b = 0) →
    ∏ i : Fin n, (if h : 0 < (i : ℕ) then
        ((lminor (NormedSpace.exp Y) ⟨i, by omega⟩).re) ^
          (-(lam ⟨(i : ℕ) - 1, by omega⟩ - lam i + 1))
      else 1) ≤
      Real.exp (-(g / 8) * min (hs Y) (Real.sqrt (hs Y) / Real.sqrt n))
end Formalism.REAL


