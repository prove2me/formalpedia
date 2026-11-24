-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InverseSplitting
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_InverseSplitting
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:31:35.94719+00:00
-- url     : https://prove2.me/theorems/6ca3d2ce-1336-42ca-8f24-7fee7edd2518
-- title:
--   Inverse Splitting
-- statement:
--   Definitions and structural lemmas for Inverse Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InverseSplitting.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P
namespace InverseSplitting
open C2x2
variable {m : ℕ}
noncomputable def lsStep (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) :
    ℕ → Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ
  | 0 => (1, 1)
  | n + 1 =>
    (Matrix.of fun i j => if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then l i j - ((lsStep w l n).1 * (lsStep w l n).2) i j else 0)
        else (lsStep w l n).1 i j,
     Matrix.of fun i j => if i.val = j.val + n + 1 then
        (if w.symm j < w.symm i then 0 else l i j - ((lsStep w l n).1 * (lsStep w l n).2) i j)
        else (lsStep w l n).2 i j)
structure Inv (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) (n : ℕ)
    (A B : Matrix (Fin m) (Fin m) ℂ) : Prop where
  up : ∀ i j : Fin m, i < j → A i j = 0 ∧ B i j = 0
  diag : ∀ i, A i i = 1 ∧ B i i = 1
  far : ∀ i j : Fin m, j.val + n < i.val → A i j = 0 ∧ B i j = 0
  supA : ∀ i j : Fin m, j < i → ¬ (w.symm j < w.symm i) → A i j = 0
  supB : ∀ i j : Fin m, j < i → w.symm j < w.symm i → B i j = 0
  prod : ∀ i j : Fin m, i.val ≤ j.val + n → (A * B) i j = l i j
end InverseSplitting
open C2x2 InverseSplitting
end Formalism.FourierDecayAlt.P


