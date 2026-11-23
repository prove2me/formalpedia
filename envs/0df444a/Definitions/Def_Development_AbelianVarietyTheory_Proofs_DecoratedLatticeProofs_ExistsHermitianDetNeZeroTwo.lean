-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:32.802321+00:00
-- url     : https://prove2.me/theorems/9da559cc-0d27-4d75-a1b4-3a9534889cd1
-- title:
--   Exists Hermitian Det Ne Zero Two
-- statement:
--   Definitions and structural lemmas for Exists Hermitian Det Ne Zero Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwo.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open MvPolynomial Matrix
noncomputable def hermGenericMatrix {κ : Type} [Field κ] (n : ℕ) (e : κ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) κ) :=
  Matrix.of fun i j => X (i, j) + X (j, i) + C e * (X (i, j) - X (j, i))
end GlobalTheory


