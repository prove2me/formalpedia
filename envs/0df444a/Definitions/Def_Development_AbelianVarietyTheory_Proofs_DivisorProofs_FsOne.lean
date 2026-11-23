-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:18.235943+00:00
-- url     : https://prove2.me/theorems/cf1432b1-21ab-4f3c-8eb8-fe2824385cbe
-- title:
--   Fs One
-- statement:
--   Definitions and structural lemmas for Fs One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FsOne.lean

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
open scoped ComplexConjugate
namespace GlobalTheory.FibCos
def nrm (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  (G 0 0 + x * G 1 0 + conj x * G 0 1 + ((‖x‖ ^ 2 : ℝ) : ℂ) * G 1 1).re
def cos (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  ‖G 0 0 + x * G 1 0‖ ^ 2 / ((G 0 0).re * nrm G x)
def fs (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  G.det.re / (Real.pi * nrm G x ^ 2)
end GlobalTheory.FibCos


