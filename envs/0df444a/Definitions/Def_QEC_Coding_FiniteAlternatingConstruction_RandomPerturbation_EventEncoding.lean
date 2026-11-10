-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:59:46.262299+00:00
-- url     : https://prove2.me/theorems/8ee36d02-53fe-4918-9ac0-3f69b8bd5cab
-- title:
--   Event Encoding
-- statement:
--   Definitions and structural lemmas for Event Encoding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventEncoding.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Mathlib.Data.List.Lex
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def eventScanKey (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : List ℕ :=
  (e.val.image (triangleKey P)).sort (· ≤ ·)
end QEC.Coding.BDL26RandomPerturbation


