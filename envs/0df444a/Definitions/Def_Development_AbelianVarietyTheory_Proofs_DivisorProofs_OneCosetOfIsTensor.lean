-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:48.124196+00:00
-- url     : https://prove2.me/theorems/afd96adb-9513-4a12-af7b-473e95bdd527
-- title:
--   One Coset Of Is Tensor
-- statement:
--   Definitions and structural lemmas for One Coset Of Is Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
abbrev Shift (G : Grid k) : Type :=
  ∀ j : Fin (G.m - 1), Matrix (Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1)) k
def Shift.vars (Y : Shift G) : Vars G := fun j rs => Y j rs.1.1 rs.1.2
theorem tgt_eq (hs : 1 ≤ G.s) (j : Fin (G.m - 1)) :
    topRank G (j + 1) + (G.m - 2 - j) = G.rank (G.m, j + 1) := by
  have h1 := topRank_add hs ((j : ℕ) + 1)
  have h2 := j.isLt
  omega
theorem src_eq (hs : 1 ≤ G.s) (j : Fin (G.m - 1)) :
    topRank G j + (G.m - 2 - j + 1) = G.rank (G.m, j) := by
  have h1 := topRank_add hs (j : ℕ)
  have h2 := j.isLt
  omega
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
end GlobalTheory.FunObj.OneCosetProof
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip
end GlobalTheory.FunObj


