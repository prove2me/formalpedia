-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:11.310006+00:00
-- url     : https://prove2.me/theorems/a2e1fcc2-eedf-4343-af32-00ec5a444b3d
-- title:
--   Khw Weight Eq Of Irr
-- statement:
--   Definitions and structural lemmas for Khw Weight Eq Of Irr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section KIrr
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}
def kirrWord (A : Fin n → Fin n → Module.End ℂ X) (u : X) : List (Fin n × Fin n) → X
  | [] => u
  | p :: l => A p.1 p.2 (kirrWord A u l)
def kirrWt (ν : Fin n → ℝ) : List (Fin n × Fin n) → Fin n → ℝ
  | [] => ν
  | p :: l => kirrWt ν l + root p.1 p.2
def KirrLow (ε : Fin n → Bool) (l : List (Fin n × Fin n)) : Prop :=
  ∀ p ∈ l, p.2 < p.1 ∧ ε p.1 = ε p.2
def kirrSpan (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) (u : X) : Submodule ℂ X :=
  Submodule.span ℂ {x | ∃ l, KirrLow ε l ∧ x = kirrWord A u l}
def kirrPs (k : ℕ) (μ : Fin n → ℝ) : ℝ := ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), μ a
def kirrH (A : Fin n → Fin n → Module.End ℂ X) (k : ℕ) : Module.End ℂ X :=
  ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), A a a
end KIrr
end ReciprocityTheory.ChartRestriction.DS


