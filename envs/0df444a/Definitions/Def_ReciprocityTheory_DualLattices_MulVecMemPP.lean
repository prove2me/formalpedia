-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
-- name    : ReciprocityTheory_DualLattices_MulVecMemPP
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T17:17:01.644988+00:00
-- url     : https://prove2.me/theorems/4fa9c7e6-d0c9-56b7-8425-9134f9f2d24c
-- title:
--   Mul Vec Mem PP
-- statement:
--   Definitions and structural lemmas for Mul Vec Mem PP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MulVecMemPP.lean

import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section F3b
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
def sumX (D : Lifts H U X) : (Ix g → R) →ₗ[R] augIdeal H.AA.carrier where
  toFun c := ⟨∑ k, c k • xL D k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (D.x_mem k)⟩
  map_add' c c' := by apply Subtype.ext; simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by apply Subtype.ext; simp [Finset.smul_sum, smul_smul]
end F3b
end ReciprocityTheory.PGsh.Up


