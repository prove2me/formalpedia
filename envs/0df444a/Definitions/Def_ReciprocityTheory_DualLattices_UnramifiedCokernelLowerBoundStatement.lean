-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
-- name    : ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:35.246316+00:00
-- url     : https://prove2.me/theorems/cea336ac-5a78-4ef6-88c5-7ac76d7cd677
-- title:
--   Unramified Cokernel Lower Bound Statement
-- statement:
--   Definitions and structural lemmas for Unramified Cokernel Lower Bound Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthStatement
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
def PermutedCokernelLowerBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (d : ℕ),
      Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL (e (π w)))) ≃ₗ[R] (Fin d → R)) →
      ∀ cw : NNReal, HasLen v R (htCoker H (e w) (e (π w))) cw →
        (v (algebraMap R C (p : R)) : ℝ) ^ ((d : ℝ) / (p - 1)) ≤ cw
def UnramifiedCokernelLowerBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (V1 : NNReal),
    HasLen v R (cokE H.Ht U.εT U.εL i (U.cj i)) V1 →
    (v (algebraMap R C (p : R)) : ℝ) ^
      (((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i) ≤ V1
def CokernelLowerBoundStatement : Prop := PermutedCokernelLowerBoundStatement ∧ UnramifiedCokernelLowerBoundStatement
end ReciprocityTheory.PGsh.Up


