-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_MemMaxVAIff
-- name    : Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_MemMaxVAIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:39.944608+00:00
-- url     : https://prove2.me/theorems/04f16d8b-c4f1-41a7-abc5-f3fd77d363a7
-- title:
--   Mem Max VAIff
-- statement:
--   Definitions and structural lemmas for Mem Max VAIff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/MemMaxVAIff.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
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
namespace Formalism.IndefR.LocBrg
def IntWittLoc : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) L),
      (∀ i j, H i j ∈ Formalism.UG.intL L) → Valued.v H.det = 1 → Formalism.UG.cT σ H = H →
      ∃ R ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L),
        Formalism.UG.cT σ ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * H * ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
          Formalism.UG.antiJ L n
section Glue
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
abbrev VA (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ValuationSubring L :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
theorem mem_VA {x : L} : x ∈ VA L ↔ Valued.v x ≤ 1 := Valuation.mem_valuationSubring_iff _ _
theorem isUnit_VA_iff (a : VA L) : IsUnit a ↔ Valued.v (a : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hmul : ((u : VA L) : L) * (((u⁻¹ : (VA L)ˣ) : VA L) : L) = 1 := by
      exact congrArg (fun x : VA L => (x : L)) u.mul_inv
    have hu : Valued.v ((u : VA L) : L) ≤ 1 := mem_VA.1 (u : VA L).2
    have hu' : Valued.v (((u⁻¹ : (VA L)ˣ) : VA L) : L) ≤ 1 := mem_VA.1 (u⁻¹ : (VA L)ˣ).1.2
    have hprod := congrArg Valued.v hmul
    rw [map_mul, map_one] at hprod
    refine le_antisymm hu ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((u : VA L) : L) *
          Valued.v (((u⁻¹ : (VA L)ˣ) : VA L) : L) := hprod.symm
      _ ≤ Valued.v ((u : VA L) : L) := mul_le_of_le_one_right' hu'
  · intro h
    have ha0 : (a : L) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h
      exact zero_ne_one h
    have hinv : (a : L)⁻¹ ∈ VA L := by
      rw [mem_VA, map_inv₀, h, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(a : L)⁻¹, hinv⟩ : VA L) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ ha0
variable (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x)
def sigA : VA L →+* VA L :=
  (σ.comp (VA L).subtype).codRestrict (VA L) (fun x => by
    show σ (x : L) ∈ VA L
    rw [mem_VA, hv]; exact mem_VA.1 x.2)
theorem sigA_coe (x : VA L) : ((sigA σ hv x : VA L) : L) = σ x := rfl
instance sigA_local : IsLocalHom (sigA σ hv) where
  map_nonunit a ha := by
    rw [isUnit_VA_iff, sigA_coe, hv] at ha
    exact (isUnit_VA_iff a).2 ha
end Glue
section Norm
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
end Norm
section Final
end Final
end Formalism.IndefR.LocBrg


