-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__NotIsGenericDetRepTwo_461173a5118a9903
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__NotIsGenericDetRepTwo_461173a5118a9903
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:39.765945+00:00
-- url     : https://prove2.me/theorems/01ecb70d-8e22-4fa7-bfe2-0741362bf107
-- title:
--   Not Is Generic Det Rep Two
-- statement:
--   Definitions and structural lemmas for Not Is Generic Det Rep Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/NotIsGenericDetRepTwo.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
namespace GlobalTheory.Whittaker
section Generic
variable {R : Type} [CommRing R] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
def superDiag (g : GL (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, (g : Matrix (Fin n) (Fin n) R) i j
def IsFunctional (ψ : AddChar R Circle) (π : Representation ℂ (GL (Fin n) R) V) (l : Module.Dual ℂ V) : Prop :=
  ∀ u ∈ unipB R (Fin n), ∀ v, l (π u v) = (ψ (superDiag u) : ℂ) * l v
def IsGeneric (ψ : AddChar R Circle) (π : Representation ℂ (GL (Fin n) R) V) : Prop :=
  ∃ l : Module.Dual ℂ V, l ≠ 0 ∧ IsFunctional ψ π l
end Generic
end GlobalTheory.Whittaker
namespace GlobalTheory.Published
open GlobalTheory.Whittaker
def JacquetShalikaLocalBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
      (α : Fin n → ℂˣ), HasSatake π α → IsUnitarisable π → IsGeneric ψ π →
      ∀ i, (resCard k : ℝ) ^ (-(1 / 2) : ℝ) < ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ < (resCard k : ℝ) ^ (1 / 2 : ℝ)
namespace JacquetShalikaLocalBound
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end JacquetShalikaLocalBound
end GlobalTheory.Published


