-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementNorm
-- name    : Formalism_LocalToGlobal_AlgebraicTheory_StatementNorm
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:30.661803+00:00
-- url     : https://prove2.me/theorems/f3822f01-b03d-56e3-a85e-0bf11bf06866
-- title:
--   Statement Norm
-- statement:
--   Definitions and structural lemmas for Statement Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AlgebraicTheory/StatementNorm.lean

import Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.AlgTh
open Formalism.L2.Th1.H (cmL CmOK matH IsSelfDual IsLat IsHerm IsPosDef Th alphaQ inter relIdx)
open Formalism.L2.Th1.GD (LocNorm)
def hPow {n : Type} (I : Type) [DecidableEq I] (h : Matrix n n ℂ) : Matrix (n × I) (n × I) ℂ :=
  fun w w' => if w.2 = w'.2 then h w.1 w'.1 else 0
def latPow {n : Type} (I : Type) (Λ : AddSubgroup (n → ℂ)) : AddSubgroup (n × I → ℂ) where
  carrier := {z | ∀ i, (fun k => z (k, i)) ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy i => Λ.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => Λ.neg_mem (hx i)
def fnPow {n : Type} (I : Type) [Fintype I] (θ : (n → ℂ) → ℂ) (z : n × I → ℂ) : ℂ := ∏ i, θ fun k => z (k, i)
def LocNormScale : Prop :=
  ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (c : ℂ), ‖ι c‖ ≤ 1 →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ (c • θ) p ι
def LocNormPow : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (I : Type) [Fintype I] [DecidableEq I],
    LocNorm a₀ b₀ dK ha hdK lam hlam (hPow I h) (latPow I Λ) (fnPow I θ) p ι
def LocNormInter : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ₁ Λ₂ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ₁ → IsLat Λ₂ →
    IsSelfDual (matH h) Λ₁ → IsSelfDual (matH h) Λ₂ →
    (∀ x ∈ Λ₁, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ₁) → (∀ x ∈ Λ₂, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ₂) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ₁,
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ¬ p ∣ relIdx Λ₁ Λ₂ →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ₁ θ p ι →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ₂ (inter (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ₁ Λ₂ θ) p ι
end Formalism.L2.AlgTh


