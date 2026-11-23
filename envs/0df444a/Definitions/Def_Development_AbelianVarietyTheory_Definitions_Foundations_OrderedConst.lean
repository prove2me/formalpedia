-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OrderedConst
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_OrderedConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:19.78935+00:00
-- url     : https://prove2.me/theorems/6a4e2ca6-00c9-4766-9d38-b31ef87e81b7
-- title:
--   Ordered Const
-- statement:
--   Definitions and structural lemmas for Ordered Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OrderedConst.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
namespace GlobalTheory.PsType
section Abstract
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
def IsEig (π : Representation ℂ G V) (H : Set G) (θ : G → ℂ) (v : V) : Prop := ∀ h ∈ H, π h v = θ h • v
def aug (π : Representation ℂ G V) (H : Set G) (θ : G → ℂ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ h ∈ H, ∃ w : V, x = π h w - θ h • w}
structure Datum [TopologicalSpace G] (H : Set G) (θ : G → ℂ) : Prop where
  one : (1 : G) ∈ H
  mul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H
  inv : ∀ a ∈ H, a⁻¹ ∈ H
  compact : IsCompact H
  val_one : θ 1 = 1
  val_mul : ∀ a ∈ H, ∀ b ∈ H, θ (a * b) = θ a * θ b
  near : ∃ U ∈ nhds (1 : G), ∀ g ∈ U, g ∈ H → θ g = 1
end Abstract
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
def Triv (χ : kˣ →* ℂˣ) (x : k) : Prop :=
  ∀ u : kˣ, valuation k (u : k) = 1 → valuation k ((u : k) - 1) ≤ valuation k x → χ u = 1
def Ordered (ψ : Fin n → kˣ →* ℂˣ) : Prop :=
  ∀ i a b j : Fin n, i ≤ a → a ≤ b → b ≤ j → ∀ x : k, Triv (ψ i / ψ j) x → Triv (ψ a / ψ b) x
def grp (ψ : Fin n → kˣ →* ℂˣ) : Set (GL (Fin n) k) :=
  {g | g ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (g.val i j)}
open Classical in

def ev (χ : kˣ →* ℂˣ) (x : k) : ℂ :=
  if h : valuation k x = 1 then (χ (Units.mk0 x fun h0 => by simp [h0] at h) : ℂ) else 1
def nxt (ψ : Fin n → kˣ →* ℂˣ) (m : Fin n) : kˣ →* ℂˣ :=
  if h : (m : ℕ) + 1 < n then ψ ⟨(m : ℕ) + 1, h⟩ else 1
def minor (g : GL (Fin n) k) (m : Fin n) : k := (g.val.toSquareBlockProp fun i => i ≤ m).det
def theta (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) : ℂ := ∏ m, ev (ψ m / nxt ψ m) (minor g m)
def HasVec {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : Fin n → kˣ →* ℂˣ) (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ IsEig π (grp ψ) (theta ψ) v
def Agree (ψ ω : Fin n → kˣ →* ℂˣ) : Prop := ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = ω i u
def strip (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k) (m : ℕ) : Set (GL (Fin n) k) :=
  {g | ∀ i j : Fin n, if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j}
def Cut (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) : Prop := ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ¬ Triv (ψ i / ψ j) 1
end GlobalTheory.PsType


