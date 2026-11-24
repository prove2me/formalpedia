-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
-- name    : Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:27.587341+00:00
-- url     : https://prove2.me/theorems/90ba2d0f-2866-45bb-b721-a913805ca63b
-- title:
--   Is Co Type
-- statement:
--   Definitions and structural lemmas for Is Co Type, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/IsCoType.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition
namespace GlobalTheory.ParHecke
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
def IsReps (g : GL (A ⊕ D) k) (R : Finset (GL (A ⊕ D) k)) (d : GL (A ⊕ D) k → kˣ) : Prop :=
  (∀ j ∈ R, j ∈ parahoric k A D ∧ (d j : k) = j.1.toBlocks₂₂.det) ∧
    ∀ j ∈ parahoric k A D, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ parahoric k A D
def IsTOp {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (g : GL (A ⊕ D) k)
    (x y : V) : Prop :=
  ∀ R d, IsReps g R d → y = ∑ j ∈ R, (((ξ (d j))⁻¹ : ℂˣ) : ℂ) • π (j * g) x
def indic (s : Finset D) : D → ℤ := fun i => if i ∈ s then 1 else 0
def genVal (q r N : ℕ) (B : Multiset ℂˣ) (n : ℕ) : ℂ :=
  ((Real.sqrt q : ℝ) : ℂ) ^ (r * n + n * (N - n)) * (B.map fun b : ℂˣ => (b : ℂ)).esymm n
def IsGen {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (ϖ : kˣ)
    (B : Multiset ℂˣ) (x : V) : Prop :=
  x ∈ typeSpace π ξ ∧ B.card = Fintype.card D ∧ ∀ s : Finset D,
    IsTOp π ξ (mtor ϖ (indic s)) x (genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • x)
def IsCoType {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (ℓ : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ v, ℓ (π j v) = (ξ d : ℂ) * ℓ v
def schur (x : Matrix (A ⊕ D) (A ⊕ D') k) : Matrix D D' k := x.toBlocks₂₂ - x.toBlocks₂₁ * x.toBlocks₁₁⁻¹ * x.toBlocks₁₂
def liftS (ξ : kˣ →* ℂˣ) (ψ : Matrix D D' k → ℂ) (x : Matrix (A ⊕ D) (A ⊕ D') k) : ℂ := datum ξ x * ψ (schur x)
open Classical in

def intInd (y : Matrix D D' k) : ℂ := if ∀ i j, y i j ∈ 𝒪[k] then 1 else 0
def IsRepsK (g₀ : GL D k) (R : Finset (GL D k)) : Prop :=
  (∀ g ∈ R, ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * g₀ * κ') ∧ ∀ κ ∈ KO k D, ∃! g, g ∈ R ∧ g⁻¹ * (κ * g₀) ∈ KO k D
def IsHgt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (H : GL n k → ℝ) : Prop :=
  (∀ κ ∈ KO k n, ∀ g, H (κ * g) = H g ∧ H (g * κ) = H g) ∧ ∀ e : n → ℤ, H (torusElt k n ϖ e) = (resCard k : ℝ) ^ (-(sumAbs e))
def segL (ϖ : kˣ) (z : ℂˣ) (t : ℕ) : Multiset ℂˣ :=
  (Multiset.range t).map fun n : ℕ => z * absPow k ((n : ℂ) - ((t : ℂ) - 1) / 2) ϖ
def omTwo {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μS μT : kˣ →* ℂˣ) (g : GL a k) (h : GL b k)
    (u : Matrix b a k → ℂ) : Matrix b a k → ℂ :=
  (((μS * μT⁻¹) (GeneralLinearGroup.det h) : ℂˣ) : ℂ) • om μT⁻¹ g h u
example {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) (g : GL (A ⊕ D) k) :
    IsTOp π ξ g 0 0 := fun R d _ => by simp
example : IsReps (1 : GL (A ⊕ D) k) {1} (fun _ => 1) := by
  refine ⟨fun j hj => ?_, fun j hj => ⟨1, ⟨by simp, by simpa using hj⟩, fun y hy => by simpa using hy.1⟩⟩
  rw [Finset.mem_singleton] at hj
  subst hj
  refine ⟨one_mem _, ?_⟩
  have : (1 : GL (A ⊕ D) k).1.toBlocks₂₂ = 1 := by
    ext i j; simp [toBlocks₂₂, Matrix.one_apply]
  rw [this]; simp
end GlobalTheory.ParHecke
end


