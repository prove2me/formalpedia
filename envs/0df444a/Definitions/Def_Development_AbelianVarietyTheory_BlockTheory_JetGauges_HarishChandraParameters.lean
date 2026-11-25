-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:27.943231+00:00
-- url     : https://prove2.me/theorems/8524931d-0ffd-480c-8e99-8ca5bbebe1d6
-- title:
--   Harish Chandra Parameters
-- statement:
--   Definitions and structural lemmas for Harish Chandra Parameters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/HarishChandraParameters.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData
variable {n : ℕ}
def formJ (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun c => if ε c then 1 else -1
def grpG (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | gᴴ * formJ ε * g = formJ ε}
def grpK (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {k | k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ ∀ a b, ε a ≠ ε b → k a b = 0}
def root (a b : Fin n) : Fin n → ℝ := Pi.single a 1 - Pi.single b 1
def posPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun x => x.1 < x.2
def cptPairs (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => x.1 < x.2 ∧ ε x.1 = ε x.2
def ncPairs (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => x.1 < x.2 ∧ ε x.1 ≠ ε x.2
def rho (n : ℕ) : Fin n → ℝ := (1 / 2 : ℝ) • ∑ x ∈ posPairs n, root x.1 x.2
def rhoC (ε : Fin n → Bool) : Fin n → ℝ := (1 / 2 : ℝ) • ∑ x ∈ cptPairs ε, root x.1 x.2
def rhoNC (ε : Fin n → Bool) : Fin n → ℝ := (1 / 2 : ℝ) • ∑ x ∈ ncPairs ε, root x.1 x.2
def IsHCParam (μ : Fin n → ℝ) : Prop :=
  StrictAnti μ ∧ ∀ i, ∃ m : ℤ, μ i = (m : ℝ) + ((n : ℝ) - 1) / 2
def lowestWeight (ε : Fin n → Bool) (μ : Fin n → ℝ) : Fin n → ℝ := μ + rhoNC ε - rhoC ε
def torus (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Complex.exp (Complex.I * (θ a : ℂ))
def wtChar (ω θ : Fin n → ℝ) : ℂ := Complex.exp (Complex.I * ((∑ a, ω a * θ a : ℝ) : ℂ))
def CptLE (ε : Fin n → Bool) (ω Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n × Fin n → ℕ, Λ - ω = ∑ x ∈ cptPairs ε, (c x : ℝ) • root x.1 x.2
section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure IsUnitaryRepOn (Γ : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) : Prop where
  map_one : σ 1 = 1
  map_mul : ∀ g ∈ Γ, ∀ g' ∈ Γ, σ (g * g') = σ g * σ g'
  norm_map : ∀ g ∈ Γ, ∀ v, ‖σ g v‖ = ‖v‖
  cont : ∀ v, ContinuousOn (fun g => σ g v) Γ
def weightSpace (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) :
    Submodule ℂ H where
  carrier := {v | ∀ θ : Fin n → ℝ, σ (torus θ) v = wtChar ω θ • v}
  add_mem' := by
    intro a b ha hb θ
    rw [map_add, ha θ, hb θ, smul_add]
  zero_mem' := by intro θ; simp
  smul_mem' := by
    intro c v hv θ
    rw [map_smul, hv θ, smul_comm]
def IsWeightVector (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) (v : H) : Prop :=
  v ≠ 0 ∧ v ∈ weightSpace σ ω
def KStable (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (S : Submodule ℂ H) : Prop :=
  ∀ k ∈ grpK ε, ∀ v ∈ S, σ k v ∈ S
structure IsKType (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (S : Submodule ℂ H) (Λ : Fin n → ℝ) : Prop where
  finDim : FiniteDimensional ℂ S
  stable : KStable ε σ S
  irred : ∀ S' : Submodule ℂ H, S' ≤ S → KStable ε σ S' → S' = ⊥ ∨ S' = S
  exists_highest : ∃ v ∈ S, IsWeightVector σ Λ v
  le_highest : ∀ ω : Fin n → ℝ, ∀ v ∈ S, IsWeightVector σ ω v → CptLE ε ω Λ
def isotypic (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (ν : Fin n → ℝ) : Submodule ℂ H :=
  sSup {S : Submodule ℂ H | IsKType ε σ S ν}
def isotypicWeight (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (ν ω : Fin n → ℝ) : Submodule ℂ H :=
  isotypic ε σ ν ⊓ weightSpace σ ω
def lowestIsotypic (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (μ : Fin n → ℝ) : Submodule ℂ H :=
  isotypic ε σ (lowestWeight ε μ)
def IsLowestTypeUnit (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (μ : Fin n → ℝ) (w : H) : Prop :=
  w ∈ lowestIsotypic ε σ μ ∧ ‖w‖ = 1
def IsLowestVector (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (μ : Fin n → ℝ) (w : H) : Prop :=
  w ∈ isotypicWeight ε σ (lowestWeight ε μ) (lowestWeight ε μ) ∧ ‖w‖ = 1
end Rep
def rhoU (k : ℕ) : Fin k → ℝ := fun i => ((k : ℝ) - 1) / 2 - (i : ℕ)
structure IsCompactIrrep {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H) (u : Fin k → ℝ) : Prop where
  param : IsHCParam u
  rep : IsUnitaryRepOn (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) π
  type : IsKType (fun _ => true) π ⊤ (u - rhoU k)
def detRep (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ →L[ℂ] ℂ := g.det • (1 : ℂ →L[ℂ] ℂ)
end GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData


