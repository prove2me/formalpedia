-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:14.55779+00:00
-- url     : https://prove2.me/theorems/2fc9855d-e462-4bcd-8406-939143a1fec8
-- title:
--   Defs Rep
-- statement:
--   Definitions and structural lemmas for Defs Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DefsRep.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def Jm (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else -1
def inUJ (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  gᴴ * Jm ε * g = Jm ε
def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | inUJ ε g}
def Kset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Jm ε = Jm ε * g}
def inG (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Xᴴ * Jm ε + Jm ε * X = 0
def inK (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = Jm ε * X
def inP (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = -(Jm ε * X)
section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsURepOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (σ 1 = 1 ∧ ∀ a ∈ G, ∀ b ∈ G, σ (a * b) = (σ a).comp (σ b)) ∧
    (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧ ∀ v : H, ContinuousOn (fun g => σ g v) G
def actM {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ M :=
  ∑ a, ∑ b, X a b • E a b
structure IsDerivedOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) : Prop where
  glRep : IsGlRep E
  kStable : ∀ k ∈ Kset ε, ∀ v ∈ D, σ k v ∈ D
  deriv : ∀ X, inG ε X → ∀ v : D,
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ((actM E X v : D) : H) 0
end Rep
end ReciprocityTheory.ChartRestriction.DS


