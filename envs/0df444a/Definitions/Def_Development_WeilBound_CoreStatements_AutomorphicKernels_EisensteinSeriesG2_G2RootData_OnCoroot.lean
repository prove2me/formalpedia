-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2RootData_OnCoroot
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2RootData_OnCoroot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:38:16.692686+00:00
-- url     : https://prove2.me/theorems/30c00f24-75bd-4548-b018-d214d0d44241
-- title:
--   On Coroot
-- statement:
--   Definitions and structural lemmas for On Coroot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2RootData/OnCoroot.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace SiegelEisensteinSeries.BRoad
open Filter Topology
structure Datum (G : Type*) [Group G] (r : ℕ) where
  Γ : Subgroup G
  Bo : Subgroup G
  K : Subgroup G
  Pa : Fin r → Subgroup G
  Hv : G → Fin r → ℝ
  ht : G → ℝ
  rho : Fin r → ℝ
  root : Fin r → Fin r → ℝ
  coroot : Fin r → Fin r → ℝ
variable {G : Type*} [Group G] {r : ℕ}
def cpair (lam : Fin r → ℂ) (x : Fin r → ℝ) : ℂ := ∑ j, lam j * (x j : ℂ)
def onCoroot (lam : Fin r → ℂ) (c : Fin r → ℝ) : ℂ := cpair lam c
namespace Datum
variable (D : Datum G r)
structure IsGood [TopologicalSpace G] : Prop where
  iwa : ∀ g : G, ∃ b ∈ D.Bo, ∃ k ∈ D.K, g = b * k
  cpt : IsCompact (D.K : Set G)
  hv_cont : Continuous D.Hv
  hv_right : ∀ g, ∀ k ∈ D.K, D.Hv (g * k) = D.Hv g
  hv_mul : ∀ b ∈ D.Bo, ∀ g, D.Hv (b * g) = D.Hv b + D.Hv g
  hv_rat : ∀ γ ∈ D.Γ ⊓ D.Bo, D.Hv γ = 0
  ht_cont : Continuous D.ht
  ht_ge : ∀ g, 1 ≤ D.ht g
  pa_ge : ∀ a, D.Bo ≤ D.Pa a
abbrev Cos := Quotient (QuotientGroup.rightRel (D.Bo.subgroupOf D.Γ))
abbrev CosA (a : Fin r) := Quotient (QuotientGroup.rightRel (D.Bo.subgroupOf (D.Γ ⊓ D.Pa a)))
abbrev CosP (a : Fin r) := Quotient (QuotientGroup.rightRel ((D.Pa a).subgroupOf D.Γ))
def term (φ : G → ℂ) (lam : Fin r → ℂ) (g : G) : ℂ :=
  Complex.exp (cpair (lam + fun j => (D.rho j : ℂ)) (D.Hv g)) * φ g
def eisB (φ : G → ℂ) (lam : Fin r → ℂ) (g : G) : ℂ := ∑' q : D.Cos, D.term φ lam ((Quotient.out q).1 * g)
def eisA (a : Fin r) (φ : G → ℂ) (lam : Fin r → ℂ) (g : G) : ℂ :=
  ∑' q : D.CosA a, D.term φ lam ((Quotient.out q).1 * g)
def refl (a : Fin r) (lam : Fin r → ℂ) : Fin r → ℂ := fun j => lam j - onCoroot lam (D.coroot a) * (D.root a j : ℂ)
def wordAct (w : List (Fin r)) (lam : Fin r → ℂ) : Fin r → ℂ := w.foldr (fun a l => D.refl a l) lam
def cone (R : ℝ) : Set (Fin r → ℝ) := {x | ∀ a, R < ∑ j, x j * D.coroot a j}
structure IsSec [TopologicalSpace G] (χ : G → ℂ) (φ : G → ℂ) : Prop where
  cont : Continuous φ
  equiv : ∀ b ∈ D.Bo, ∀ g, φ (b * g) = χ b * φ g
  unit : ∀ b ∈ D.Bo, ‖χ b‖ = 1
  rat : ∀ γ ∈ D.Γ ⊓ D.Bo, χ γ = 1
  bdd : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M
end Datum
end SiegelEisensteinSeries.BRoad


