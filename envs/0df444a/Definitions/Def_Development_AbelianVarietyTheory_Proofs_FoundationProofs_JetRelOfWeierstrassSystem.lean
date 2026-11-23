-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:34.803776+00:00
-- url     : https://prove2.me/theorems/b56d663c-c5c7-42e4-bec1-b92a3e02e46e
-- title:
--   Jet Rel Of Weierstrass System
-- statement:
--   Definitions and structural lemmas for Jet Rel Of Weierstrass System, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.JetConj
def JetRel (S : Subring (ℂ × ℂ)) (f g : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧ ∀ n, (iteratedDeriv n f 0, iteratedDeriv n g 0) ∈ S
def IsFieldGraph (S : Subring (ℂ × ℂ)) : Prop :=
  (∀ a b, (a, b) ∈ S → (a = 0 ↔ b = 0)) ∧ ∀ a b, (a, b) ∈ S → (a⁻¹, b⁻¹) ∈ S
noncomputable def graph (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Subring (ℂ × ℂ) :=
  (RingHom.prod (M.val : M →+* ℂ) (ρ : M →+* ℂ)).range
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
lemma JetRel.deriv (H : JetRel S f f') : JetRel S (deriv f) (deriv f') := by
  obtain ⟨hf, hf', hd⟩ := H
  refine ⟨hf.deriv, hf'.deriv, fun n => ?_⟩
  rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
  exact hd (n + 1)
end GlobalTheory.JetConj


