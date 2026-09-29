-- Prove2me | Definitions.Def_Deformations_ContinuousSMulDiscrete
-- name    : Deformations_ContinuousSMulDiscrete
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/456dcccc-3d51-5c5f-b926-33ac76dd876f
-- title:
--   Continuity of actions on discrete sets: open-orbit-fibre condition
-- statement:
--   This module introduces a single-field proposition class [`ContinuousSMulDiscrete G M`](../def/Deformations_ContinuousSMulDiscrete.html#L7), for a type $G$ carrying a topology and acting on a bare type $M$ by scalar multiplication with no topology on $M$ required. Its only field `isOpen_smul_eq` asserts that for all $x, y : M$ the set $\{g : G \mid g \cdot x = y\}$ is open in $G$; that is, each fibre of each orbit map $g \mapsto g \cdot x$ over a point of $M$ is open. This is exactly continuity of the action when $M$ is given the discrete topology, and the point of the formulation is that it can be imposed on an $M$ that already carries some other (possibly non-discrete) topology.
--
--   Four auxiliary results pin the notion down. [`continuousSMulDiscrete_iff`](../def/Deformations_ContinuousSMulDiscrete.html#L10) shows that if $M$ is endowed with a topology which is discrete, then [`ContinuousSMulDiscrete G M`](../def/Deformations_ContinuousSMulDiscrete.html#L7) holds if and only if the joint action map $G \times M \to M$ is continuous in Mathlib's sense (`ContinuousSMul G M`); the two directions are recorded separately as a low-priority instance producing `ContinuousSMul` from the class and as [`ContinuousSMulDiscrete.of_continuousSMul`](../def/Deformations_ContinuousSMulDiscrete.html#L23) in the opposite direction. [`continuousSMulDiscrete_iff_isOpen_stabilizer`](../def/Deformations_ContinuousSMulDiscrete.html#L27) treats the case of a group $G$ with continuous multiplication acting on $M$: there the class is equivalent to openness of the stabiliser subgroup $\mathrm{Stab}_G(x)$, as a subset of $G$, for every $x : M$, the proof translating an arbitrary fibre $\{g \mid g \cdot x = y\}$ to a stabiliser by left translation (the empty fibre being open trivially). The forward implication alone is isolated as [`ContinuousSMulDiscrete.isOpen_stabilizer`](../def/Deformations_ContinuousSMulDiscrete.html#L37), which needs no continuity of multiplication on $G$.
--
--   **Relation to Mathlib.** Mathlib has `ContinuousSMul`, which requires a topology on the acted-upon type; [`ContinuousSMulDiscrete`](../def/Deformations_ContinuousSMulDiscrete.html#L7) is the project's variant that dispenses with it, and the module supplies the comparison lemmas and an instance `ContinuousSMul` whenever the given topology on $M$ is discrete.
--
--   **Where it is used.** The condition packaged here is the usual continuity requirement for an action of a profinite group, such as a Galois group, on a discrete module, stated so that it may be used for modules carrying an unrelated topology; it belongs to the topological infrastructure for Galois deformation theory.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Deformations/RepresentationTheory/ContinuousSMulDiscrete.lean` — © 2025 Andrew Yang; authors: Andrew Yang). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_ContinuousSMulDiscrete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

variable {G M : Type*} [TopologicalSpace G] [SMul G M]

class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isOpen_smul_eq (G) (x y : M) : IsOpen { g : G | g • x = y }

lemma continuousSMulDiscrete_iff [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMulDiscrete G M ↔ ContinuousSMul G M := by
  refine ⟨fun H ↦ ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  · convert_to IsOpen (⋃ x, { g : G | g • x = y } ×ˢ {x})
    · ext; simp
    · exact isOpen_iUnion fun _ ↦
        .prod (ContinuousSMulDiscrete.isOpen_smul_eq _ _ _) (isOpen_discrete _)
  · exact ((isOpen_discrete {y}).preimage continuous_smul).preimage (Continuous.prodMk_left x)

instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]

lemma ContinuousSMulDiscrete.of_continuousSMul [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul G M] : ContinuousSMulDiscrete G M := by
  rwa [continuousSMulDiscrete_iff]

lemma continuousSMulDiscrete_iff_isOpen_stabilizer {G M : Type*} [TopologicalSpace G]
    [Group G] [ContinuousMul G] [MulAction G M] :
    ContinuousSMulDiscrete G M ↔ ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun H x ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ _ _, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  obtain h | ⟨g, rfl⟩ := Set.eq_empty_or_nonempty {g : G | g • x = y}
  · exact h ▸ isOpen_empty
  · convert (H x).preimage (Homeomorph.mulLeft g⁻¹).continuous using 1
    ext g'
    simp [mul_smul, inv_smul_eq_iff]

lemma ContinuousSMulDiscrete.isOpen_stabilizer (G : Type*) {M : Type*} [TopologicalSpace G]
    [Group G] [MulAction G M] [ContinuousSMulDiscrete G M] (x : M) :
      IsOpen (MulAction.stabilizer G x : Set G) := ContinuousSMulDiscrete.isOpen_smul_eq _ _ _

end


