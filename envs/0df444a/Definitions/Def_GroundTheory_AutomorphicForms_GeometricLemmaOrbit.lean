-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaOrbit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:05.331157+00:00
-- url     : https://prove2.me/theorems/7cf65d65-295f-433a-a5fc-949894dccdce
-- title:
--   Geometric Lemma Orbit
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Topology Set DoubleCoset
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SigmaCompactSpace G]
section Action
variable (P Q : Subgroup G) (x : G)
@[instance_reducible]
def doubleCosetAction : MulAction (P × Q) (doubleCoset x (P : Set G) Q) where
  smul pq g := ⟨(pq.1 : G) * g * (pq.2 : G)⁻¹, by
    obtain ⟨p, hp, q, hq, h⟩ := mem_doubleCoset.1 g.2
    refine mem_doubleCoset.2 ⟨pq.1 * p, P.mul_mem pq.1.2 hp, q * (pq.2 : G)⁻¹,
      Q.mul_mem hq (Q.inv_mem pq.2.2), ?_⟩
    rw [h]
    group⟩
  one_smul g := Subtype.ext (by
    show ((1 : P × Q).1 : G) * g * ((1 : P × Q).2 : G)⁻¹ = g
    simp)
  mul_smul a b g := Subtype.ext (by
    show ((a * b).1 : G) * g * ((a * b).2 : G)⁻¹ =
      (a.1 : G) * ((b.1 : G) * g * (b.2 : G)⁻¹) * (a.2 : G)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
    group)
end Action
variable {P Q : Subgroup G}
end Parabolic
end GroundTheory.Automorphic


