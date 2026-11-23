-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTower
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:19.111872+00:00
-- url     : https://prove2.me/theorems/411da9c8-9cdb-4eff-a813-d1ddc32585f1
-- title:
--   Exists Square Presentation Of Tower
-- statement:
--   Definitions and structural lemmas for Exists Square Presentation Of Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquarePresentationOfTower.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory.SquareTower
open MvPolynomial
noncomputable def presOf {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {s : ℕ}
    (φ : MvPolynomial (Fin s) R →ₐ[R] S) (g : Fin s → MvPolynomial (Fin s) R)
    (hs : Function.Surjective φ) (hk : RingHom.ker φ = Ideal.span (Set.range g)) :
    Algebra.Presentation R S (Fin s) (Fin s) :=
  have he : MvPolynomial.aeval (fun i => φ (X i)) = φ := MvPolynomial.algHom_ext (fun i => aeval_X _ _)
  { toGenerators := Algebra.Generators.ofSurjective (fun i => φ (X i)) (by rw [he]; exact hs)
    relation := g
    span_range_relation_eq_ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, ← hk]
      change RingHom.ker φ = RingHom.ker (MvPolynomial.aeval (fun i => φ (X i)))
      rw [he] }
end GlobalTheory.SquareTower


