-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:19.989582+00:00
-- url     : https://prove2.me/theorems/08288f9d-1a72-4a92-a609-3e587c463bc8
-- title:
--   Det Emb Unitri A
-- statement:
--   Definitions and structural lemmas for Det Emb Unitri A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DetEmbUnitriA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
theorem UpperTheory.Reformulated.B.Qe13.aux1 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ),
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R)
          (0 : Matrix (Fin (1 : ℕ)) (Fin n) R) (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        (1 : Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R) := by
  intro R _ n
  exact Matrix.fromBlocks_one
theorem UpperTheory.Reformulated.B.Qe13.aux2 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ) (A B : Matrix (Fin n) (Fin n) R),
      Matrix.fromBlocks (A * B) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
          (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) *
          Matrix.fromBlocks B (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) := by
  intro R _ n A B
  rw [Matrix.fromBlocks_multiply]
  simp
noncomputable def UpperTheory.Reformulated.B.Qe13.blkHom :
    (R : Type) →
      [inst : CommRing R] → (n : ℕ) → Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R :=
    fun (R : Type) [CommRing R] (n : ℕ) ↦
      {
        toFun := fun (A : Matrix (Fin n) (Fin n) R) ↦
          Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R),
        map_one' := UpperTheory.Reformulated.B.Qe13.aux1 R n, map_mul' := UpperTheory.Reformulated.B.Qe13.aux2 R n :
        Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R }
noncomputable def UpperTheory.Reformulated.B.Qe13.embGL :
    (R : Type) → [inst : CommRing R] → (n N : ℕ) → n + (1 : ℕ) = N → GL (Fin n) R →* GL (Fin N) R :=
    fun (R : Type) [CommRing R] (n N : ℕ) (h : n + (1 : ℕ) = N) ↦
      Units.map
        ((↑(↑(Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))) :
                    Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →ₐ[R] Matrix (Fin N) (Fin N) R).toRingHom :
              Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →* Matrix (Fin N) (Fin N) R).comp
          (UpperTheory.Reformulated.B.Qe13.blkHom R n))


