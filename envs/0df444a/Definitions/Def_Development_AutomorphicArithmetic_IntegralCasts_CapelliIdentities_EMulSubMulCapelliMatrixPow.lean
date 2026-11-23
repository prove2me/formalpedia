-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:42.038357+00:00
-- url     : https://prove2.me/theorems/05fa2ad5-afd6-4a5e-8e05-a964320693a9
-- title:
--   EMul Sub Mul Capelli Matrix Pow
-- statement:
--   Definitions and structural lemmas for EMul Sub Mul Capelli Matrix Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EMulSubMulCapelliMatrixPow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk36.gl :
    Nat → Type :=
    fun (n : Nat) ↦ Matrix (Fin n) (Fin n) Complex
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk36.U :
    Nat → Type :=
    fun (n : Nat) ↦
      @UniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
        (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
        (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
          (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
          Complex.commRing
          (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
            (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
            (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
noncomputable def UpperTheory.Reformulated.B.Qk36.E :
    {n : Nat} → Prod (Fin n) (Fin n) → UpperTheory.Reformulated.B.Qk36.gl n :=
    fun {n : Nat} (a : Prod (Fin n) (Fin n)) ↦
      @Matrix.single (Fin n) (Fin n) Complex (instDecidableEqFin n) (instDecidableEqFin n) Complex.instZero
        (@Prod.fst (Fin n) (Fin n) a) (@Prod.snd (Fin n) (Fin n) a)
        (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
noncomputable def UpperTheory.Reformulated.B.Qk36.e :
    {n : Nat} → Prod (Fin n) (Fin n) → UpperTheory.Reformulated.B.Qk36.U n :=
    fun {n : Nat} (a : Prod (Fin n) (Fin n)) ↦
      @DFunLike.coe
        (@LieHom Complex (UpperTheory.Reformulated.B.Qk36.gl n)
          (@UniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
              Complex.commRing
              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
          Complex.commRing
          (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
            (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
          (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
            (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
            Complex.commRing
            (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
              (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
              (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
          (@LieRing.ofAssociativeRing
            (@UniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
            (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
          (@LieAlgebra.ofAssociativeAlgebra
            (@UniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
            (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
            Complex Complex.commRing
            (@instAlgebraUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))
        (UpperTheory.Reformulated.B.Qk36.gl n)
        (fun (x : UpperTheory.Reformulated.B.Qk36.gl n) ↦
          @UniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
              Complex.commRing
              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
        (@LieHom.instFunLike Complex (UpperTheory.Reformulated.B.Qk36.gl n)
          (@UniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
            (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
            (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
              (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
              Complex.commRing
              (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
          Complex.commRing
          (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
            (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
          (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
            (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
            Complex.commRing
            (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
              (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
              (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
          (@LieRing.ofAssociativeRing
            (@UniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
            (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing))))))
          (@LieAlgebra.ofAssociativeAlgebra
            (@UniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
            (@instRingUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
            Complex Complex.commRing
            (@instAlgebraUniversalEnvelopingAlgebra Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
              (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
              (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
                (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
                Complex.commRing
                (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
                  (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
                  (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))))
        (@UniversalEnvelopingAlgebra.ι Complex (UpperTheory.Reformulated.B.Qk36.gl n) Complex.commRing
          (@LieRing.ofAssociativeRing (UpperTheory.Reformulated.B.Qk36.gl n)
            (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing))
          (@LieAlgebra.ofAssociativeAlgebra (UpperTheory.Reformulated.B.Qk36.gl n)
            (@Matrix.instRing (Fin n) Complex (Fin.fintype n) (instDecidableEqFin n) Complex.instRing) Complex
            Complex.commRing
            (@Matrix.instAlgebra (Fin n) Complex Complex (Fin.fintype n) (instDecidableEqFin n)
              (@CommRing.toCommSemiring Complex Complex.commRing) (@Ring.toSemiring Complex Complex.instRing)
              (@Algebra.id Complex (@CommRing.toCommSemiring Complex Complex.commRing)))))
        (@UpperTheory.Reformulated.B.Qk36.E n a)
noncomputable def UpperTheory.Reformulated.B.Qk36.capelliMatrix :
    {n : Nat} → Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n) :=
    fun {n : Nat} (i j : Fin n) ↦ @UpperTheory.Reformulated.B.Qk36.e n (@Prod.mk (Fin n) (Fin n) i j)


