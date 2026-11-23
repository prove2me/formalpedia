-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:15.394543+00:00
-- url     : https://prove2.me/theorems/6e3d93a9-4a07-4cfe-9eaf-95b1c93fb535
-- title:
--   Smooth On Group Sum
-- statement:
--   Definitions and structural lemmas for Smooth On Group Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SmoothOnGroupSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qh27.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
noncomputable def UpperTheory.Reformulated.B.Qh27.inUJ :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @Eq (Matrix (Fin n) (Fin n) Complex)
        (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
            Complex.instAddCommMonoid)
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose (Fin n) (Fin n) Complex
              (@InvolutiveStar.toStar Complex
                (@StarAddMonoid.toInvolutiveStar Complex
                  (@AddCommMonoid.toAddMonoid Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              g)
            (@UpperTheory.Reformulated.B.Qh27.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.Qh27.Jm n ε)
noncomputable def UpperTheory.Reformulated.B.Qh27.SmoothOnG :
    {n : Nat} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) Complex → Complex) → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) Complex → Complex) ↦
      ∀ (g₀ : Matrix (Fin n) (Fin n) Complex),
        @UpperTheory.Reformulated.B.Qh27.inUJ n ε g₀ →
          ∃ (U : Set (Matrix (Fin n) (Fin n) Complex)) (F : Matrix (Fin n) (Fin n) Complex → Complex),
            And
              (@IsOpen (Matrix (Fin n) (Fin n) Complex)
                (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
                  (@UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
                U)
              (And
                (@Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
                  (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) U g₀)
                (And
                  (@ContDiffOn Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField)
                    (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.normedAddCommGroup (Fin n) (Fin n) Complex (Fin.fintype n) (Fin.fintype n)
                      Complex.instNormedAddCommGroup)
                    (@Matrix.normedSpace Real (Fin n) (Fin n) Complex (Fin.fintype n) (Fin.fintype n)
                      (@NontriviallyNormedField.toNormedField Real
                        (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField))
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                        instInnerProductSpaceRealComplex))
                    Complex Complex.instNormedAddCommGroup
                    (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      instInnerProductSpaceRealComplex)
                    (@WithTop.some ENat (@Top.top ENat instTopENat)) F U)
                  (∀ (g : Matrix (Fin n) (Fin n) Complex),
                    @Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
                        (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) U g →
                      @UpperTheory.Reformulated.B.Qh27.inUJ n ε g → @Eq Complex (f g) (F g))))


