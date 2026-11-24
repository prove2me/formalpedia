-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StrictlyUpperRank
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StrictlyUpperRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:32.489848+00:00
-- url     : https://prove2.me/theorems/56d89e25-332e-41f8-9351-3e10c7134b5f
-- title:
--   Strictly Upper Rank
-- statement:
--   Definitions and structural lemmas for Strictly Upper Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/StrictlyUpperRank.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.StrictlyUpperRank.IsStrictUpper.{u_1, u_2} :
    {𝕜 : Type u_1} → [RCLike 𝕜] → {n : Type u_2} → [LinearOrder n] → Matrix n n 𝕜 → Prop :=
    fun {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_1 : LinearOrder n] (X : Matrix n n 𝕜) ↦
      ∀ (i j : n),
        @LE.le n
            (@Preorder.toLE n
              (@PartialOrder.toPreorder n
                (@SemilatticeInf.toPartialOrder n
                  (@Lattice.toSemilatticeInf n (@DistribLattice.toLattice n (@instDistribLatticeOfLinearOrder n inst_1))))))
            j i →
          @Eq 𝕜 (X i j)
            (@OfNat.ofNat 𝕜 (nat_lit 0)
              (@Zero.toOfNat0 𝕜
                (@MulZeroClass.toZero 𝕜
                  (@instMulZeroClassOfSemiring 𝕜
                    (@DivisionSemiring.toSemiring 𝕜
                      (@Semifield.toDivisionSemiring 𝕜
                        (@Field.toSemifield 𝕜
                          (@NormedField.toField 𝕜
                            (@DenselyNormedField.toNormedField 𝕜 (@RCLike.toDenselyNormedField 𝕜 inst))))))))))
noncomputable def UpperTheory.Reformulated.B.StrictlyUpperRank.rankBelow.{u_2} :
    {n : Type u_2} → [Fintype n] → [LinearOrder n] → n → Nat :=
    fun {n : Type u_2} [Fintype n] [inst_1 : LinearOrder n] (i : n) ↦
      @Finset.card n
        {x : n |
          @LT.lt n
            (@Preorder.toLT n
              (@PartialOrder.toPreorder n
                (@SemilatticeInf.toPartialOrder n
                  (@Lattice.toSemilatticeInf n (@DistribLattice.toLattice n (@instDistribLatticeOfLinearOrder n inst_1))))))
            x i}


