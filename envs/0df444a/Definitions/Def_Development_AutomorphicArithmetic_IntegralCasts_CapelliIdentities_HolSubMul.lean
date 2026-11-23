-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HolSubMul
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HolSubMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:46.23706+00:00
-- url     : https://prove2.me/theorems/eb34825e-8606-4be8-9679-18d16d25dcb6
-- title:
--   Hol Sub Mul
-- statement:
--   Definitions and structural lemmas for Hol Sub Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HolSubMul.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe28.FDSec :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] →
            {r : Nat} → {Comp : Type} → (Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r) → Type :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
        [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {r : Nat} {Comp : Type}
        (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r) ↦
      (c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex
noncomputable def UpperTheory.Reformulated.B.Qe28.IsHolCusp :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] →
            {r : Nat} →
              {Comp : Type} →
                (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r) →
                  ((c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r) →
                    @UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X → Prop :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
        [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {r : Nat} {Comp : Type}
        (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r)
        (la : (c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r)
        (P : @UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) ↦
      ∀ (c : Comp),
        @Membership.mem
          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
          (Set (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex))
          (@Set.instMembership
            (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex))
          (@ReciprocityTheory.ChartRestriction.G.FD.Data.SS E inst inst_1 inst_2 r (X c) (la c)) (P c)
noncomputable def UpperTheory.Reformulated.B.Qe28.holSub :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] →
            {r : Nat} →
              {Comp : Type} →
                (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r) →
                  ((c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r) →
                    @Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                      (@Pi.addCommMonoid Comp
                        (fun (c : Comp) ↦
                          @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                            Complex)
                        fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      (@Pi.module Comp
                        (fun (c : Comp) ↦
                          @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                            Complex)
                        Complex Complex.instSemiring
                        (fun (i : Comp) ↦
                          @Pi.addCommMonoid
                            (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                            (fun
                                (a :
                                  @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                    r) ↦
                              Complex)
                            fun
                              (i :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex.instAddCommMonoid)
                        fun (i : Comp) ↦
                        @Pi.Function.module
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          Complex Complex Complex.instSemiring Complex.instAddCommMonoid
                          (@Semiring.toModule Complex Complex.instSemiring)) :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
        [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {r : Nat} {Comp : Type}
        (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r)
        (la : (c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r) ↦
      @Submodule.span Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
        (@Pi.addCommMonoid Comp
          (fun (c : Comp) ↦
            @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
          fun (i : Comp) ↦
          @Pi.addCommMonoid (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
            (fun (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦ Complex)
            fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
            Complex.instAddCommMonoid)
        (@Pi.module Comp
          (fun (c : Comp) ↦
            @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
          Complex Complex.instSemiring
          (fun (i : Comp) ↦
            @Pi.addCommMonoid (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
              (fun (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                Complex)
              fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
              Complex.instAddCommMonoid)
          fun (i : Comp) ↦
          @Pi.Function.module (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
            Complex Complex Complex.instSemiring Complex.instAddCommMonoid
            (@Semiring.toModule Complex Complex.instSemiring))
        (@Set.ofPred (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
          fun (P : @UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) ↦
          @UpperTheory.Reformulated.B.Qe28.IsHolCusp E inst inst_1 inst_2 r Comp X la P)


