-- Prove2me | Definitions.Def_Yukon_d0df5d5d970b1a61cfb95c13
-- name    : Yukon_d0df5d5d970b1a61cfb95c13
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T15:05:59.628248+00:00
-- url     : https://prove2.me/theorems/17da3598-f1f2-4876-b931-782bbdeda673
-- title:
--   Probability sampling lemmas
-- statement:
--   Indicator-weighted PMF sum and invariance of uniform sampling under equivalence. Exported as ordinary Lean terms from the original ArkLib declarations, including their generated supporting lemma. Native Lean checks confirm the original theorem types and permitted axioms. No custom notation or elaborator code is included.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Probability/Notation.lean
--
--   yukon-proof-operation:d0df5d5d970b1a61cfb95c13332b3fe55cb213eaa44e01cac9808eac1d7e35a2
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZDBkZjVkNWQ5NzBiMWE2MWNmYjk1YzEzMzMyYjNmZTU1Y2IyMTNlYWE0NGUwMWNhYzk4MDhlYWMxZDdlMzVhMiIsImhhc2giOiI4OGRmN2I5Y2QwZDQyNjRmNGU1MDY0OTEwOTQyNzViMWU4YjYxYzU2Y2YyZDk0ZjMyZmExZGE2ZTk2Yzc3M2ExIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9kMGRmNWQ1ZDk3MGIxYTYxY2ZiOTVjMTMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši
-/
import Mathlib
set_option backward.isDefEq.respectTransparency.types false
theorem ProbabilityTheory.Pr_eq_tsum_indicator._simp_1_3 : ∀ {a b : Prop}, @Eq.{1} Prop (@Eq.{1} Prop a b) (Iff a b) :=
fun {a b : Prop} => @propext (@Eq.{1} Prop a b) (Iff a b) (@eq_iff_iff a b)
theorem ProbabilityTheory.Pr_eq_tsum_indicator : ∀ {α : Type} (p : PMF.{0} α) (P : α → Prop)
  [inst : @DecidablePred.{1} α P],
  @Eq.{1} ENNReal
    (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
      (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) α Prop p fun (a : α) =>
        @Pure.pure.{0, 0} PMF.{0}
          (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop (P a))
      True)
    (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
      (fun (a : α) =>
        @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
          (@instHMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          (@DFunLike.coe.{1, 1, 1} (PMF.{0} α) α (fun (x : α) => ENNReal) (@PMF.instFunLike.{0} α) p a)
          (@ite.{1} ENNReal (P a) (inst a)
            (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
            (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
      (SummationFilter.unconditional.{0} α)) :=
fun {α : Type} (p : PMF.{0} α) (P : α → Prop) [inst : @DecidablePred.{1} α P] =>
  @of_eq_true
    (@Eq.{1} ENNReal
      (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
        (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) α Prop p fun (a : α) =>
          @Pure.pure.{0, 0} PMF.{0}
            (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop (P a))
        True)
      (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
        (fun (a : α) =>
          @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
            (@Subtype.val.{1} (α → ENNReal)
              (fun (f : α → ENNReal) =>
                @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                  (SummationFilter.unconditional.{0} α))
              p a)
            (@ite.{1} ENNReal (P a) (inst a)
              (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
              (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
        (SummationFilter.unconditional.{0} α)))
    (@Eq.trans.{1} Prop
      (@Eq.{1} ENNReal
        (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
          (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) α Prop p fun (a : α) =>
            @Pure.pure.{0, 0} PMF.{0}
              (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop (P a))
          True)
        (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
          (fun (a : α) =>
            @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (@Subtype.val.{1} (α → ENNReal)
                (fun (f : α → ENNReal) =>
                  @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (SummationFilter.unconditional.{0} α))
                p a)
              (@ite.{1} ENNReal (P a) (inst a)
                (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
          (SummationFilter.unconditional.{0} α)))
      (@Eq.{1} ENNReal
        (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
          (fun (a : α) =>
            @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (@Subtype.val.{1} (α → ENNReal)
                (fun (f : α → ENNReal) =>
                  @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (SummationFilter.unconditional.{0} α))
                p a)
              (@ite.{1} ENNReal (P a) (inst a)
                (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
          (SummationFilter.unconditional.{0} α))
        (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
          (fun (a : α) =>
            @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (@Subtype.val.{1} (α → ENNReal)
                (fun (f : α → ENNReal) =>
                  @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (SummationFilter.unconditional.{0} α))
                p a)
              (@ite.{1} ENNReal (P a) (inst a)
                (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
          (SummationFilter.unconditional.{0} α)))
      True
      (@congrFun'.{1, 1} ENNReal Prop
        (@Eq.{1} ENNReal
          (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
            (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) α Prop p fun (a : α) =>
              @Pure.pure.{0, 0} PMF.{0}
                (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop (P a))
            True))
        (@Eq.{1} ENNReal
          (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
            (fun (a : α) =>
              @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (@Subtype.val.{1} (α → ENNReal)
                  (fun (f : α → ENNReal) =>
                    @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                      (SummationFilter.unconditional.{0} α))
                  p a)
                (@ite.{1} ENNReal (P a) (inst a)
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
            (SummationFilter.unconditional.{0} α)))
        (@congrArg.{1, 1} ENNReal (ENNReal → Prop)
          (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
            (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) α Prop p fun (a : α) =>
              @Pure.pure.{0, 0} PMF.{0}
                (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop (P a))
            True)
          (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
            (fun (a : α) =>
              @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (@Subtype.val.{1} (α → ENNReal)
                  (fun (f : α → ENNReal) =>
                    @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                      (SummationFilter.unconditional.{0} α))
                  p a)
                (@ite.{1} ENNReal (P a) (inst a)
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
            (SummationFilter.unconditional.{0} α))
          (@Eq.{1} ENNReal)
          (@congrFun'.{1, 1} (SummationFilter.{0} α) ENNReal
            (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace fun (a : α) =>
              @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (@Subtype.val.{1} (α → ENNReal)
                  (fun (f : α → ENNReal) =>
                    @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                      (SummationFilter.unconditional.{0} α))
                  p a)
                (@ite.{1} ENNReal (@Eq.{1} Prop True (P a)) (Classical.propDecidable (@Eq.{1} Prop True (P a)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
            (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace fun (a : α) =>
              @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (@Subtype.val.{1} (α → ENNReal)
                  (fun (f : α → ENNReal) =>
                    @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                      (SummationFilter.unconditional.{0} α))
                  p a)
                (@ite.{1} ENNReal (P a) (inst a)
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
            (@congrArg.{1, 1} ((a : α) → ENNReal)
              ((L : optParam.{1} (SummationFilter.{0} α) (SummationFilter.unconditional.{0} α)) → ENNReal)
              (fun (a : α) =>
                @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (@Subtype.val.{1} (α → ENNReal)
                    (fun (f : α → ENNReal) =>
                      @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                        (SummationFilter.unconditional.{0} α))
                    p a)
                  (@ite.{1} ENNReal (@Eq.{1} Prop True (P a)) (Classical.propDecidable (@Eq.{1} Prop True (P a)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
              (fun (a : α) =>
                @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (@Subtype.val.{1} (α → ENNReal)
                    (fun (f : α → ENNReal) =>
                      @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                        (SummationFilter.unconditional.{0} α))
                    p a)
                  (@ite.{1} ENNReal (P a) (inst a)
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
              (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace)
              (@funext.{1, 1} α (fun (x : α) => ENNReal)
                (fun (x : α) =>
                  @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (@Subtype.val.{1} (α → ENNReal)
                      (fun (f : α → ENNReal) =>
                        @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                          (SummationFilter.unconditional.{0} α))
                      p x)
                    (@ite.{1} ENNReal (@Eq.{1} Prop True (P x)) (Classical.propDecidable (@Eq.{1} Prop True (P x)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
                (fun (x : α) =>
                  @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (@Subtype.val.{1} (α → ENNReal)
                      (fun (f : α → ENNReal) =>
                        @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                          (SummationFilter.unconditional.{0} α))
                      p x)
                    (@ite.{1} ENNReal (P x) (inst x)
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
                fun (a : α) =>
                @congrArg.{1, 1} ENNReal ENNReal
                  (@ite.{1} ENNReal (@Eq.{1} Prop True (P a)) (Classical.propDecidable (@Eq.{1} Prop True (P a)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                  (@ite.{1} ENNReal (P a) (inst a)
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (@Subtype.val.{1} (α → ENNReal)
                      (fun (f : α → ENNReal) =>
                        @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                          (SummationFilter.unconditional.{0} α))
                      p a))
                  (@ite_congr.{1} ENNReal (@Eq.{1} Prop True (P a)) (P a)
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
                    (Classical.propDecidable (@Eq.{1} Prop True (P a))) (inst a)
                    (@Eq.trans.{1} Prop (@Eq.{1} Prop True (P a)) (Iff True (P a)) (P a)
                      (@ProbabilityTheory.Pr_eq_tsum_indicator._simp_1_3 True (P a)) (true_iff (P a)))
                    (fun (a : P a) =>
                      @Eq.refl.{1} ENNReal
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne)))
                    fun (a : Not (P a)) =>
                    @Eq.refl.{1} ENNReal
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))))
            (SummationFilter.unconditional.{0} α)))
        (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
          (fun (a : α) =>
            @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (@Subtype.val.{1} (α → ENNReal)
                (fun (f : α → ENNReal) =>
                  @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (SummationFilter.unconditional.{0} α))
                p a)
              (@ite.{1} ENNReal (P a) (inst a)
                (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
          (SummationFilter.unconditional.{0} α)))
      (@eq_self.{1} ENNReal
        (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
          (fun (a : α) =>
            @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (@Subtype.val.{1} (α → ENNReal)
                (fun (f : α → ENNReal) =>
                  @HasSum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace f
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                    (SummationFilter.unconditional.{0} α))
                p a)
              (@ite.{1} ENNReal (P a) (inst a)
                (@OfNat.ofNat.{0} ENNReal (nat_lit 1) (@One.toOfNat1.{0} ENNReal ENNReal.instOne))
                (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
          (SummationFilter.unconditional.{0} α))))
theorem ProbabilityTheory.Pr_uniform_equiv : ∀ {α β : Type} [inst : Fintype.{0} α] [inst_1 : Nonempty.{1} α]
  [inst_2 : Fintype.{0} β] [inst_3 : Nonempty.{1} β] (e : Equiv.{1, 1} α β) (P : β → Prop),
  @Eq.{1} ENNReal
    (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
      (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) α Prop
        (@PMF.uniformOfFintype.{0} α inst inst_1) fun (a : α) =>
        @Pure.pure.{0, 0} PMF.{0}
          (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop
          (P
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
      True)
    (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
      (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) β Prop
        (@PMF.uniformOfFintype.{0} β inst_2 inst_3) fun (b : β) =>
        @Pure.pure.{0, 0} PMF.{0}
          (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop (P b))
      True) :=
fun {α β : Type} [inst : Fintype.{0} α] [inst_1 : Nonempty.{1} α] [inst_2 : Fintype.{0} β] [inst_3 : Nonempty.{1} β]
    (e : Equiv.{1, 1} α β) (P : β → Prop) =>
  have hmap :
    @Eq.{1} (PMF.{0} β)
      (@PMF.map.{0, 0} α β
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
        (@PMF.uniformOfFintype.{0} α inst inst_1))
      (@PMF.uniformOfFintype.{0} β inst_2 inst_3) :=
    @PMF.ext.{0} β
      (@PMF.map.{0, 0} α β
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
        (@PMF.uniformOfFintype.{0} α inst inst_1))
      (@PMF.uniformOfFintype.{0} β inst_2 inst_3) fun (b : β) =>
      @Eq.mpr.{0}
        (@Eq.{1} ENNReal
          (@DFunLike.coe.{1, 1, 1} (PMF.{0} β) β (fun (x : β) => ENNReal) (@PMF.instFunLike.{0} β)
            (@PMF.map.{0, 0} α β
              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
              (@PMF.uniformOfFintype.{0} α inst inst_1))
            b)
          (@DFunLike.coe.{1, 1, 1} (PMF.{0} β) β (fun (x : β) => ENNReal) (@PMF.instFunLike.{0} β)
            (@PMF.uniformOfFintype.{0} β inst_2 inst_3) b))
        (@Eq.{1} ENNReal
          (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
            @ite.{1} ENNReal
              (@Eq.{1} β b
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
              (Classical.propDecidable
                (@Eq.{1} β b
                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
              (@Inv.inv.{0} ENNReal ENNReal.instInv
                (@Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Fintype.card.{0} β inst_2)))
              (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
          (@Inv.inv.{0} ENNReal ENNReal.instInv
            (@Nat.cast.{0} ENNReal
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
              (@Fintype.card.{0} β inst_2))))
        (@id.{0}
          (@Eq.{1} Prop
            (@Eq.{1} ENNReal
              (@DFunLike.coe.{1, 1, 1} (PMF.{0} β) β (fun (x : β) => ENNReal) (@PMF.instFunLike.{0} β)
                (@PMF.map.{0, 0} α β
                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
                  (@PMF.uniformOfFintype.{0} α inst inst_1))
                b)
              (@DFunLike.coe.{1, 1, 1} (PMF.{0} β) β (fun (x : β) => ENNReal) (@PMF.instFunLike.{0} β)
                (@PMF.uniformOfFintype.{0} β inst_2 inst_3) b))
            (@Eq.{1} ENNReal
              (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
                @ite.{1} ENNReal
                  (@Eq.{1} β b
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
                  (Classical.propDecidable
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
              (@Inv.inv.{0} ENNReal ENNReal.instInv
                (@Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Fintype.card.{0} β inst_2)))))
          (@congr.{1, 1} ENNReal Prop
            (@Eq.{1} ENNReal
              (@DFunLike.coe.{1, 1, 1} (PMF.{0} β) β (fun (x : β) => ENNReal) (@PMF.instFunLike.{0} β)
                (@PMF.map.{0, 0} α β
                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
                  (@PMF.uniformOfFintype.{0} α inst inst_1))
                b))
            (@Eq.{1} ENNReal
              (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
                @ite.{1} ENNReal
                  (@Eq.{1} β b
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
                  (Classical.propDecidable
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
            (@DFunLike.coe.{1, 1, 1} (PMF.{0} β) β (fun (x : β) => ENNReal) (@PMF.instFunLike.{0} β)
              (@PMF.uniformOfFintype.{0} β inst_2 inst_3) b)
            (@Inv.inv.{0} ENNReal ENNReal.instInv
              (@Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (@Fintype.card.{0} β inst_2)))
            (@congrArg.{1, 1} ENNReal (ENNReal → Prop)
              (@DFunLike.coe.{1, 1, 1} (PMF.{0} β) β (fun (x : β) => ENNReal) (@PMF.instFunLike.{0} β)
                (@PMF.map.{0, 0} α β
                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
                  (@PMF.uniformOfFintype.{0} α inst inst_1))
                b)
              (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
                @ite.{1} ENNReal
                  (@Eq.{1} β b
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
                  (Classical.propDecidable
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
              (@Eq.{1} ENNReal)
              (@Eq.trans.{1} ENNReal
                (@DFunLike.coe.{1, 1, 1} (PMF.{0} β) β (fun (x : β) => ENNReal) (@PMF.instFunLike.{0} β)
                  (@PMF.map.{0, 0} α β
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
                    (@PMF.uniformOfFintype.{0} α inst inst_1))
                  b)
                (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
                  (fun (a : α) =>
                    @ite.{1} ENNReal
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          a))
                      (Classical.propDecidable
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            a)))
                      (@DFunLike.coe.{1, 1, 1} (PMF.{0} α) α (fun (x : α) => ENNReal) (@PMF.instFunLike.{0} α)
                        (@PMF.uniformOfFintype.{0} α inst inst_1) a)
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                  (SummationFilter.unconditional.{0} α))
                (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (b_1 : α) =>
                  @ite.{1} ENNReal
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                        b_1))
                    (Classical.propDecidable
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          b_1)))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                (@PMF.map_apply.{0, 0} α β
                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
                  (@PMF.uniformOfFintype.{0} α inst inst_1) b)
                (@Eq.trans.{1} ENNReal
                  (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
                    (fun (a : α) =>
                      @ite.{1} ENNReal
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            a))
                        (Classical.propDecidable
                          (@Eq.{1} β b
                            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β))
                              e a)))
                        (@DFunLike.coe.{1, 1, 1} (PMF.{0} α) α (fun (x : α) => ENNReal) (@PMF.instFunLike.{0} α)
                          (@PMF.uniformOfFintype.{0} α inst inst_1) a)
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                    (SummationFilter.unconditional.{0} α))
                  (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
                    (fun (a : α) =>
                      @ite.{1} ENNReal
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            a))
                        (Classical.propDecidable
                          (@Eq.{1} β b
                            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β))
                              e a)))
                        (@Inv.inv.{0} ENNReal ENNReal.instInv
                          (@Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            (@Fintype.card.{0} β inst_2)))
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                    (SummationFilter.unconditional.{0} α))
                  (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (b_1 : α) =>
                    @ite.{1} ENNReal
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          b_1))
                      (Classical.propDecidable
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            b_1)))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                  (@congrFun'.{1, 1} (SummationFilter.{0} α) ENNReal
                    (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace fun (a : α) =>
                      @ite.{1} ENNReal
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            a))
                        (Classical.propDecidable
                          (@Eq.{1} β b
                            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β))
                              e a)))
                        (@DFunLike.coe.{1, 1, 1} (PMF.{0} α) α (fun (x : α) => ENNReal) (@PMF.instFunLike.{0} α)
                          (@PMF.uniformOfFintype.{0} α inst inst_1) a)
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                    (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace fun (a : α) =>
                      @ite.{1} ENNReal
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            a))
                        (Classical.propDecidable
                          (@Eq.{1} β b
                            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β))
                              e a)))
                        (@Inv.inv.{0} ENNReal ENNReal.instInv
                          (@Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            (@Fintype.card.{0} β inst_2)))
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                    (@congrArg.{1, 1} ((a : α) → ENNReal)
                      ((L : optParam.{1} (SummationFilter.{0} α) (SummationFilter.unconditional.{0} α)) → ENNReal)
                      (fun (a : α) =>
                        @ite.{1} ENNReal
                          (@Eq.{1} β b
                            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β))
                              e a))
                          (Classical.propDecidable
                            (@Eq.{1} β b
                              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                  (@Equiv.instEquivLike.{1, 1} α β))
                                e a)))
                          (@DFunLike.coe.{1, 1, 1} (PMF.{0} α) α (fun (x : α) => ENNReal) (@PMF.instFunLike.{0} α)
                            (@PMF.uniformOfFintype.{0} α inst inst_1) a)
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                      (fun (a : α) =>
                        @ite.{1} ENNReal
                          (@Eq.{1} β b
                            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β))
                              e a))
                          (Classical.propDecidable
                            (@Eq.{1} β b
                              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                  (@Equiv.instEquivLike.{1, 1} α β))
                                e a)))
                          (@Inv.inv.{0} ENNReal ENNReal.instInv
                            (@Nat.cast.{0} ENNReal
                              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                              (@Fintype.card.{0} β inst_2)))
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                      (@tsum.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace)
                      (@funext.{1, 1} α (fun (x : α) => ENNReal)
                        (fun (x : α) =>
                          @ite.{1} ENNReal
                            (@Eq.{1} β b
                              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                  (@Equiv.instEquivLike.{1, 1} α β))
                                e x))
                            (Classical.propDecidable
                              (@Eq.{1} β b
                                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                    (@Equiv.instEquivLike.{1, 1} α β))
                                  e x)))
                            (@DFunLike.coe.{1, 1, 1} (PMF.{0} α) α (fun (x : α) => ENNReal) (@PMF.instFunLike.{0} α)
                              (@PMF.uniformOfFintype.{0} α inst inst_1) x)
                            (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                        (fun (x : α) =>
                          @ite.{1} ENNReal
                            (@Eq.{1} β b
                              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                  (@Equiv.instEquivLike.{1, 1} α β))
                                e x))
                            (Classical.propDecidable
                              (@Eq.{1} β b
                                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                    (@Equiv.instEquivLike.{1, 1} α β))
                                  e x)))
                            (@Inv.inv.{0} ENNReal ENNReal.instInv
                              (@Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                (@Fintype.card.{0} β inst_2)))
                            (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                        fun (a : α) =>
                        @ite_congr.{1} ENNReal
                          (@Eq.{1} β b
                            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β))
                              e a))
                          (@Eq.{1} β b
                            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β))
                              e a))
                          (@DFunLike.coe.{1, 1, 1} (PMF.{0} α) α (fun (x : α) => ENNReal) (@PMF.instFunLike.{0} α)
                            (@PMF.uniformOfFintype.{0} α inst inst_1) a)
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
                          (@Inv.inv.{0} ENNReal ENNReal.instInv
                            (@Nat.cast.{0} ENNReal
                              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                              (@Fintype.card.{0} β inst_2)))
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
                          (Classical.propDecidable
                            (@Eq.{1} β b
                              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                  (@Equiv.instEquivLike.{1, 1} α β))
                                e a)))
                          (Classical.propDecidable
                            (@Eq.{1} β b
                              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                  (@Equiv.instEquivLike.{1, 1} α β))
                                e a)))
                          (@Eq.refl.{1} Prop
                            (@Eq.{1} β b
                              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                  (@Equiv.instEquivLike.{1, 1} α β))
                                e a)))
                          (fun
                              (a_1 :
                                @Eq.{1} β b
                                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                      (@Equiv.instEquivLike.{1, 1} α β))
                                    e a)) =>
                            @Eq.trans.{1} ENNReal
                              (@DFunLike.coe.{1, 1, 1} (PMF.{0} α) α (fun (x : α) => ENNReal) (@PMF.instFunLike.{0} α)
                                (@PMF.uniformOfFintype.{0} α inst inst_1) a)
                              (@Inv.inv.{0} ENNReal ENNReal.instInv
                                (@Nat.cast.{0} ENNReal
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      ENNReal.instAddCommMonoidWithOne))
                                  (@Fintype.card.{0} α inst)))
                              (@Inv.inv.{0} ENNReal ENNReal.instInv
                                (@Nat.cast.{0} ENNReal
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      ENNReal.instAddCommMonoidWithOne))
                                  (@Fintype.card.{0} β inst_2)))
                              (@PMF.uniformOfFintype_apply.{0} α inst inst_1 a)
                              (@congrArg.{1, 1} ENNReal ENNReal
                                (@Nat.cast.{0} ENNReal
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      ENNReal.instAddCommMonoidWithOne))
                                  (@Fintype.card.{0} α inst))
                                (@Nat.cast.{0} ENNReal
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      ENNReal.instAddCommMonoidWithOne))
                                  (@Fintype.card.{0} β inst_2))
                                (@Inv.inv.{0} ENNReal ENNReal.instInv)
                                (@congrArg.{1, 1} Nat ENNReal (@Fintype.card.{0} α inst) (@Fintype.card.{0} β inst_2)
                                  (@Nat.cast.{0} ENNReal
                                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                        ENNReal.instAddCommMonoidWithOne)))
                                  (@Fintype.card_congr.{0, 0} α β inst inst_2 e))))
                          fun
                            (a :
                              Not
                                (@Eq.{1} β b
                                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β
                                      (@Equiv.instEquivLike.{1, 1} α β))
                                    e a))) =>
                          @Eq.refl.{1} ENNReal
                            (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
                    (SummationFilter.unconditional.{0} α))
                  (@tsum_fintype.{0, 0} ENNReal α ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
                    (SummationFilter.unconditional.{0} α) (SummationFilter.instLeAtTopUnconditional.{0} α) inst
                    fun (b_1 : α) =>
                    @ite.{1} ENNReal
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          b_1))
                      (Classical.propDecidable
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            b_1)))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))))
            (@PMF.uniformOfFintype_apply.{0} β inst_2 inst_3 b)))
        (have hs :
          @Eq.{1} ENNReal
            (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
              @ite.{1} ENNReal
                (@Eq.{1} β b
                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
                (Classical.propDecidable
                  (@Eq.{1} β b
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2)))
                (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
            (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
              @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2)))
                (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))) :=
          @Eq.mpr.{0}
            (@Eq.{1} ENNReal
              (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
                @ite.{1} ENNReal
                  (@Eq.{1} β b
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
                  (Classical.propDecidable
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
              (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
                @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
            (@Eq.{1} ENNReal
              (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
                @ite.{1} ENNReal
                  (@Eq.{1} β b
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
                  (Classical.propDecidable
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
              (@Inv.inv.{0} ENNReal ENNReal.instInv
                (@Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Fintype.card.{0} β inst_2))))
            (@id.{0}
              (@Eq.{1} Prop
                (@Eq.{1} ENNReal
                  (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
                    @ite.{1} ENNReal
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          a))
                      (Classical.propDecidable
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            a)))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                  (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
                    @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
                (@Eq.{1} ENNReal
                  (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
                    @ite.{1} ENNReal
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          a))
                      (Classical.propDecidable
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            a)))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))))
              (@congrArg.{1, 1} ENNReal Prop
                (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
                  @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2)))
                (@Eq.{1} ENNReal
                  (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
                    @ite.{1} ENNReal
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          a))
                      (Classical.propDecidable
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            a)))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
                (@Eq.trans.{1} ENNReal
                  (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (x : β) =>
                    @ite.{1} ENNReal (@Eq.{1} β b x) (Classical.propDecidable (@Eq.{1} β b x))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                        (@Zero.toOfNat0.{0} ENNReal
                          (@AddZero.toZero.{0} ENNReal
                            (@AddZeroClass.toAddZero.{0} ENNReal
                              (@AddMonoid.toAddZeroClass.{0} ENNReal
                                (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid)))))))
                  (@ite.{1} ENNReal
                    (@Membership.mem.{0, 0} β (Finset.{0} β)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} β) β (@Finset.instSetLike.{0} β))
                      (@Finset.univ.{0} β inst_2) b)
                    (@Finset.decidableMem.{0} β (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) b
                      (@Finset.univ.{0} β inst_2))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                      (@Zero.toOfNat0.{0} ENNReal
                        (@AddZero.toZero.{0} ENNReal
                          (@AddZeroClass.toAddZero.{0} ENNReal
                            (@AddMonoid.toAddZeroClass.{0} ENNReal
                              (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid)))))))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@Finset.sum_ite_eq.{0, 0} β ENNReal ENNReal.instAddCommMonoid
                    (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) (@Finset.univ.{0} β inst_2) b
                    fun (x : β) =>
                    @Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                  (@ite_cond_eq_true.{1} ENNReal
                    (@Membership.mem.{0, 0} β (Finset.{0} β)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} β) β (@Finset.instSetLike.{0} β))
                      (@Finset.univ.{0} β inst_2) b)
                    (@Finset.decidableMem.{0} β (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) b
                      (@Finset.univ.{0} β inst_2))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                      (@Zero.toOfNat0.{0} ENNReal
                        (@AddZero.toZero.{0} ENNReal
                          (@AddZeroClass.toAddZero.{0} ENNReal
                            (@AddMonoid.toAddZeroClass.{0} ENNReal
                              (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid))))))
                    (@Finset.mem_univ._simp_1.{0} β inst_2 b)))))
            (@Eq.mp.{0}
              (@Eq.{1} ENNReal
                (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (x : α) =>
                  @ite.{1} ENNReal
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e x))
                    (Classical.propDecidable
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          x)))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (x : β) =>
                  @ite.{1} ENNReal (@Eq.{1} β b x) (Classical.propDecidable (@Eq.{1} β b x))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
              (@Eq.{1} ENNReal
                (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (x : α) =>
                  @ite.{1} ENNReal
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e x))
                    (Classical.propDecidable
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          x)))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2))))
              (@congrArg.{1, 1} ENNReal Prop
                (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (x : β) =>
                  @ite.{1} ENNReal (@Eq.{1} β b x) (Classical.propDecidable (@Eq.{1} β b x))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2)))
                (@Eq.{1} ENNReal
                  (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (x : α) =>
                    @ite.{1} ENNReal
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          x))
                      (Classical.propDecidable
                        (@Eq.{1} β b
                          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                            x)))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
                (@Eq.trans.{1} ENNReal
                  (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (x : β) =>
                    @ite.{1} ENNReal (@Eq.{1} β b x) (Classical.propDecidable (@Eq.{1} β b x))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                        (@Zero.toOfNat0.{0} ENNReal
                          (@AddZero.toZero.{0} ENNReal
                            (@AddZeroClass.toAddZero.{0} ENNReal
                              (@AddMonoid.toAddZeroClass.{0} ENNReal
                                (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid)))))))
                  (@ite.{1} ENNReal
                    (@Membership.mem.{0, 0} β (Finset.{0} β)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} β) β (@Finset.instSetLike.{0} β))
                      (@Finset.univ.{0} β inst_2) b)
                    (@Finset.decidableMem.{0} β (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) b
                      (@Finset.univ.{0} β inst_2))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                      (@Zero.toOfNat0.{0} ENNReal
                        (@AddZero.toZero.{0} ENNReal
                          (@AddZeroClass.toAddZero.{0} ENNReal
                            (@AddMonoid.toAddZeroClass.{0} ENNReal
                              (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid)))))))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@Finset.sum_ite_eq.{0, 0} β ENNReal ENNReal.instAddCommMonoid
                    (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) (@Finset.univ.{0} β inst_2) b
                    fun (x : β) =>
                    @Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                  (@ite_cond_eq_true.{1} ENNReal
                    (@Membership.mem.{0, 0} β (Finset.{0} β)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} β) β (@Finset.instSetLike.{0} β))
                      (@Finset.univ.{0} β inst_2) b)
                    (@Finset.decidableMem.{0} β (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) b
                      (@Finset.univ.{0} β inst_2))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                      (@Zero.toOfNat0.{0} ENNReal
                        (@AddZero.toZero.{0} ENNReal
                          (@AddZeroClass.toAddZero.{0} ENNReal
                            (@AddMonoid.toAddZeroClass.{0} ENNReal
                              (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid))))))
                    (@Finset.mem_univ._simp_1.{0} β inst_2 b))))
              (@Fintype.sum_equiv.{0, 0, 0} α β ENNReal inst inst_2 ENNReal.instAddCommMonoid e
                (fun (a : α) =>
                  @ite.{1} ENNReal
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
                    (Classical.propDecidable
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          a)))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                (fun (b' : β) =>
                  @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                fun (a : α) =>
                @Eq.refl.{1} ENNReal
                  (@ite.{1} ENNReal
                    (@Eq.{1} β b
                      (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                        (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
                    (Classical.propDecidable
                      (@Eq.{1} β b
                        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e
                          a)))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))));
        @Eq.trans.{1} ENNReal
          (@Finset.sum.{0, 0} α ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} α inst) fun (a : α) =>
            @ite.{1} ENNReal
              (@Eq.{1} β b
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a))
              (Classical.propDecidable
                (@Eq.{1} β b
                  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
              (@Inv.inv.{0} ENNReal ENNReal.instInv
                (@Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Fintype.card.{0} β inst_2)))
              (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
          (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
            @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
              (@Inv.inv.{0} ENNReal ENNReal.instInv
                (@Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Fintype.card.{0} β inst_2)))
              (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
          (@Inv.inv.{0} ENNReal ENNReal.instInv
            (@Nat.cast.{0} ENNReal
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
              (@Fintype.card.{0} β inst_2)))
          hs
          (@of_eq_true
            (@Eq.{1} ENNReal
              (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
                @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
              (@Inv.inv.{0} ENNReal ENNReal.instInv
                (@Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Fintype.card.{0} β inst_2))))
            (@Eq.trans.{1} Prop
              (@Eq.{1} ENNReal
                (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
                  @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2))))
              (@Eq.{1} ENNReal
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2)))
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2))))
              True
              (@congrFun'.{1, 1} ENNReal Prop
                (@Eq.{1} ENNReal
                  (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
                    @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))
                (@Eq.{1} ENNReal
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2))))
                (@congrArg.{1, 1} ENNReal (ENNReal → Prop)
                  (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (b' : β) =>
                    @ite.{1} ENNReal (@Eq.{1} β b b') (Classical.propDecidable (@Eq.{1} β b b'))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                  (@Inv.inv.{0} ENNReal ENNReal.instInv
                    (@Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (@Fintype.card.{0} β inst_2)))
                  (@Eq.{1} ENNReal)
                  (@Eq.trans.{1} ENNReal
                    (@Finset.sum.{0, 0} β ENNReal ENNReal.instAddCommMonoid (@Finset.univ.{0} β inst_2) fun (x : β) =>
                      @ite.{1} ENNReal (@Eq.{1} β b x) (Classical.propDecidable (@Eq.{1} β b x))
                        (@Inv.inv.{0} ENNReal ENNReal.instInv
                          (@Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            (@Fintype.card.{0} β inst_2)))
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                          (@Zero.toOfNat0.{0} ENNReal
                            (@AddZero.toZero.{0} ENNReal
                              (@AddZeroClass.toAddZero.{0} ENNReal
                                (@AddMonoid.toAddZeroClass.{0} ENNReal
                                  (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid)))))))
                    (@ite.{1} ENNReal
                      (@Membership.mem.{0, 0} β (Finset.{0} β)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} β) β (@Finset.instSetLike.{0} β))
                        (@Finset.univ.{0} β inst_2) b)
                      (@Finset.decidableMem.{0} β (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) b
                        (@Finset.univ.{0} β inst_2))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                        (@Zero.toOfNat0.{0} ENNReal
                          (@AddZero.toZero.{0} ENNReal
                            (@AddZeroClass.toAddZero.{0} ENNReal
                              (@AddMonoid.toAddZeroClass.{0} ENNReal
                                (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid)))))))
                    (@Inv.inv.{0} ENNReal ENNReal.instInv
                      (@Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (@Fintype.card.{0} β inst_2)))
                    (@Finset.sum_ite_eq.{0, 0} β ENNReal ENNReal.instAddCommMonoid
                      (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) (@Finset.univ.{0} β inst_2) b
                      fun (x : β) =>
                      @Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                    (@ite_cond_eq_true.{1} ENNReal
                      (@Membership.mem.{0, 0} β (Finset.{0} β)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} β) β (@Finset.instSetLike.{0} β))
                        (@Finset.univ.{0} β inst_2) b)
                      (@Finset.decidableMem.{0} β (fun (a b : β) => Classical.propDecidable (@Eq.{1} β a b)) b
                        (@Finset.univ.{0} β inst_2))
                      (@Inv.inv.{0} ENNReal ENNReal.instInv
                        (@Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (@Fintype.card.{0} β inst_2)))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                        (@Zero.toOfNat0.{0} ENNReal
                          (@AddZero.toZero.{0} ENNReal
                            (@AddZeroClass.toAddZero.{0} ENNReal
                              (@AddMonoid.toAddZeroClass.{0} ENNReal
                                (@AddCommMonoid.toAddMonoid.{0} ENNReal ENNReal.instAddCommMonoid))))))
                      (@Finset.mem_univ._simp_1.{0} β inst_2 b))))
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2))))
              (@eq_self.{1} ENNReal
                (@Inv.inv.{0} ENNReal ENNReal.instInv
                  (@Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (@Fintype.card.{0} β inst_2)))))));
  @id.{0}
    (@Eq.{1} ENNReal
      (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
        (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) α Prop
          (@PMF.uniformOfFintype.{0} α inst inst_1) fun (a : α) =>
          @Pure.pure.{0, 0} PMF.{0}
            (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop
            (P
              (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e a)))
        True)
      (@DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop)
        (@Bind.bind.{0, 0} PMF.{0} (@Monad.toBind.{0, 0} PMF.{0} PMF.instMonad.{0}) β Prop
          (@PMF.uniformOfFintype.{0} β inst_2 inst_3) fun (b : β) =>
          @Pure.pure.{0, 0} PMF.{0}
            (@Applicative.toPure.{0, 0} PMF.{0} (@Monad.toApplicative.{0, 0} PMF.{0} PMF.instMonad.{0})) Prop (P b))
        True))
    (have hcomp :
      @Eq.{1} (PMF.{0} Prop)
        (@PMF.map.{0, 0} α Prop
          (@Function.comp.{1, 1, 1} α β Prop P
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e))
          (@PMF.uniformOfFintype.{0} α inst inst_1))
        (@PMF.map.{0, 0} β Prop P
          (@PMF.map.{0, 0} α β
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
            (@PMF.uniformOfFintype.{0} α inst inst_1))) :=
      @Eq.symm.{1} (PMF.{0} Prop)
        (@PMF.map.{0, 0} β Prop P
          (@PMF.map.{0, 0} α β
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
            (@PMF.uniformOfFintype.{0} α inst inst_1)))
        (@PMF.map.{0, 0} α Prop
          (@Function.comp.{1, 1, 1} α β Prop P
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e))
          (@PMF.uniformOfFintype.{0} α inst inst_1))
        (@PMF.map_comp.{0, 0, 0} α β Prop
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
          (@PMF.uniformOfFintype.{0} α inst inst_1) P);
    @congrArg.{1, 1} (PMF.{0} Prop) ENNReal
      (@PMF.map.{0, 0} α Prop
        (@Function.comp.{1, 1, 1} α β Prop P
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e))
        (@PMF.uniformOfFintype.{0} α inst inst_1))
      (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3))
      (fun (q : PMF.{0} Prop) =>
        @DFunLike.coe.{1, 1, 1} (PMF.{0} Prop) Prop (fun (x : Prop) => ENNReal) (@PMF.instFunLike.{0} Prop) q True)
      (@Eq.trans.{1} (PMF.{0} Prop)
        (@PMF.map.{0, 0} α Prop
          (@Function.comp.{1, 1, 1} α β Prop P
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e))
          (@PMF.uniformOfFintype.{0} α inst inst_1))
        (@PMF.map.{0, 0} β Prop P
          (@PMF.map.{0, 0} α β
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
            (@PMF.uniformOfFintype.{0} α inst inst_1)))
        (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3)) hcomp
        (@Eq.mpr.{0}
          (@Eq.{1} (PMF.{0} Prop)
            (@PMF.map.{0, 0} β Prop P
              (@PMF.map.{0, 0} α β
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
                (@PMF.uniformOfFintype.{0} α inst inst_1)))
            (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3)))
          (@Eq.{1} (PMF.{0} Prop) (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3))
            (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3)))
          (@id.{0}
            (@Eq.{1} Prop
              (@Eq.{1} (PMF.{0} Prop)
                (@PMF.map.{0, 0} β Prop P
                  (@PMF.map.{0, 0} α β
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
                    (@PMF.uniformOfFintype.{0} α inst inst_1)))
                (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3)))
              (@Eq.{1} (PMF.{0} Prop) (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3))
                (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3))))
            (@congrArg.{1, 1} (PMF.{0} β) Prop
              (@PMF.map.{0, 0} α β
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} α β) α (fun (x : α) => β)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} α β) α β (@Equiv.instEquivLike.{1, 1} α β)) e)
                (@PMF.uniformOfFintype.{0} α inst inst_1))
              (@PMF.uniformOfFintype.{0} β inst_2 inst_3)
              (fun (_a : PMF.{0} β) =>
                @Eq.{1} (PMF.{0} Prop) (@PMF.map.{0, 0} β Prop P _a)
                  (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3)))
              hmap))
          (@Eq.refl.{1} (PMF.{0} Prop) (@PMF.map.{0, 0} β Prop P (@PMF.uniformOfFintype.{0} β inst_2 inst_3))))))


