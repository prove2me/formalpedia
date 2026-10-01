-- Prove2me | Definitions.Def_Yukon_5af2022acebdca615a0a04f9
-- name    : Yukon_5af2022acebdca615a0a04f9
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:49:18.512479+00:00
-- url     : https://prove2.me/theorems/49841ff0-ce80-4654-9b5e-8724e65b27f0
-- title:
--   YukonModule.ArkLib.ProofSystem.ToyProblem.Spec.ErasureDecoder.part0
-- statement:
--   Source module ArkLib.ProofSystem.ToyProblem.Spec.ErasureDecoder. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean
--
--   yukon-proof-operation:9fc422ae213f1619357bafc80c66a628194728967180bdb5d7a15fcab4d4fbda
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZmJjY2FlZjVlZjVlNjZkODg4MjQ4MDRiM2Q5YTQ5ZGNkOWRiN2I1YzIxNDQwODZhZjZiYjA2YTQ3ZTBiOGE0NCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjlmYzQyMmFlMjEzZjE2MTkzNTdiYWZjODBjNjZhNjI4MTk0NzI4OTY3MTgwYmRiNWQ3YTE1ZmNhYjRkNGZiZGEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81YWYyMDIyYWNlYmRjYTYxNWEwYTA0ZjkiLCJ2IjoyfQ]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/


import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e

import Definitions.Def_Yukon_06abc6af2bee1228adb4245e



import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Init
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Batteries.Tactic.Lint
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Batteries.Control.Lemmas
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Finset.Card
import Batteries.Control.OptionT
import Batteries.Control.AlternativeMonad
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Init.Data.UInt.Lemmas
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.List.Sym
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Order.Basic
import Mathlib.Control.Monad.Writer
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Set.Card
import Init.Data.Vector.Lemmas
import Mathlib.Control.Lawful
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Logic.Equiv.Sum
import Std.Tactic.Do
import Std.Internal.Do.Assertion
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Init.Data.String.Lemmas.Iterate
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Iterate
import Init.Data.String.Defs
import Init.Omega
import Init.Data.Slice.Lemmas
import Init.Data.Nat.Mod
import Init.Data.List.TakeDrop
import Init.Data.List.Range
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Range
import Init.Data.Iterators.Lemmas
import Init.Data.Range
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Std.Do.Triple.SpecLemmas
import Init.Data.Slice.Array
import Init.Data.Range.Polymorphic
import Init.Data.Range.Polymorphic.Iterators
import Init.While
import Init.Syntax
import Lean.Meta.Sym.Pattern
import Lean.Meta.Tactic.Simp
import Lean.Meta.Match.MatcherApp
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Do.Attr
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Sym.Apply
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finsupp.Order
import Std.Data.HashMap.Lemmas
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Use
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Notation
import Batteries.Data.Vector.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Vector.Basic
import Definitions.Def_Yukon_6b274c76f1610f2d89b18673
import Definitions.Def_Yukon_f6ef87da37ae124e79421110
import Definitions.Def_Yukon_73cb364285b0db29404203c2
import Definitions.Def_Yukon_8f2c8c65169aeb35b0e3b51b
import Definitions.Def_Yukon_30e807a5525bb5bfbcd8d7fe
import Definitions.Def_Yukon_8cbc36bf7c5db72d14564b22
import Definitions.Def_Yukon_be2502e9fa82964be2b26d94
import Definitions.Def_Yukon_73e12f81c9297752b15d64fc
import Definitions.Def_Yukon_b2c54449f2b5ff5eadbe0d35
import Definitions.Def_Yukon_44168058399b05f7fa2f05f3
import Definitions.Def_Yukon_d24a38ec5f10307fd0342f04
import Definitions.Def_Yukon_97cb7c7d84a051f4f06c406f
import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
import Definitions.Def_Yukon_3e259ba73c40aefea227f941
import Definitions.Def_Yukon_ec6e56db18cc5472c07c58c9
import Definitions.Def_Yukon_2b5744019605f484379c669d
import Definitions.Def_Yukon_279cd606a70ccf731403c588
import Definitions.Def_Yukon_06171bfbcf8faa33c2404989
import Definitions.Def_Yukon_ec400a7ccf6a92c555e3042d
import Definitions.Def_Yukon_be0ea4aaa74139969f477ed4
import Definitions.Def_Yukon_dcb7ae1acc5c3f644cb2dbde
import Definitions.Def_Yukon_244e3ea6d0d0730a9e5f32f1
import Definitions.Def_Yukon_d5677f095c6f5bc42a19ec97
import Definitions.Def_Yukon_65bf5f146acacdd3fb8e2a4b
import Definitions.Def_Yukon_38ec85bb4fa19191fc03f2b7
import Definitions.Def_Yukon_adec2dfd4b542b412818840e
import Definitions.Def_Yukon_13e8bc1bb87885041af4460c
import Definitions.Def_Yukon_5f72f990f3206a29ca7cf412
import Definitions.Def_Yukon_dec25d5b26c5465c24348b33
import Definitions.Def_Yukon_4231d0ef2a5eb8af03e94595
import Definitions.Def_Yukon_3a940f7a9ed7ceff2d5cc7d0
import Definitions.Def_Yukon_30b8fbcd5edceadbd62dc3a2
import Definitions.Def_Yukon_8009e2d1f7dbff7b8c9229a3
import Definitions.Def_Yukon_10be02bf5325c192ea9b6156
import Definitions.Def_Yukon_2c14ff8159663d774b8d6932
import Definitions.Def_Yukon_f78c736ab028618310894567
import Definitions.Def_Yukon_253c1feebadee49aac5da140
import Definitions.Def_Yukon_bb6a74fb27943bb3c66baf5c
import Definitions.Def_Yukon_3df7984cc5373c300a4b8062
import Definitions.Def_Yukon_a28c9fe400a38bdf3eceff63
import Definitions.Def_Yukon_8946d0143d9c9079b9c7f954
import Definitions.Def_Yukon_548e569f5946909e0d9a91e1
import Definitions.Def_Yukon_55d30d3deeb7817ce41e3794
import Definitions.Def_Yukon_d98d4e7e5ec3bb11cc1d90f7
import Definitions.Def_Yukon_7273a9c19f6473b89f551716
import Definitions.Def_Yukon_2a6b3412af2af8cd7980168b
import Definitions.Def_Yukon_e3fd5de4db781670631c9e44
import Definitions.Def_Yukon_a15ac1cded7817143982668b
import Definitions.Def_Yukon_022bb9d266cb8f4801551966
import Definitions.Def_Yukon_611b01610aecbd244ce9662d
import Definitions.Def_Yukon_ecfd5800d3727e21f4e6ac0e
import Definitions.Def_Yukon_ac1fabbdddd4e4a4c0618520
import Definitions.Def_Yukon_c2812cd3bb492fcd345c5cac
import Definitions.Def_Yukon_78e7aecf404d2dec005a0f9a
import Definitions.Def_Yukon_f25f93421272fca15844f5d1
import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
import Definitions.Def_Yukon_117c11ed2c735a2904af9c20
import Definitions.Def_Yukon_77e185d7a48169037ca7e1d0
import Definitions.Def_Yukon_0b6b33c0cec00f644e57a89f
import Definitions.Def_Yukon_f6ffada621076861526b623c
import Definitions.Def_Yukon_0c415a7ac30982e40294fe41
import Definitions.Def_Yukon_53e8729e1f49868bba25744c
import Definitions.Def_Yukon_c47804ec84543e90a1df6a93
import Definitions.Def_Yukon_78fd002a26a9069876a24c31
import Definitions.Def_Yukon_d2d49184152cd1dbc0f0c191
import Definitions.Def_Yukon_92db958debc53176a8bcb5d5
import Definitions.Def_Yukon_d7f4157140aca01d48a00dbd
import Definitions.Def_Yukon_d65ebf357e39550be37d8383
import Definitions.Def_Yukon_eb44a079d629d0642e74f1e2
import Definitions.Def_Yukon_b2b98f746341a120449778db
import Definitions.Def_Yukon_9d723aac7b391c205a909f63
import Definitions.Def_Yukon_cda3959af6f436acfe6b2dff
import Definitions.Def_Yukon_423eef2a8735822795222f49
import Definitions.Def_Yukon_a4d42534f10e26d40ca4547d
import Definitions.Def_Yukon_c042061a45cc167df49b6d76
import Definitions.Def_Yukon_ece90b6202ec9f124162dcb0
import Definitions.Def_Yukon_41bdec15cc33404b0ec63823
import Definitions.Def_Yukon_8b5665bf82210d0598b96dcf
import Definitions.Def_Yukon_0ea8ce6d524d4af5d6af8c16
import Definitions.Def_Yukon_0e90bb4102c4ff68ed52ad80
import Definitions.Def_Yukon_bea5afc7edc0c83512a59496
import Definitions.Def_Yukon_e88c9935225aedcca88ceb17
import Definitions.Def_Yukon_c28297ca596069f170436f68
import Definitions.Def_Yukon_641302f1e500c2a544b42adc
import Definitions.Def_Yukon_2e7e800d480cc4c5ab2a0a15
import Definitions.Def_Yukon_c6017af749ce513ad214b155
import Definitions.Def_Yukon_2846fc6c80f8d5f5a8cd4e1b
import Definitions.Def_Yukon_a90bed0360280b6145f16a15
import Definitions.Def_Yukon_72181b0b489f9080e3f451b4
import Definitions.Def_Yukon_ec5bf85a212c6e6b07515e5b
import Definitions.Def_Yukon_02548f31838b67bf22685e61
import Definitions.Def_Yukon_886a4b334c887c16be8aca61
import Definitions.Def_Yukon_b73f94a7148a7d7a63af5100
import Definitions.Def_Yukon_1086cc3ce97dd189da831378
import Definitions.Def_Yukon_a7c0a0263f6aa5ef293ff57a
import Definitions.Def_Yukon_b72a997d3500e16e073e2af5
import Definitions.Def_Yukon_9f3aba2e8637ece6713a3f01
import Definitions.Def_Yukon_135b1e0f495a7a36531945f6
import Definitions.Def_Yukon_6a927b8822dd6d7731330099
import Definitions.Def_Yukon_879bf24290703d39a13e4167
import Definitions.Def_Yukon_5d8e96e71d6efa023561961d
import Definitions.Def_Yukon_103f1b0cd9116d3cfa5b22eb
import Definitions.Def_Yukon_7e23854ba7506d6e8bc7c0b0
import Definitions.Def_Yukon_c572cdc7ac754cf2a006a2e7
import Definitions.Def_Yukon_168b3f56a3214d856e63e24f
import Definitions.Def_Yukon_b695517d2595cd94ce373ad8
import Definitions.Def_Yukon_81690654349d137d5e1c95cb
import Definitions.Def_Yukon_02f07db8b576026b76bdd512
import Definitions.Def_Yukon_b7bcde9867b418c719f2e246
import Definitions.Def_Yukon_ba7304588491aaabedef2404
import Definitions.Def_Yukon_13abd70b92beced94bdb4981
import Definitions.Def_Yukon_950ab98b4aafc32b0f064af3
import Definitions.Def_Yukon_b274322d0e11762f90f047d3
import Definitions.Def_Yukon_84b1a34b80631e562026cc16
import Definitions.Def_Yukon_8d2d9b1245cbb497a9fbffbf
set_option backward.isDefEq.respectTransparency.types false
/-!
# Executable scalar Reed--Solomon erasure decoding for the toy problem

This file implements the scalar Reed--Solomon erasure decoder used by the concrete
round-by-round extractor for ABF26 Lemma 6.8.  The known-good coordinates are computed
*after* the combination challenge `γ` from the equality
`encode g j = f₁ j + γ • f₂ j`; the decoder interpolates on that dynamic finset.

## Scope

The concrete result is for alphabet `A = F`, an injective evaluation domain
`domain : ι ↪ F`, and coefficient messages `Fin k → F`.  It is not a generic additive-
code or folded-RS decoder.  Berlekamp--Welch, Gao, and Guruswami--Sudan are raw-error
decoders and are neither needed nor used on this known-erasure path.

## Cost (aspirational; unclocked per library convention)

ArkLib has no cost harness. The executable path uses CompPoly's pinned v4.32.2
`CPolynomial` interpolation and a finite re-encoding check.  No formal field-operation
bound, and in particular no generic `O((s n)^3)` claim, is made here.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26] (§6, App A.1).
-/

namespace ToyProblem.Spec

open CompPoly.CPolynomial
open Code InterleavedCode ProximityGap
open Probability
open scoped NNReal ENNReal ProbabilityTheory

variable {ι F : Type} [DecidableEq ι] [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]

/-- Degree-`< k` polynomial whose coefficient vector is `m`.  This proof-side bridge
uses Mathlib's explicit finite-sum linear equivalence, not `Classical.choose`.  It is
noncomputable only because Mathlib's `Polynomial` semiring instance is noncomputable;
the executable encoder and decoder below do not call it. -/
noncomputable def rsPolynomial (k : ℕ) (m : Fin k → F) : Polynomial F :=
  ((Polynomial.degreeLTEquiv F k).symm m).1

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem rsPolynomial_coeff (k : ℕ) (m : Fin k → F) (j : Fin k) :
    (rsPolynomial k m).coeff j = m j := by
  exact congrFun ((Polynomial.degreeLTEquiv F k).apply_symm_apply m) j

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
theorem rsPolynomial_degree_lt (k : ℕ) (m : Fin k → F) :
    (rsPolynomial k m).degree < k := by
  exact Polynomial.mem_degreeLT.mp ((Polynomial.degreeLTEquiv F k).symm m).2

/-- Scalar Reed--Solomon evaluation encoder on an arbitrary finite injective domain. -/
def rsEncoder (k : ℕ) (domain : ι ↪ F) : (Fin k → F) →ₗ[F] (ι → F) :=
  { toFun := fun m j ↦ ∑ i, m i * domain j ^ i.val
    map_add' := by
      intro m₁ m₂
      ext j
      simp only [Pi.add_apply, _root_.add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c m
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [_root_.mul_assoc] }

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem rsEncoder_apply (k : ℕ) (domain : ι ↪ F) (m : Fin k → F) (j : ι) :
    rsEncoder k domain m j = (rsPolynomial k m).eval (domain j) := by
  have hp : rsPolynomial k m ∈ Polynomial.degreeLT F k := by
    exact Polynomial.mem_degreeLT.mpr (rsPolynomial_degree_lt k m)
  change (∑ i, m i * domain j ^ i.val) = _
  rw [Polynomial.eval_eq_sum_degreeLTEquiv hp]
  apply Finset.sum_congr rfl
  intro i _
  change m i * domain j ^ i.val = (rsPolynomial k m).coeff i * domain j ^ i.val
  rw [rsPolynomial_coeff]

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The executable coefficient encoder has exactly the usual degree-`< k`
Reed--Solomon code as its range. -/
theorem rsEncoder_range (k : ℕ) (domain : ι ↪ F) :
    Set.range (rsEncoder k domain) =
      (ReedSolomon.code domain k : Set (ι → F)) := by
  ext w
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨rsPolynomial k m, Polynomial.mem_degreeLT.mpr (rsPolynomial_degree_lt k m), ?_⟩
    ext j
    simp [ReedSolomon.evalOnPoints]
  · rintro ⟨p, hp, rfl⟩
    let m : Fin k → F := Polynomial.degreeLTEquiv F k ⟨p, hp⟩
    refine ⟨m, ?_⟩
    have hpoly : rsPolynomial k m = p := by
      exact congrArg Subtype.val ((Polynomial.degreeLTEquiv F k).symm_apply_apply ⟨p, hp⟩)
    ext j
    rw [rsEncoder_apply, hpoly]
    rfl

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Evaluation on at least `k` distinct nodes is injective on coefficient messages. -/
theorem rsEncoder_injective [Fintype ι] {k : ℕ} {domain : ι ↪ F}
    (hcard : k ≤ Fintype.card ι) : Function.Injective (rsEncoder k domain) := by
  intro m₁ m₂ h
  have hp : rsPolynomial k m₁ = rsPolynomial k m₂ := by
    by_cases hk : k = 0
    · subst k
      have hm : m₁ = m₂ := by
        funext j
        exact Fin.elim0 j
      exact congrArg (rsPolynomial (F := F) 0) hm
    · apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ domain.injective
      · intro j
        rw [← rsEncoder_apply, ← rsEncoder_apply]
        exact congrFun h j
      · apply max_lt
        · by_cases hp : rsPolynomial k m₁ = 0
          · simpa [hp] using lt_of_lt_of_le (Nat.pos_of_ne_zero hk) hcard
          · exact (Polynomial.natDegree_lt_iff_degree_lt hp).2
              (rsPolynomial_degree_lt k m₁) |>.trans_le hcard
        · by_cases hp : rsPolynomial k m₂ = 0
          · simpa [hp] using lt_of_lt_of_le (Nat.pos_of_ne_zero hk) hcard
          · exact (Polynomial.natDegree_lt_iff_degree_lt hp).2
              (rsPolynomial_degree_lt k m₂) |>.trans_le hcard
  funext j
  rw [← rsPolynomial_coeff k m₁ j, hp, rsPolynomial_coeff]

omit [DecidableEq ι] [BEq F] [LawfulBEq F] in
/-- The full RS minimum-distance hypothesis supplies at least `k` retained coordinates.
This is the erasure-radius step: no half-distance error-decoding bound is used. -/
theorem rs_large_agreement_card [Fintype ι] [Nonempty ι] {k : ℕ} [NeZero k]
    (domain : ι ↪ F) (hk : k ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F)) : ℝ≥0))
    {S : Finset ι} (hS : (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card) :
    k ≤ S.card := by
  have hdmin :
      (((minRelHammingDistCode
        (ReedSolomon.code domain k : Set (ι → F)) : ℚ≥0) : ℝ)) =
        ((Fintype.card ι - k + 1 : ℕ) : ℝ) / Fintype.card ι := by
    letI : Inhabited ι := Classical.inhabited_of_nonempty ‹Nonempty ι›
    have h := minDist_div_card_eq_minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F))
    rw [ReedSolomon.minDist_eq_card_sub_min_add_1, min_eq_left hk] at h
    have hr := congrArg (fun q : ℚ => (q : ℝ)) h.symm
    norm_num at hr
    rw [Nat.cast_add, Nat.cast_one]
    exact hr
  have hδR : (δ : ℝ) <
      ((minRelHammingDistCode
        (ReedSolomon.code domain k : Set (ι → F)) : ℚ≥0) : ℝ) := by
    exact_mod_cast hδ
  rw [hdmin] at hδR
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hδmul : (δ : ℝ) * Fintype.card ι <
      (Fintype.card ι - k + 1 : ℕ) := (lt_div_iff₀ hnpos).mp hδR
  by_contra hnot
  have hcard : S.card ≤ k - 1 := by omega
  have hdecomp : Fintype.card ι - k + 1 + (k - 1) = Fintype.card ι := by omega
  have hcardR : (S.card : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hcard
  have hdecompR : ((Fintype.card ι - k + 1 : ℕ) : ℝ) + (k - 1 : ℕ) =
      Fintype.card ι := by exact_mod_cast hdecomp
  push_cast at hS hδmul hcardR hdecompR
  nlinarith

/-- **Computable interpolation erasure decoder** (scalar `A = F`). Given a set of `k`
non-erased node coordinates `nodes` and the evaluation domain `domain`, decode a
received word `w : ι → F` by Lagrange-interpolating through the nodes and reading off
the first `k` coefficients of the (unique, degree-`< #nodes`) interpolant.

A computable `def` (Lean accepts it without `noncomputable`), though
`#print axioms interpolationDecoder` reports `[propext, Classical.choice, Quot.sound]`
inherited via `CLagrange.interpolate` (`cinterpolate_eq_interpolate` bridges it to the
Mathlib `Lagrange.interpolate` used in the correctness proof). **NB the caller must supply
uncorrupted nodes** — this decoder does not itself find or verify an agreement set. -/
def interpolationDecoder (k : ℕ) (nodes : Finset ι) (domain : ι → F)
    (w : ι → F) : Fin k → F :=
  fun j ↦ (CLagrange.interpolate nodes domain w).coeff j.val

omit [DecidableEq F] in
/-- **Correctness / left-inverse of `interpolationDecoder`.** If `p : F[X]` has degree
`< #nodes`, the `domain` is injective on `nodes`, and `w` equals `p`'s evaluations on
`nodes` (an erasure pattern: only the non-erased `nodes` coordinates matter), then the
decoder returns exactly `p`'s coefficients. This is the erasure-decoding guarantee: the
degree-`< #nodes` interpolant is unique, so decoding recovers the true message. It
discharges the `hli` hypothesis of `Spec/General.lean :: erasureExtractor_mem_of_leftInverse`
whenever the Reed–Solomon `encode` is evaluation of a degree-`< k` message over a domain
containing `≥ k` agreement coordinates. -/
theorem interpolationDecoder_eq_coeff {k : ℕ} {nodes : Finset ι} {domain : ι → F}
    {w : ι → F} {p : Polynomial F} (hinj : Set.InjOn domain nodes)
    (hdeg : p.degree < nodes.card) (hval : ∀ j ∈ nodes, p.eval (domain j) = w j)
    (j : Fin k) : interpolationDecoder k nodes domain w j = p.coeff j.val := by
  -- Bridge the computable coefficient to the underlying `Polynomial` coefficient.
  have hbridge : (CLagrange.interpolate nodes domain w).coeff j.val
      = ((CLagrange.interpolate nodes domain w).toPoly).coeff j.val := by
    rw [CompPoly.CPolynomial.toPoly, CompPoly.CPolynomial.Raw.coeff_toPoly]
  -- Identify the computable interpolant's `toPoly` with the Mathlib Lagrange interpolant,
  -- which equals `p` by uniqueness of low-degree interpolation.
  rw [interpolationDecoder, hbridge, CLagrange.cinterpolate_eq_interpolate,
    ← Lagrange.eq_interpolate_of_eval_eq w hinj hdeg hval]

/-- Executable known-erasure Reed--Solomon decoder.  It interpolates on the actual
non-erased finset, reads the first `k` coefficients, and accepts only if re-encoding
agrees with every retained coordinate. -/
def rsErasureDecoder [Fintype ι] (k : ℕ) (domain : ι ↪ F)
    (nodes : Finset ι) (w : ι → F) : Option (Fin k → F) :=
  if k ≤ nodes.card then
    let m := interpolationDecoder k nodes domain w
    if ∀ j ∈ nodes, rsEncoder k domain m j = w j then some m else none
  else none

/-- Deterministic totalization used by the RBR extractor.  Correctness shows that the
zero fallback is unreachable on the good transition event. -/
def rsErasureDecodeOrZero [Fintype ι] (k : ℕ) (domain : ι ↪ F)
    (nodes : Finset ι) (w : ι → F) : Fin k → F :=
  (rsErasureDecoder k domain nodes w).getD 0

/-- Full recovery contract for `rsErasureDecoder`: at least `k` retained distinct nodes
whose values agree with a degree-`< k` RS word recover that word's coefficient message. -/
theorem rsErasureDecoder_eq_some [Fintype ι] {k : ℕ} {domain : ι ↪ F}
    {nodes : Finset ι} {w : ι → F} {m : Fin k → F}
    (hcard : k ≤ nodes.card)
    (hval : ∀ j ∈ nodes, rsEncoder k domain m j = w j) :
    rsErasureDecoder k domain nodes w = some m := by
  have hdecode : interpolationDecoder k nodes domain w = m := by
    funext j
    rw [interpolationDecoder_eq_coeff domain.injective.injOn
      ((rsPolynomial_degree_lt k m).trans_le (WithBot.coe_le_coe.mpr hcard))
      (fun i hi ↦ by simpa using hval i hi) j]
    exact rsPolynomial_coeff k m j
  rw [rsErasureDecoder, if_pos hcard, hdecode, if_pos hval]

theorem rsErasureDecodeOrZero_eq [Fintype ι] {k : ℕ} {domain : ι ↪ F}
    {nodes : Finset ι} {w : ι → F} {m : Fin k → F}
    (hcard : k ≤ nodes.card)
    (hval : ∀ j ∈ nodes, rsEncoder k domain m j = w j) :
    rsErasureDecodeOrZero k domain nodes w = m := by
  rw [rsErasureDecodeOrZero, rsErasureDecoder_eq_some hcard hval]
  rfl

/-- The source-faithful maximal agreement set computed after `γ` and `g` are known. -/
def gammaAgreementSet [Fintype ι] {k : ℕ} (encode : (Fin k → F) → (ι → F))
    (f₁ f₂ : ι → F) (γ : F) (g : Fin k → F) : Finset ι :=
  Finset.univ.filter (fun j ↦ encode g j = f₁ j + γ • f₂ j)

omit [DecidableEq ι] [BEq F] [LawfulBEq F] in
@[simp]
theorem mem_gammaAgreementSet [Fintype ι] {k : ℕ}
    {encode : (Fin k → F) → (ι → F)}
    {f₁ f₂ : ι → F} {γ : F} {g : Fin k → F} {j : ι} :
    j ∈ gammaAgreementSet encode f₁ f₂ γ g ↔
      encode g j = f₁ j + γ • f₂ j := by
  simp [gammaAgreementSet]

end ToyProblem.Spec


