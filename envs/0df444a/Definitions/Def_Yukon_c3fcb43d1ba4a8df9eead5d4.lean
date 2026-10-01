-- Prove2me | Definitions.Def_Yukon_c3fcb43d1ba4a8df9eead5d4
-- name    : Yukon_c3fcb43d1ba4a8df9eead5d4
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:52:08.763671+00:00
-- url     : https://prove2.me/theorems/11a7b85d-9f79-44ec-aa0b-6fa589aa2a35
-- title:
--   YukonModule.ArkLib.ProofSystem.ToyProblem.Impl.IRS.part0
-- statement:
--   Source module ArkLib.ProofSystem.ToyProblem.Impl.IRS. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean
--
--   yukon-proof-operation:87e2f055a0c586ad62abffa6b8be55ba2757da1abd82ee87445f6a24125adcd8
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiM2MzOGMwMGEzMzlkZTQ4ZDY0MTdjYzAyMjY4OWUzMzQ5N2YxZTBlY2Y0OWM3NDQ0YmIxMTYxMWI4NTMyMmQ2NiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjg3ZTJmMDU1YTBjNTg2YWQ2MmFiZmZhNmI4YmU1NWJhMjc1N2RhMWFiZDgyZWU4NzQ0NWY2YTI0MTI1YWRjZDgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jM2ZjYjQzZDFiYTRhOGRmOWVlYWQ1ZDQiLCJ2IjoyfQ]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Definitions.Def_Yukon_95e1f6c57ba6527ee61187a2

import Definitions.Def_Yukon_5af2022acebdca615a0a04f9



import Definitions.Def_Yukon_8d2d9b1245cbb497a9fbffbf



import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Init
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.CompletePartialOrder
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
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
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Batteries.Tactic.Lint
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Batteries.Control.Lemmas
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
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_Yukon_30e807a5525bb5bfbcd8d7fe
import Definitions.Def_Yukon_13abd70b92beced94bdb4981
import Definitions.Def_Yukon_8f2c8c65169aeb35b0e3b51b
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
import Definitions.Def_Yukon_950ab98b4aafc32b0f064af3
import Definitions.Def_Yukon_b274322d0e11762f90f047d3
import Definitions.Def_Yukon_6b274c76f1610f2d89b18673
import Definitions.Def_Yukon_f6ef87da37ae124e79421110
import Definitions.Def_Yukon_73cb364285b0db29404203c2
import Definitions.Def_Yukon_84b1a34b80631e562026cc16
set_option backward.isDefEq.respectTransparency.types false
/-!
# Executable interleaved Reed--Solomon implementation for the toy problem

This file realizes the toy problem over the genuine interleaved alphabet `Fin s → F`.
A length-`k` scalar message is split into `s` rows of length `k / s`, each row is encoded
by the scalar Reed--Solomon encoder, and the resulting rows are exposed column-wise.

The divisibility hypothesis `s ∣ k` is part of every flattening API.  Consequently the
executable encoder has exactly `k` scalar input coordinates and its range is the current
`ReedSolomon.Interleaved.irsCode domain k s`, without silently dropping a remainder.

The definitions in the extraction path are computable.  Proofs may use classical logic,
but no proof-side choice is called by the encoder, decoder, agreement-set computation, or
transition extractor.

## Distance from here to a numeric knowledge error

Everything proven below is parametric: the shipped error keeps `ε_mca(C,δ)` and
`Λ(C^{≡2},δ)` symbolic, so no numeral is asserted at any parameter shape (see the
"Verified vs. admitted" section of `Spec/General.lean`).  For this interleaved-RS profile
the route to a numeral is short, and it is worth recording exactly what is missing:

* **MCA term.**  `ProximityGap.mcaError_interleaved_eq` (`ProximityGap/Errors.lean`,
  `sorry`-free) collapses the interleaved MCA error to the scalar one, so at radius
  `δ ∈ (0,1)` the `s`-interleaved code inherits the RS bound at message length `k / s`.
  In the Johnson range the scalar bound, `rs_mcaError_le_in_johnson_range`
  (`ProximityGap/CapacityBounds.lean`), is the **one external admit** on this path
  ([BCHKS25, Thm 4.6]); at smaller radii the proven
  `linear_mcaError_le_one_point_five_johnson`
  (`ProximityGap/CapacityBounds/JohnsonMca.lean`) already supplies an admit-free bound.
* **List term.**  Fully proven route, no admits:
  `ListDecodability.lambda_interleaved_le_choose_mul_pow` composed with
  `irs_lambda_le_johnson_mds` (both in `sorry`-free files), with
  `ReedSolomon.Interleaved.minDist_irsCode` supplying the relative-distance input.  What
  is missing is only real-arithmetic glue, not a mathematical input.
* **Coercions.**  The `ENNReal → ℝ≥0` bridges needed to land the two terms in the
  error type are proven.

So a numeric §6.4-shaped corollary would rest on exactly one external admit.  It is
deliberately not stated here.  Beyond the import-cone quarantine, the live downstream
consumer of these theorems cannot use an admit-backed numeral at all: it enforces a
transitive axiom closure of exactly `propext`, `Classical.choice`, `Quot.sound`, and it
reaches a numeric bound by a different, fully axiom-clean route — ArkLib's *unique-decoding*
correlated-agreement bound transported through interleaving, rather than the Johnson-range
MCA admit.  An admit-backed corollary here would therefore be a weaker-provenance parallel
route to the same quantity.  Any future numeric claim in-tree should adopt
`CapacityBounds.lean`'s "external admit unless stated" convention rather than pull that file
into the launch cone.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26], §6 (the interleaved-RS instantiation and the
  Appendix A.1 erasure-decoding extractor realized executably here).
-/

namespace ToyProblem.Impl.IRS

open Code InterleavedCode CoreDefinitions
open Probability
open scoped NNReal ProbabilityTheory

variable {ι F : Type} [DecidableEq ι] [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]

/-- Row-major equivalence between `s` rows of length `k / s` and a length-`k`
message.  The proof argument records that no coordinates are lost to division. -/
def indexEquiv (k s : ℕ) (hdvd : s ∣ k) : Fin s × Fin (k / s) ≃ Fin k :=
  finProdFinEquiv.trans (finCongr (Nat.mul_div_cancel' hdvd))

/-- Split a length-`k` scalar message into `s` rows of length `k / s`. -/
def unflatten (k s : ℕ) (hdvd : s ∣ k) (m : Fin k → F) :
    Fin s → Fin (k / s) → F :=
  fun row col ↦ m (indexEquiv k s hdvd (row, col))

/-- Join `s` rows of length `k / s` into a length-`k` scalar message. -/
def flatten (k s : ℕ) (hdvd : s ∣ k) (rows : Fin s → Fin (k / s) → F) :
    Fin k → F :=
  fun j ↦ rows ((indexEquiv k s hdvd).symm j).1
    ((indexEquiv k s hdvd).symm j).2

omit [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem unflatten_flatten (k s : ℕ) (hdvd : s ∣ k)
    (rows : Fin s → Fin (k / s) → F) :
    unflatten k s hdvd (flatten k s hdvd rows) = rows := by
  funext row col
  simp [unflatten, flatten]

omit [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem flatten_unflatten (k s : ℕ) (hdvd : s ∣ k) (m : Fin k → F) :
    flatten k s hdvd (unflatten k s hdvd m) = m := by
  funext j
  simp [unflatten, flatten]

omit [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] in
theorem unflatten_injective (k s : ℕ) (hdvd : s ∣ k) :
    Function.Injective (unflatten (F := F) k s hdvd) := by
  intro m₁ m₂ h
  rw [← flatten_unflatten k s hdvd m₁, ← flatten_unflatten k s hdvd m₂, h]

/-- Executable `s`-interleaved Reed--Solomon encoder.  Its public alphabet is
`Fin s → F`; interleaving is not modeled by enlarging the word-position type. -/
def encoder (k s : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    (Fin k → F) →ₗ[F] (ι → Fin s → F) :=
  { toFun := fun m j row ↦
      Spec.rsEncoder (k / s) domain (unflatten k s hdvd m row) j
    map_add' := by
      intro m₁ m₂
      ext j row
      rw [show unflatten k s hdvd (m₁ + m₂) row =
        unflatten k s hdvd m₁ row + unflatten k s hdvd m₂ row by rfl]
      exact congrFun (map_add (Spec.rsEncoder (k / s) domain)
        (unflatten k s hdvd m₁ row) (unflatten k s hdvd m₂ row)) j
    map_smul' := by
      intro c m
      ext j row
      rw [show unflatten k s hdvd (c • m) row =
        c • unflatten k s hdvd m row by rfl]
      exact congrFun (map_smul (Spec.rsEncoder (k / s) domain) c
        (unflatten k s hdvd m row)) j }

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem encoder_apply (k s : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F)
    (m : Fin k → F) (j : ι) (row : Fin s) :
    encoder k s hdvd domain m j row =
      Spec.rsEncoder (k / s) domain (unflatten k s hdvd m row) j := rfl

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The executable encoder has exactly the canonical interleaved Reed--Solomon code
as its range. -/
theorem encoder_range (k s : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    Set.range (encoder k s hdvd domain) =
      (ReedSolomon.Interleaved.irsCode domain k s : Set (ι → Fin s → F)) := by
  ext w
  constructor
  · rintro ⟨m, rfl⟩
    change ∀ row, (fun j ↦ encoder k s hdvd domain m j row) ∈
      ReedSolomon.code domain (k / s)
    intro row
    change Spec.rsEncoder (k / s) domain (unflatten k s hdvd m row) ∈
      ReedSolomon.code domain (k / s)
    have hmem : Spec.rsEncoder (k / s) domain (unflatten k s hdvd m row) ∈
        (ReedSolomon.code domain (k / s) : Set (ι → F)) := by
      rw [← Spec.rsEncoder_range]
      exact ⟨unflatten k s hdvd m row, rfl⟩
    exact hmem
  · intro hw
    change (∀ row, (fun j ↦ w j row) ∈ ReedSolomon.code domain (k / s)) at hw
    classical
    have hrange : ∀ row, (fun j ↦ w j row) ∈
        Set.range (Spec.rsEncoder (k / s) domain) := by
      intro row
      rw [Spec.rsEncoder_range]
      exact hw row
    choose rows hrows using hrange
    refine ⟨flatten k s hdvd rows, ?_⟩
    funext j row
    change Spec.rsEncoder (k / s) domain
      (unflatten k s hdvd (flatten k s hdvd rows) row) j = w j row
    rw [unflatten_flatten]
    exact congrFun (hrows row) j

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Below scalar-row saturation, the executable interleaved encoder is injective. -/
theorem encoder_injective [Fintype ι] (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) (hcard : k / s ≤ Fintype.card ι) :
    Function.Injective (encoder k s hdvd domain) := by
  intro m₁ m₂ henc
  exact unflatten_injective k s hdvd <| funext fun row ↦
    Spec.rsEncoder_injective hcard <| funext fun j ↦
      congrFun (congrFun henc j) row

variable [Fintype ι] [Fintype F]

noncomputable def certifiedGammaError (k s : ℕ) (domain : ι ↪ F)
    (δ : ℝ≥0) : ℝ≥0 :=
  ToyProblem.certifiedGammaError (ReedSolomon.Interleaved.irsCode domain k s) δ

end ToyProblem.Impl.IRS


