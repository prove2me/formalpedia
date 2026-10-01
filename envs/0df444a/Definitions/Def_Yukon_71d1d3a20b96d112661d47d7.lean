-- Prove2me | Definitions.Def_Yukon_71d1d3a20b96d112661d47d7
-- name    : Yukon_71d1d3a20b96d112661d47d7
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:54:58.775902+00:00
-- url     : https://prove2.me/theorems/cb1e5a3d-27ce-496f-8447-72720889df95
-- title:
--   YukonModule.ArkLib.ProofSystem.ToyProblem.Leaderboard.part0
-- statement:
--   Source module ArkLib.ProofSystem.ToyProblem.Leaderboard. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ProofSystem/ToyProblem/Leaderboard.lean
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ProofSystem/ToyProblem/Leaderboard.lean
--
--   yukon-proof-operation:5c6d1bf5b8f85f16b4aafc5eedecfe0d3fb653857906cf17d11eb4111aaece70
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTVmNGNlN2Q5ZjgyZjhhNzI4Nzg4NTVjZDliZjUzYmY4YTRmODNmOGU4NDg5OWMzNWQ2ZjA0NjcxMmUxZjA5YyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjVjNmQxYmY1YjhmODVmMTZiNGFhZmM1ZWVkZWNmZTBkM2ZiNjUzODU3OTA2Y2YxN2QxMWViNDExMWFhZWNlNzAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83MWQxZDNhMjBiOTZkMTEyNjYxZDQ3ZDciLCJ2IjoyfQ]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Definitions.Def_Yukon_f9f75c203e12e22a1b2b52a1

import Definitions.Def_Yukon_c3fcb43d1ba4a8df9eead5d4




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
import Mathlib.Tactic.ComputeDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_Yukon_06fd17bede7d9846a07acaa7
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
import Definitions.Def_Yukon_8d2d9b1245cbb497a9fbffbf
import Definitions.Def_Yukon_6b274c76f1610f2d89b18673
import Definitions.Def_Yukon_f6ef87da37ae124e79421110
import Definitions.Def_Yukon_73cb364285b0db29404203c2
import Definitions.Def_Yukon_84b1a34b80631e562026cc16
set_option backward.isDefEq.respectTransparency.types false
/-!
# Neutral fixed-radius reference interface for the toy problem

This is a small façade over the reusable toy-problem mathematics.  It packages
an encoder, its code and repetition count, and gives stable projections for the
winning-set/spot-check upper bound and the executable extractor's MCA-plus-list
certificate.  It intentionally contains no score format, ranking direction,
submission metadata, or chosen operating radius.

**Verified vs. admitted.**  Both projections below are `sorry`-free and are *symbolic*:
`certifiedExtractorError` unfolds to `ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F| `-shaped data, not to a
numeral.  Instantiating a `FixedRadiusParameters` therefore asserts nothing numeric about a
parameter point; obtaining a numeral additionally requires the MCA/CA capacity bounds under
`Data/CodingTheory/ProximityGap/CapacityBounds` (several proven, the rest external admits),
which are deliberately outside this file's import cone (see the "Verified vs. admitted"
section of `Spec/General.lean` and the numeric-route notes in `Impl/IRS.lean`).
-/

namespace ToyProblem

open Code
open scoped NNReal

variable {ι F A : Type} [Fintype ι] [Field F] [Fintype F]
variable [AddCommGroup A] [Module F A] [Fintype A]

/-- Neutral parameters needed to state a fixed-radius toy-protocol bound. -/
structure FixedRadiusParameters where
  k : ℕ
  t : ℕ
  code : ModuleCode ι F A
  encoder : (Fin k → F) →ₗ[F] (ι → A)
  encoder_injective : Function.Injective encoder
  encoder_range : Set.range encoder = (code : Set (ι → A))

/-- A concrete inhabitant of the neutral fixed-radius façade, built from the
proved Ext6 folded-RS geometric-progression reference point with `s = 32`,
`k = 2^20`, and `t = 128`.

This packages exactly the encoder, range, and injectivity facts required by
`FixedRadiusParameters`; it does not add the smooth base-field provenance or
the numerical security certificate of the separate protected prize profile. -/
noncomputable def FixedRadiusParameters.koalaFRS :
    FixedRadiusParameters
      (ι := Fin (2 ^ 16)) (F := KoalaBear.Ext6)
      (A := Fin 32 → KoalaBear.Ext6) where
  k := 2 ^ 20
  t := 128
  code := ReedSolomon.Folded.frsCode Impl.FRS.domain (2 ^ 20) 32
    Impl.FRS.foldOmega
  encoder := Impl.FRS.encoder
  encoder_injective := Impl.FRS.encoder_injective
  encoder_range := Impl.FRS.encoder_range

/-! ### Scope: no in-tree interleaved-RS inhabitant

The façade's one in-tree inhabitant is folded-RS, even though the executable extractor
(`Impl.IRS.straightlineExtractor`) is interleaved-RS.  The concrete interleaved profile —
smooth base-field evaluation domain, production parameter shape, and any numeric
certificate — is realized in the downstream prize-challenge repository from
`Impl.IRS.encoder`/`encoder_injective`/`encoder_range` and this structure; a second copy
here would fork that protected profile and its domain construction. -/

/-- The certified winning-set/spot-check upper bound for a neutral parameter point. -/
noncomputable def FixedRadiusParameters.winningSetUpperBound
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : ℝ≥0 :=
  ToyProblem.winningSetUpperBound p.encoder δ p.t

/-- The MCA-plus-list/spot-check certificate used by the executable extractor. -/
noncomputable def FixedRadiusParameters.certifiedExtractorError
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : ℝ≥0 :=
  ToyProblem.certifiedExtractorError p.code δ p.t

omit [Fintype A] in
/-- At every admissible radius, the winning-set/spot-check upper bound is
bounded by the executable extractor certificate. -/
theorem FixedRadiusParameters.winningSetUpperBound_le_certifiedExtractorError
    [Finite A] [DecidableEq A] [Nonempty ι]
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0)
      ((minRelHammingDistCode (p.code : Set (ι → A)) : ℝ≥0))) :
    p.winningSetUpperBound δ ≤ p.certifiedExtractorError δ := by
  classical
  letI := Fintype.ofFinite A
  letI : DecidableEq F := Classical.decEq F
  exact ToyProblem.winningSetUpperBound_le_certifiedExtractorError
    p.code δ p.t hδ p.encoder p.encoder_injective p.encoder_range

/-- A neutral carrier for a proved upper bound on the executable extractor's
fixed-radius certificate.

**The carrier is directional, and inhabitation alone asserts nothing.**  The field
`proof` is `certifiedExtractorError δ ≤ bound`, so *every* weaker `bound` qualifies and
`FixedRadiusCertificateBound.self` inhabits it unconditionally at the exact certificate.
A **smaller** `bound` is the stronger statement.  Any downstream policy layer must
therefore compare the numerals in `bound` and must not treat "this parameter point has a
`FixedRadiusCertificateBound`" as a security claim. -/
structure FixedRadiusCertificateBound
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) where
  bound : ℝ≥0
  proof : p.certifiedExtractorError δ ≤ bound

/-- The bound carrier is non-vacuous: the exact certificate always supplies a
canonical inhabitant. -/
noncomputable def FixedRadiusCertificateBound.self
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : FixedRadiusCertificateBound p δ :=
  ⟨p.certifiedExtractorError δ, le_rfl⟩

end ToyProblem


