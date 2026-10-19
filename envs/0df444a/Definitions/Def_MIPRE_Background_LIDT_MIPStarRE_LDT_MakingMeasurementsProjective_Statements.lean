-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:19:51.310222+00:00
-- url     : https://prove2.me/theorems/67d5c3c3-b6ea-411c-95a1-fc5e38f3c29f
-- title:
--   Definitions of Statements: Section 5 — Statements Statements for Naimark dilation, one-measurement Naimark, the orthogonalization lemma, rounding…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Statements` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Statements. Statements for Naimark dilation, one-measurement Naimark, the orthogonalization lemma, rounding to projectors, rank reduction, and completing to measurement.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (7): `MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement` (Paper origin: `references/ldt-paper/preliminaries.tex:348-376` (`\label{def:approx_delta}`) and…); `MIPStarRE.LDT.MakingMeasurementsProjective.RoundedProjMeasStatement` (Paper origin: `references/ldt-paper/orthonormalization.tex:414-538` (`\label{lem:projective-non-measurement}`).); `MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncationStatement` (Paper origin: `references/ldt-paper/orthonormalization.tex:414-538` (`\label{lem:projective-non-measurement}`); the truncation-function…); `MIPStarRE.LDT.MakingMeasurementsProjective.naimarkProductExtensionDensity` (The density matrix of `ψ ⊗ aux`, written in the register order used by the paper's dilated measurements: `(Alice × AliceAux) × (Bob ×…); `MIPStarRE.LDT.MakingMeasurementsProjective.naimarkProductExtensionEquiv` (The canonical register permutation from `(Alice × Bob) × (AliceAux × BobAux)` to `(Alice × AliceAux) × (Bob × BobAux)`.); `MIPStarRE.LDT.MakingMeasurementsProjective.naimarkProductExtensionState` (The quantum state `ψ ⊗ aux` in the register order used by the full Naimark correlation theorem.); `MIPStarRE.LDT.MakingMeasurementsProjective.optionCompletion` (Complete a submeasurement by adjoining the residual `I - ∑ₐ Aₐ` at the fresh `none` outcome.).
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `naimarkProductExtensionDensity_eq_reindex_opTensor`, `naimarkProductExtensionDensity_nonneg`, `naimarkProductExtensionState_density`, `optionCompletion_outcome_none`, `optionCompletion_outcome_some`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Statements` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Theorems.Thm_MIPStarRE_Quantum_reindex_nonneg

set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — Statements

Statements for Naimark dilation, one-measurement Naimark, the
orthogonalization lemma, rounding to projectors, rank reduction, and completing
to measurement.

## Naimark dilation statements

The **one-measurement Naimark lemma** (`OneMeasNaimarkLemma`) is the
building block: any submeasurement can be dilated to a projective
submeasurement on a space enlarged by one auxiliary register.

The questionwise **Naimark interface** (`NaimarkStatement`) records the
per-question one-measurement dilations and their single-outcome marginal
preservation identities.  It is not the full tensor-product statement of
`\label{thm:naimark}`.

The source theorem form is recorded separately as
`NaimarkTensorProductCorrelationStatement` and
`naimarkTensorProductCorrelation`.  This statement contains the full
bipartite auxiliary-state and correlation-preservation conclusion of
`\label{thm:naimark}` in the projective-submeasurement form supplied by the
paper's one-measurement helper.  The proof is the tensor-product assembly
implemented in `NaimarkFull.lean`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe u

/-! ### One-measurement Naimark statement -/

/-! ### Questionwise Naimark interface -/

/-! ### Tensor-product Naimark source theorem -/

/-- The density matrix of `ψ ⊗ aux`, written in the register order used by the
paper's dilated measurements:
`(Alice × AliceAux) × (Bob × BobAux)`.

The source paper writes the dilated vector as
`\ket{\widehat{\psi}} = \ket{\psi} \otimes \ket{\mathsf{aux}}`.  Since the
local dilated measurements act on `Alice × AliceAux` and `Bob × BobAux`, the
matrix entries below are the corresponding tensor-product density after the
canonical reassociation and permutation of the four finite registers. -/
noncomputable def naimarkProductExtensionDensity
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    MIPStarRE.Quantum.Op
      ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) :=
  fun r c =>
    ψ.density (r.1.1, r.2.1) (c.1.1, c.2.1) *
      aux.density (r.1.2, r.2.2) (c.1.2, c.2.2)

/-- The canonical register permutation from
`(Alice × Bob) × (AliceAux × BobAux)` to
`(Alice × AliceAux) × (Bob × BobAux)`. -/
def naimarkProductExtensionEquiv
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u}) :
    ((HA.carrier × HB.carrier) × (HauxA.carrier × HauxB.carrier)) ≃
      ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) :=
  Equiv.prodProdProdComm HA.carrier HB.carrier HauxA.carrier HauxB.carrier

/-- The product-extension density is the ordinary tensor-product density after
the register permutation used by the dilated measurements. -/
theorem naimarkProductExtensionDensity_eq_reindex_opTensor
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux =
      Matrix.reindex (naimarkProductExtensionEquiv HA HB HauxA HauxB)
        (naimarkProductExtensionEquiv HA HB HauxA HauxB)
        (opTensor ψ.density aux.density) := by
  ext r c
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The product-extension density is positive semidefinite. -/
theorem naimarkProductExtensionDensity_nonneg
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    0 ≤ naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux := by
  rw [naimarkProductExtensionDensity_eq_reindex_opTensor]
  exact MIPStarRE.Quantum.reindex_nonneg (naimarkProductExtensionEquiv HA HB HauxA HauxB)
    (opTensor_nonneg ψ.density_psd aux.density_psd)

/-- The quantum state `ψ ⊗ aux` in the register order used by the full Naimark
correlation theorem. -/
noncomputable def naimarkProductExtensionState
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    QuantumState ((HA.carrier × HauxA.carrier) × (HB.carrier × HauxB.carrier)) where
  density := naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux
  density_psd := naimarkProductExtensionDensity_nonneg HA HB HauxA HauxB ψ aux

@[simp] theorem naimarkProductExtensionState_density
    (HA HB HauxA HauxB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (aux : QuantumState (HauxA.carrier × HauxB.carrier)) :
    (naimarkProductExtensionState HA HB HauxA HauxB ψ aux).density =
      naimarkProductExtensionDensity HA HB HauxA HauxB ψ aux := rfl

/-! ### Orthonormalization statements -/

/-- Paper origin: `references/ldt-paper/preliminaries.tex:348-376`
(`\label{def:approx_delta}`) and `references/ldt-paper/orthonormalization.tex`
§4 prose around `\label{lem:projective-non-measurement}` (lines 414-538).

Conclusion of the intermediate almost-projective step: a measurement which is
ζ-strongly self-consistent and ζ-self-close in the state-dependent distance,
and whose effects satisfy `Σₐ (Aₐ − Aₐ²) ≤ ζ`. -/
structure AlmostProjMeasStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) : Prop where
  strongSelfConsistency :
    SSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ
  selfDistance :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily A.toSubMeas)
      (2 * ζ)
  sourceAlmostProjective :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-538`
(`\label{lem:projective-non-measurement}`); the truncation-function `trunc_δ`
itself is introduced inside the proof at lines 434-444, with the supporting
inequality `\label{lem:trunc-inequality}` at line 447.

Conclusion of the truncation-function step in the proof of rounding to
projectors. -/
structure SpectralTruncationStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) where
  /-- The operator family obtained by applying the truncation function to each effect. -/
  roundedFamily : OpFamily Outcome ι
  /-- Each truncated effect is a projection. -/
  projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (roundedFamily.outcome a)
  /-- The truncated family stays close to the input measurement in
  state-dependent operator distance, with the paper's `2√ζ` bound
  (`references/ldt-paper/orthonormalization.tex:417`). -/
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (fun _ => (A.toSubMeas : OpFamily Outcome ι))
      (fun _ => roundedFamily)
      (2 * spectralTruncationError ζ)
  /-- The stored total operator is the sum of the rounded family. -/
  sum_eq_total : ∑ a, roundedFamily.outcome a = roundedFamily.total
  /-- The total operator of the rounded family is almost bounded by `I`. -/
  total_le :
    roundedFamily.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-538`
(`\label{lem:projective-non-measurement}`).

Conclusion of the rounding-to-projective step: a genuine projective
sub-measurement `P` which is `ζ`-close to the input measurement `A` in the
state-dependent operator distance. -/
structure RoundedProjMeasStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (P : ProjSubMeas Outcome ι) (ζ : Error) : Prop where
  closeness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily P.toSubMeas)
      ζ

/-- Complete a submeasurement by adjoining the residual `I - ∑ₐ Aₐ` at the
fresh `none` outcome.

This is the completion used in the paper's proof of
`thm:orthonormalization`: the original outcomes are kept as `some a`, and the
missing mass is recorded separately at `none`. -/
noncomputable def optionCompletion {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) : Measurement (Option Outcome) ι where
  toSubMeas :=
    { outcome := fun
        | none => 1 - A.total
        | some a => A.outcome a
      total := 1
      outcome_pos := fun
        | none => sub_nonneg.mpr A.total_le_one
        | some a => A.outcome_pos a
      sum_eq_total := (Fintype.sum_option _).trans <|
        (congrArg (1 - A.total + ·) A.sum_eq_total).trans (sub_add_cancel 1 A.total)
      total_le_one := le_rfl }
  total_eq_one := rfl

@[simp] lemma optionCompletion_outcome_none {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) :
    (optionCompletion A).outcome none = 1 - A.total := rfl

@[simp] lemma optionCompletion_outcome_some {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a : Outcome) :
    (optionCompletion A).outcome (some a) = A.outcome a := rfl

end MIPStarRE.LDT.MakingMeasurementsProjective


