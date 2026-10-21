-- Prove2me | Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
-- name    : MazurTransfer_OriginalContinuousRationalRootClassData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T23:28:19.656677+00:00
-- url     : https://prove2.me/theorems/96f2c55a-b8b9-4022-aa82-431907929fc9
-- title:
--   Original rational-root representative predicate and coefficient value
-- statement:
--   Retain the original literal mu19 coefficient value and exact rational-root representation predicate in the same continuous H1 presentation. Both complete constructor types and whole values, the original scoped roots module type and whole value, seventeen context types and twelve whole values, and every generated structural proof type are independently checked. Named downstream consumer: the exact class-zero criterion, rational power-ratio comparison and actual pi Selmer radicand map.
-- source:
--   MazurTheorem ContinuousRationalRootClassKernel by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the existing literal mu19 coefficient value and the exact predicate for a rational-root representative in the original continuous H1 presentation. Vanishing criteria are separate theorem interfaces.
No finite-extension hypothesis or global Hilbert 90 surjectivity is used.
Named downstream consumer: rational power-class bounds for the actual
selected pi Selmer subspace.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousUnitRootCohomologyData20261019
import Mathlib.FieldTheory.Galois.Infinite

noncomputable section
namespace MazurTransfer.ContinuousRationalRootClassKernel
open NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousUnitRootCohomology
variable (K : Type) [Field K] [CharZero K]
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K
local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)

def value (x : M) : K := coefficientValue K Γ (rootsRepresentation K) x











def RepresentsRoot (z : continuousCocycles Γ M) (a : ℚˣ) (β : K) : Prop :=
  β ≠ 0 ∧ β ^ 19 = algebraMap ℚ K (a : ℚ) ∧
    ∀ σ : Γ, σ β = value K (Additive.toMul (z.val σ)) * β

variable [IsGalois ℚ K]







end MazurTransfer.ContinuousRationalRootClassKernel
#print axioms MazurTransfer.ContinuousRationalRootClassKernel.value
#print axioms MazurTransfer.ContinuousRationalRootClassKernel.RepresentsRoot
#print axioms MazurTransfer.ContinuousRationalRootClassKernel.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRootClassKernel


