-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicLattices
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicLattices
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:30:29.187231+00:00
-- url     : https://prove2.me/theorems/922557de-6eb0-4715-b7cb-2b0d312d5dee
-- title:
--   Statements Adelic Lattices
-- statement:
--   Definitions and structural lemmas for Statements Adelic Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsAdelicLattices.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def AdelicLatticeDictionary.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∃ (K : Subgroup (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) (D : ℕ)
    (L : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) → AddSubgroup W),
    IsCompact (K : Set (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) ∧
    IsOpen (K : Set (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) ∧
    (∀ g, IsDIntegral h D (L g)) ∧
    (∀ (γ : h.unitaryGroup) g, L ((adeleSplit h v (hermitianDiagonal h v γ)).2 * g) = γ • L g) ∧
    ∀ g g', L g = L g' ↔ g⁻¹ * g' ∈ K
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


