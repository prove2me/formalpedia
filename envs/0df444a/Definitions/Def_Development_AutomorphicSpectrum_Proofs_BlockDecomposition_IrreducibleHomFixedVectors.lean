-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:08.726272+00:00
-- url     : https://prove2.me/theorems/81650fa4-3949-4c66-9477-8a0525d24f07
-- title:
--   Irreducible Hom Fixed Vectors
-- statement:
--   Definitions and structural lemmas for Irreducible Hom Fixed Vectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
namespace GlobalTheory.CompanionTheory.HeckeInj
section Generic
variable {G : Type} [Group G]
def act {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G V) (A : M →ₗ[ℂ] V) : (G →₀ M) →ₗ[ℂ] V :=
  Finsupp.lsum ℂ fun g => ρ g ∘ₗ A
def avg {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K L : Subgroup G)
    [Fintype (K ⧸ L.subgroupOf K)] : V →ₗ[ℂ] V :=
  ∑ q : K ⧸ L.subgroupOf K, ρ ((q.out : K) : G)
def cosetFn (K L : Subgroup G) [Fintype (K ⧸ L.subgroupOf K)] (g x : G) : ℂ :=
  open Classical in
  ∑ q : K ⧸ L.subgroupOf K,
    if (QuotientGroup.mk x : G ⧸ K) = QuotientGroup.mk (((q.out : K) : G) * g) then 1 else 0
end Generic
section Hecke
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
end Hecke
end GlobalTheory.CompanionTheory.HeckeInj


