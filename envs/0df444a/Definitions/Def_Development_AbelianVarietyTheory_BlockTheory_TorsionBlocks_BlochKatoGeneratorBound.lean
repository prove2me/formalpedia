-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BlochKatoGeneratorBound
-- name    : Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BlochKatoGeneratorBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:19.487837+00:00
-- url     : https://prove2.me/theorems/2598b587-74d4-498e-8241-1640e77e8e54
-- title:
--   Bloch Kato Generator Bound
-- statement:
--   Definitions and structural lemmas for Bloch Kato Generator Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/BlochKatoGeneratorBound.lean

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
section Reduction
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
def latAct (L : Lattice (O := O) ρ) (g : G) : ↥L.T →ₗ[O] ↥L.T :=
  ((ρ g).restrictScalars O).restrict (fun x hx => L.stable g x hx)
abbrev LatMod (L : Lattice (O := O) ρ) (I : Ideal O) : Type :=
  ↥L.T ⧸ (I • (⊤ : Submodule O ↥L.T))
def latModAct (L : Lattice (O := O) ρ) (I : Ideal O) (g : G) : LatMod L I →ₗ[O] LatMod L I :=
  Submodule.mapQ _ _ (latAct L g) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)
def galoisLatticeModIdealInvariants (L : Lattice (O := O) ρ) (I : Ideal O) : Submodule (O ⧸ I) (LatMod L I) where
  carrier := {y | ∀ g : G, latModAct L I g y = y}
  zero_mem' := fun g => map_zero _
  add_mem' := by
    intro a b ha hb g
    rw [map_add, ha g, hb g]
  smul_mem' := by
    intro c y hy g
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    change latModAct L I g (a • y) = a • y
    rw [map_smul, hy g]
def h0ModResidueDim (L : Lattice (O := O) ρ) (ϖ : O) : ℕ :=
  Module.finrank (O ⧸ Ideal.span {ϖ}) ↥(galoisLatticeModIdealInvariants L (Ideal.span {ϖ}))
end Reduction
def GeneratedByAtMost {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (N : Submodule O M) (m : ℕ) : Prop :=
  ∃ s : Finset M, Submodule.span O (s : Set M) = N ∧ s.card ≤ m
section Bound
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
def GeneratorBound (PD : PeriodData G Qp K₀ K B BdR) (T : LocLat G Qp LL O) (ϖ : O) : Prop :=
  GeneratedByAtMost (latticeFiniteCohomology PD T.L)
      (Module.finrank Qp K * Module.finrank O ↥T.L.T + h0ModResidueDim T.L ϖ) ∧
    Module.finrank Qp K * Module.finrank O ↥T.L.T + h0ModResidueDim T.L ϖ ≤
      (Module.finrank Qp K + 1) * Module.finrank O ↥T.L.T
end Bound
def H1fGeneratorBoundAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : FinExt l), CaseA K LL →
    ∀ ϖ : ↥(OL LL), Irreducible ϖ →
      ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ →
        GeneratorBound (P.PD K) T ϖ
def H1fGeneratorBoundAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), H1fGeneratorBoundAt P
end GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions


