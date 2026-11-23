-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:13.983019+00:00
-- url     : https://prove2.me/theorems/7bfa0328-8bce-4846-9b9b-7a970e8b8d5f
-- title:
--   Elliptic Functions
-- statement:
--   Definitions and structural lemmas for Elliptic Functions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
variable (L : PeriodPair)
instance isClosed_lattice_toAddSubgroup : IsClosed (L.lattice.toAddSubgroup : Set ℂ) :=
  L.isClosed_lattice
abbrev Torus : Type := ℂ ⧸ L.lattice.toAddSubgroup
abbrev Torus.mk (z : ℂ) : Torus L := QuotientAddGroup.mk z
lemma Torus.mk_add {z l : ℂ} (hl : l ∈ L.lattice) : Torus.mk L (z + l) = Torus.mk L z :=
  QuotientAddGroup.mk_add_of_mem z hl
lemma Torus.mk_surjective : Function.Surjective (Torus.mk L) :=
  QuotientAddGroup.mk_surjective
lemma Torus.continuous_mk : Continuous (Torus.mk L) :=
  continuous_quot_mk
def IsPeriodic {E : Type*} (f : ℂ → E) : Prop :=
  ∀ z : ℂ, ∀ l ∈ L.lattice, f (z + l) = f z
def IsEllipticFunction (f : ℂ → ℂ) : Prop :=
  Meromorphic f ∧ IsPeriodic L f
variable {L}
variable (L)
instance : CompactSpace (Torus L) := by
  have h := IsZLattice.isCompact_range_of_periodic L.lattice (Torus.mk L) (Torus.continuous_mk L)
    (fun z w hw ↦ Torus.mk_add L hw)
  rw [(Torus.mk_surjective L).range_eq] at h
  exact isCompact_univ_iff.mp h
instance : T2Space (Torus L) := inferInstance
instance : IsTopologicalAddGroup (Torus L) := inferInstance
def fundamentalCompact : Set ℂ := closure (ZSpan.fundamentalDomain L.basis)
variable {L}
def singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) : Set ℂ :=
  {z | ¬ AnalyticAt ℂ f z}
def poles {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) : Set ℂ :=
  {z | meromorphicOrderAt f z < 0}
variable (L)
end Elliptic
end GroundTheory.Global


