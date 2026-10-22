-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
-- name    : LPCA_Solutions_LPCA_ComplementRings_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:21:24.356989+00:00
-- url     : https://prove2.me/theorems/6c7cc63f-f6d3-411a-957d-f731b93aac01
-- title:
--   Complement Rings for localized persistent commutative algebra
-- statement:
--   This bundle supplies complement Rings for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Restrict a finite face family along an embedding of the remaining vertices.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_ComplementRings.lean, selected declarations in lines 15–165; source SHA-256 556f520bf8ea8ab96c88b637daa2b1a4116b6eeaafa4ca7c5b7de6574f2bc05f; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA

set_option autoImplicit false

namespace LPCA

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W]
variable (k : Type u) [Field k]

/-- Restrict a finite face family along an embedding of the remaining vertices. -/
noncomputable def restrictComplex (K : Complex V) (e : W ↪ V) : Complex W where
  faces := K.faces.preimage (Finset.map e) (Finset.map_injective e).injOn
  down_closed := by
    intro s t hs hts
    apply Finset.mem_preimage.mpr
    exact K.down_closed (Finset.mem_preimage.mp hs) (Finset.map_subset_map.mpr hts)

@[simp] theorem mem_restrictComplex (K : Complex V) (e : W ↪ V) (F : Finset W) :
    F ∈ (restrictComplex K e).faces ↔ F.map e ∈ K.faces :=
  Finset.mem_preimage (hf := (Finset.map_injective e).injOn)

























def complementEmbedding (i : V) : {v : V // v ≠ i} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩





end LPCA


