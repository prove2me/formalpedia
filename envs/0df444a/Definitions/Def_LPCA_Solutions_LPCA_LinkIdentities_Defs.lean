-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LinkIdentities_Defs
-- name    : LPCA_Solutions_LPCA_LinkIdentities_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:21:32.833781+00:00
-- url     : https://prove2.me/theorems/9639742c-e0c1-443e-bc6f-c020fa08b9e4
-- title:
--   Link Identities for localized persistent commutative algebra
-- statement:
--   This bundle supplies link Identities for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The first link identity in Corollary 2.10; the face being linked lies in the complement of the distinguished vertex.
--   - The iterated link is the link of the union, retaining void complexes when either linking face does not occur.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LinkIdentities.lean, selected declarations in lines 11–46; source SHA-256 0a581f69f32f9867460c1d973481b8a374c6279350459557a065c95caff79cb0; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]

theorem Complex.ext_faces {K L : Complex V} (h : K.faces = L.faces) : K = L := by
  cases K
  cases L
  cases h
  rfl

/-- The first link identity in Corollary 2.10; the face being linked
lies in the complement of the distinguished vertex. -/
theorem link_deletion (K : Complex V) (i : V) (σ : Finset V) (hσ : i ∉ σ) :
    link (deletion K i) σ = deletion (link K σ) i := by
  apply Complex.ext_faces
  ext F
  simp only [link, deletion, Finset.mem_filter, Finset.mem_union, not_or]
  tauto

/-- The iterated link is the link of the union, retaining void complexes
when either linking face does not occur. -/
theorem link_link_singleton (K : Complex V) (i : V) (σ : Finset V) (hσ : i ∉ σ) :
    link (link K {i}) σ = link K (σ ∪ {i}) := by
  apply Complex.ext_faces
  ext F
  simp only [link, Finset.mem_filter, Finset.disjoint_union_right,
    Finset.disjoint_singleton_right, Finset.mem_union, not_or, Finset.union_assoc]
  constructor
  · rintro ⟨⟨hFK, hiF, hFi⟩, hd, hFs, hiFs, hFsi⟩
    exact ⟨hFK, ⟨hd, hiF⟩, hFsi⟩
  · rintro ⟨hFK, ⟨hd, hiF⟩, hFsi⟩
    have hFi : F ∪ {i} ∈ K.faces := K.down_closed hFsi (by
      intro v hv
      simp only [Finset.mem_union, Finset.mem_singleton] at hv ⊢
      tauto)
    have hFs : F ∪ σ ∈ K.faces := K.down_closed hFsi (by
      intro v hv
      simp only [Finset.mem_union] at hv ⊢
      tauto)
    exact ⟨⟨hFK, hiF, hFi⟩, hd, hFs, ⟨hiF, hσ⟩, hFsi⟩

end LPCA


