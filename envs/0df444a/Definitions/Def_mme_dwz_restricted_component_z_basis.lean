-- Prove2me | Definitions.Def_mme_dwz_restricted_component_z_basis
-- name    : mme_dwz_restricted_component_z_basis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T08:52:07.949944+00:00
-- url     : https://prove2.me/theorems/86302893-f325-489e-8c7d-390e40735ad0
-- title:
--   Canonical available-word basis of a restricted Table-2 component
-- statement:
--   Fix a field $K$, a Table-2 row $s$, and an integral scale $m\geq0$. The literal restricted component factor $T_s^{\otimes n_s m}[\widetilde\alpha_s]$ has a canonical basis in its $Z$ mode indexed by exactly the available canonical component words:
--
--   $$
--   \left\{w:\#\{r:\operatorname{left}(w_r)=a\}=n_{s,a}m\text{ for every }a\in\{0,1,2\}\right\}.
--   $$
--
--   The basis is obtained by restricting the canonical word basis of the full component power to the available-word subset and identifying its span with the selected $Z$ subspace. This retains the literal source coordinate labels needed for the standard-form small-block grading and includes $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.4, specialized to Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Theorems.Thm_mme_dwz_table2_component_projection_certificate
import Mathlib.LinearAlgebra.Basis.Submodule

open MME Module

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-- The canonical available-word basis of the actually restricted Z mode. -/
noncomputable def restrictedComponentZBasis
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ) :
    Basis (AvailableComponentWord.{u} s m) K
      ((restrictedComponentPower K s m).V 2) := by
  let b := componentPowerZBasis K s m
  let v : AvailableComponentWord.{u} s m →
      (((canonicalComponentBlock K s).kronPow
        (MME.DWZTable2Counts.component s * m)).V 2) :=
    fun w ↦ b w.1
  have hv : LinearIndependent K v := by
    exact b.linearIndependent.comp
      (fun w : AvailableComponentWord.{u} s m ↦ w.1)
      Subtype.val_injective
  have hrange : Set.range v =
      b '' {w | componentWordAllowed s m w} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hspan : Submodule.span K (Set.range v) =
      (componentPowerProjectionGrading K s m).classOf 2 0 := by
    rw [hrange]
    symm
    exact (mme_dwz_table2_component_projection_certificate
      (K := K) s m).2.2.2
  change Basis (AvailableComponentWord.{u} s m) K
    ((componentPowerProjectionGrading K s m).classOf 2 0)
  exact (Basis.span hv).map (LinearEquiv.ofEq _ _ hspan)

end MME.DWZComponentRestriction


