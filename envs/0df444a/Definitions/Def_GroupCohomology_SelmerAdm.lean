-- Prove2me | Definitions.Def_GroupCohomology_SelmerAdm
-- name    : GroupCohomology_SelmerAdm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/97cc6895-1518-5eb9-8391-ec7975d5c386
-- title:
--   Admissible Selmer submodules and the ≤ Greenberg–Wiles datum
-- statement:
--   Throughout, $k$ is a field, $\Gamma$ a group, $(\Gamma_v)_{v \in \iota}$ a family of groups with homomorphisms $\mathrm{loc}_v \colon \Gamma_v \to \Gamma$, and $M$ a $k$-linear representation of $\Gamma$; $H^1$ is Mathlib's first group cohomology and $\mathrm{locRes}_v \colon H^1(M) \to H^1(\mathrm{res}_{\mathrm{loc}_v} M)$ the restriction map along $\mathrm{loc}_v$. Given local conditions $L_v \le H^1(\mathrm{res}_{\mathrm{loc}_v} M)$, the Selmer submodule $\mathrm{selmer}$ is $\bigsqcap_v \mathrm{locRes}_v^{-1}(L_v)$. The module defines `selmerAdm`, the intersection $\mathrm{selmer}\,\sqcap\,\mathrm{adm}$ of that Selmer submodule with a further submodule $\mathrm{adm} \le H^1(M)$ of "admissible" classes: membership means that all local restrictions lie in the $L_v$ and that the class lies in $\mathrm{adm}$. Accompanying lemmas record that it lies below both factors, that it equals $\mathrm{selmer}$ when $\mathrm{adm} = \top$ and is trivial when $\mathrm{adm} = \bot$, and that it is finite-dimensional whenever $\mathrm{adm}$ is.
--
--   For $\iota$ finite, a second representation $M'$ and pairings $H^1(\mathrm{res}_{\mathrm{loc}_v} M) \times H^1(\mathrm{res}_{\mathrm{loc}_v} M') \to k$, the predicate `greenbergWilesLeAdm` asserts the one-sided inequality
--   $$\dim \mathrm{selmerAdm}(L,\mathrm{adm}) + \dim (M')^{\Gamma} + \sum_v \dim (\mathrm{res}_{\mathrm{loc}_v} M)^{\Gamma_v} \le \dim \mathrm{selmerAdm}(L^{\perp},\mathrm{adm}') + \dim M^{\Gamma} + \sum_v \dim L_v,$$
--   where $L^{\perp}_v$ is the annihilator of $L_v$ under the $v$-th pairing. The structure `IsGreenbergWilesLeDatumAdm` packages this inequality as a field together with finite-dimensionality of the two admissible Selmer submodules and of each $L_v$; it is thus a hypothesis-bundle carrying the Greenberg–Wiles inequality rather than a proof of it. Two results relate this to the unrestricted version: `greenbergWilesLeAdm_top_iff` identifies the case $\mathrm{adm} = \mathrm{adm}' = \top$ with `greenbergWilesLe`, and `IsGreenbergWilesLeDatum.toAdm` converts an unrestricted datum into the admissible one at $\top$, $\top$.
--
--   **Relation to Mathlib.** Built on Mathlib's group cohomology ($H^1$, restriction along a group homomorphism) and `Rep`; Mathlib has no Selmer submodules attached to a family of local conditions and no Greenberg–Wiles dimension formula, so `selmer`, `selmerAdm` and the Greenberg–Wiles predicates are the project's own.
--
--   **Where it is used.** The admissible variant exists so that the Greenberg–Wiles input can be stated with both Selmer terms cut down inside submodules of $H^1$ for which finite-dimensionality is available (for instance classes with prescribed local behaviour over a Galois group of a number field), and so that only the inequality, which is what the Taylor–Wiles dimension count consumes, has to be supplied.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_SelmerAdm.lean

import Mathlib
import Definitions.Def_GroupCohomology_SelmerLe

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable def selmerAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) : Submodule k (H1 M) :=
  selmer loc M L ⊓ adm

lemma mem_selmerAdm_iff (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) (x : H1 M) :
    x ∈ selmerAdm loc M L adm ↔ (∀ v, (locRes loc M v).hom x ∈ L v) ∧ x ∈ adm := by
  rw [selmerAdm, Submodule.mem_inf, mem_selmer_iff]

lemma selmerAdm_le_selmer (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) : selmerAdm loc M L adm ≤ selmer loc M L :=
  inf_le_left

lemma selmerAdm_le_adm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) : selmerAdm loc M L adm ≤ adm :=
  inf_le_right

@[simp]
lemma selmerAdm_top (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmerAdm loc M L ⊤ = selmer loc M L :=
  inf_top_eq _

@[simp]
lemma selmerAdm_bot (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmerAdm loc M L ⊥ = ⊥ :=
  inf_bot_eq _

instance finiteDimensional_selmerAdm_of_adm
    (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (adm : Submodule k (H1 M))
    [FiniteDimensional k adm] : FiniteDimensional k (selmerAdm loc M L adm) :=
  Submodule.finiteDimensional_inf_right _ _

variable [Fintype ι] (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def greenbergWilesLeAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) (adm' : Submodule k (H1 M')) : Prop :=
  finrank k (selmerAdm loc M L adm)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    ≤ finrank k (selmerAdm loc M' (dualConditions loc M M' pairing L) adm')
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

theorem greenbergWilesLeAdm_top_iff (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    greenbergWilesLeAdm loc M M' pairing L ⊤ ⊤ ↔ greenbergWilesLe loc M M' pairing L := by
  unfold greenbergWilesLeAdm greenbergWilesLe
  rw [selmerAdm_top, selmerAdm_top]

structure IsGreenbergWilesLeDatumAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) (adm' : Submodule k (H1 M')) : Prop where

  finite_selmer : FiniteDimensional k (selmerAdm loc M L adm)

  finite_dualSelmer :
    FiniteDimensional k (selmerAdm loc M' (dualConditions loc M M' pairing L) adm')

  finite_local : ∀ v, FiniteDimensional k (L v)

  le : greenbergWilesLeAdm loc M M' pairing L adm adm'

theorem IsGreenbergWilesLeDatum.toAdm {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : IsGreenbergWilesLeDatum loc M M' pairing L) :
    IsGreenbergWilesLeDatumAdm loc M M' pairing L ⊤ ⊤ where
  finite_selmer := by rw [selmerAdm_top]; exact h.finite_selmer
  finite_dualSelmer := by rw [selmerAdm_top]; exact h.finite_dualSelmer
  finite_local := h.finite_local
  le := (greenbergWilesLeAdm_top_iff loc M M' pairing L).mpr h.le

end groupCohomology


