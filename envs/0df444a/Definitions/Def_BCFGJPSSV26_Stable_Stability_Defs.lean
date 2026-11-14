-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs
-- name    : BCFGJPSSV26_Stable_Stability_Defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:59:29.310302+00:00
-- url     : https://prove2.me/theorems/a5b64b66-47f8-4e3f-856c-d24e99ae67ad
-- title:
--   BCFGJPSSV26.Stable.Stability.Defs — Synchronized and close clusters
-- statement:
--   This is module `BCFGJPSSV26.Stable.Stability.Defs` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Section 4.1]: an optimal center `c*` is **synced** if its cluster `C*` and the
--   local-search cluster of some `c ∈ S` differ in at most `ε min(|C*|, |C_c|)` clients
--   (`BCFGJPSSV26.Stable.Ctx.IsSynced`, [BCFGJPSSV26b, Definition 4.1]); `σ_sync(c*)` is such a
--   `c` (`BCFGJPSSV26.Stable.Ctx.σsync`). An unsynced center is **close** if
--   `d(c*, S) ≤ η avg_OPT + 2 ε avg_S` (`BCFGJPSSV26.Stable.Ctx.IsClose`), with substitute
--   `σ_cl(c*) = near(S, c*)`. `O_S0` collects both kinds, and `O₁ = O \ O_S0`
--   (`BCFGJPSSV26.Stable.Ctx.O1`).
--
--   Stability gives (`BCFGJPSSV26.Stable.Hyp.cluster_nonempty`,
--   `BCFGJPSSV26.Stable.Hyp.card_mul_sep_ge`): every optimal cluster is nonempty, and
--   `|C_o| d_o ≥ β opt` for the distance `d_o` from `o` to the other optimal centers
--   (`BCFGJPSSV26.Stable.Ctx.sep`).
--
--   **Contents.** The module is published as a whole: 20 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Stability/Defs.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Hyp

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Stability.Defs` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Synchronized and close clusters

[BCFGJPSSV26b, Section 4.1]: an optimal center `c*` is **synced** if its cluster `C*` and the
local-search cluster of some `c ∈ S` differ in at most `ε min(|C*|, |C_c|)` clients
(`BCFGJPSSV26.Stable.Ctx.IsSynced`, [BCFGJPSSV26b, Definition 4.1]); `σ_sync(c*)` is such a
`c` (`BCFGJPSSV26.Stable.Ctx.σsync`). An unsynced center is **close** if
`d(c*, S) ≤ η avg_OPT + 2 ε avg_S` (`BCFGJPSSV26.Stable.Ctx.IsClose`), with substitute
`σ_cl(c*) = near(S, c*)`. `O_S0` collects both kinds, and `O₁ = O \ O_S0`
(`BCFGJPSSV26.Stable.Ctx.O1`).

Stability gives (`BCFGJPSSV26.Stable.Hyp.cluster_nonempty`,
`BCFGJPSSV26.Stable.Hyp.card_mul_sep_ge`): every optimal cluster is nonempty, and
`|C_o| d_o ≥ β opt` for the distance `d_o` from `o` to the other optimal centers
(`BCFGJPSSV26.Stable.Ctx.sep`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

/-- `d_o`: the distance from `o` to the other optimal centers. -/
noncomputable def sep (o : Fin X.I.m) : ℝ := X.I.dSet (.inr o) (X.O.erase o)

/-- The number of clients in which `C*` and the local-search cluster of `c` differ. -/
noncomputable def symmCard (c c' : Fin X.I.m) : ℕ :=
  ((X.C c \ X.CS c') ∪ (X.CS c' \ X.C c)).card

/-- **Synced** [BCFGJPSSV26b, Definition 4.1]: some `c ∈ S` has a cluster differing from `C*`
in at most `ε min(|C*|, |C_c|)` clients. -/
def IsSynced (c : Fin X.I.m) : Prop :=
  ∃ c' ∈ X.S, (X.symmCard c c' : ℝ) ≤ X.ε * min ((X.C c).card : ℝ) (X.CS c').card

open Classical in
/-- The partner `σ_sync(c*)` of a synced center (`c*` itself otherwise). -/
noncomputable def σsync (c : Fin X.I.m) : Fin X.I.m :=
  if h : X.IsSynced c then Classical.choose h else c

/-- **Close** [BCFGJPSSV26b, Proposition 4.4]: unsynced, and
`d(c*, S) ≤ η avg_OPT + 2 ε avg_S`. -/
def IsClose (c : Fin X.I.m) : Prop :=
  ¬ X.IsSynced c ∧ X.dOS c ≤ eta * X.avgO c + 2 * X.ε * X.avgS c

open Classical in
/-- The synced centers. -/
noncomputable def Osync : Finset (Fin X.I.m) := X.O.filter X.IsSynced

open Classical in
/-- The close centers. -/
noncomputable def Ocl : Finset (Fin X.I.m) := X.O.filter X.IsClose

/-- `O_S0 = O_sync ∪ O_cl`. -/
noncomputable def OS0 : Finset (Fin X.I.m) := X.Osync ∪ X.Ocl

/-- `O₁ = O \ O_S0`. -/
noncomputable def O1 : Finset (Fin X.I.m) := X.O \ X.OS0

/-- The nearest local-search center `near(S, c)` of a facility (`c` itself if `S = ∅`). -/
noncomputable def σcl (c : Fin X.I.m) : Fin X.I.m :=
  if h : X.S.Nonempty then X.I.near X.S h (.inr c) else c

open Classical in
/-- The substitute `σ₀` on `O_S0`: the partner of a synced center, the nearest local-search
center of a close one. -/
noncomputable def σ₀ (c : Fin X.I.m) : Fin X.I.m := if X.IsSynced c then X.σsync c else X.σcl c

end Ctx

namespace Hyp

variable {X : Ctx}

theorem σsync_spec (_ : Hyp X) {c : Fin X.I.m} (hc : X.IsSynced c) :
    X.σsync c ∈ X.S ∧
      (X.symmCard c (X.σsync c) : ℝ) ≤ X.ε * min ((X.C c).card : ℝ) (X.CS (X.σsync c)).card := by
  unfold Ctx.σsync
  rw [dif_pos hc]
  exact Classical.choose_spec hc

variable (H : Hyp X)
include H

/-- `|C_o| d_o ≥ β opt`, proved before `cluster_nonempty`, which follows from it. -/
private theorem card_mul_sep_ge_aux {o : Fin X.I.m} (ho : o ∈ X.O) :
    X.β * X.opt ≤ (X.C o).card * X.sep o := by
  classical
  have hv := H.valid
  have hOne := H.O_nonempty
  have hcard : (X.O.erase o).card = X.I.k - 1 := by rw [card_erase_of_mem ho, H.isOpt.card]
  have hne : (X.O.erase o).Nonempty := by
    rw [← card_pos, hcard]
    have := H.two_le_k
    omega
  have hpt : ∀ j, X.I.dSet (.inl j) (X.O.erase o) ≤
      X.I.dSet (.inl j) X.O + if j ∈ X.C o then X.sep o else 0 := by
    intro j
    by_cases hj : j ∈ X.C o
    · rw [if_pos hj]
      have h1 := Instance.dSet_triangle hv (.inl j) (.inr o) (X.O.erase o)
      have h2 : X.I.dSet (.inl j) X.O = X.I.dd (.inl j) (.inr o) :=
        Instance.dSet_of_mem_cluster hj
      unfold Ctx.sep
      linarith
    · rw [if_neg hj, add_zero]
      have hnear : X.I.near X.O hOne (.inl j) ∈ X.O.erase o :=
        mem_erase.2 ⟨fun h ↦ hj ((Instance.mem_cluster hOne).2 h), Instance.near_mem _ _⟩
      calc _ ≤ X.I.dd (.inl j) (.inr (X.I.near X.O hOne (.inl j))) := Instance.dSet_le hnear _
        _ = _ := Instance.dd_near _ _
  have hcost : X.I.costF (X.O.erase o) ≤ X.I.costF X.O + (X.C o).card * X.sep o := by
    calc X.I.costF (X.O.erase o)
        ≤ ∑ j, (X.I.dSet (.inl j) X.O + if j ∈ X.C o then X.sep o else 0) :=
          sum_le_sum fun j _ ↦ hpt j
      _ = X.I.costF X.O + (X.C o).card * X.sep o := by
          rw [sum_add_distrib, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
          rfl
  have hstab := H.stable H.two_le_k
  have hopt := Instance.opt_le_costF hne hcard.le
  rw [H.isOpt.cost] at hcost
  unfold Ctx.opt
  linarith

/-- **Every optimal cluster is nonempty**: otherwise `opt (k - 1) ≤ cost(O \ {c*}) = opt`,
against stability. -/
theorem cluster_nonempty {c : Fin X.I.m} (hc : c ∈ X.O) : (X.C c).Nonempty := by
  by_contra h
  have h0 := H.card_mul_sep_ge_aux hc
  rw [not_nonempty_iff_eq_empty.1 h, card_empty, Nat.cast_zero, zero_mul] at h0
  have := mul_pos H.β_pos H.opt_pos
  unfold Ctx.opt at h0
  linarith

/-- **`|C_o| d_o ≥ β opt`**: moving the clients of `C_o` to the nearest other optimal
center costs at most `|C_o| d_o` more, and the result has `k - 1` centers. -/
theorem card_mul_sep_ge {o : Fin X.I.m} (ho : o ∈ X.O) :
    X.β * X.opt ≤ (X.C o).card * X.sep o :=
  H.card_mul_sep_ge_aux ho

theorem sep_pos {o : Fin X.I.m} (ho : o ∈ X.O) : 0 < X.sep o := by
  have h := H.card_mul_sep_ge ho
  have hβo : 0 < X.β * X.opt := mul_pos H.β_pos H.opt_pos
  have hc : (0 : ℝ) ≤ (X.C o).card := Nat.cast_nonneg _
  by_contra hneg
  have hs := not_lt.1 hneg
  nlinarith

/-- Distinct synced centers have distinct partners. -/
theorem σsync_injOn : Set.InjOn X.σsync X.Osync := by
  classical
  intro c₁ hc₁ c₂ hc₂ heq
  have hc₁' := mem_filter.1 (mem_coe.1 hc₁)
  have hc₂' := mem_filter.1 (mem_coe.1 hc₂)
  by_contra hne
  have h₁ := (H.σsync_spec hc₁'.2).2
  have h₂ := (H.σsync_spec hc₂'.2).2
  rw [heq] at h₁
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hdisj : Disjoint (X.C c₁) (X.C c₂) := Instance.disjoint_cluster _ hne
  have hs₁ : ((X.CS (X.σsync c₂) \ X.C c₁).card : ℝ) ≤ X.symmCard c₁ (X.σsync c₂) := by
    exact_mod_cast card_le_card subset_union_right
  have hs₂ : ((X.CS (X.σsync c₂) \ X.C c₂).card : ℝ) ≤ X.symmCard c₂ (X.σsync c₂) := by
    exact_mod_cast card_le_card subset_union_right
  have hcov : X.CS (X.σsync c₂) ⊆
      (X.CS (X.σsync c₂) \ X.C c₁) ∪ (X.CS (X.σsync c₂) \ X.C c₂) := by
    intro j hj
    by_cases h1 : j ∈ X.C c₁
    · exact mem_union_right _ (mem_sdiff.2 ⟨hj, disjoint_left.1 hdisj h1⟩)
    · exact mem_union_left _ (mem_sdiff.2 ⟨hj, h1⟩)
  have hC' : ((X.CS (X.σsync c₂)).card : ℝ) ≤
      (X.CS (X.σsync c₂) \ X.C c₁).card + (X.CS (X.σsync c₂) \ X.C c₂).card := by
    exact_mod_cast (card_le_card hcov).trans (card_union_le _ _)
  have hm₁ : X.ε * min ((X.C c₁).card : ℝ) (X.CS (X.σsync c₂)).card ≤
      X.ε * (X.CS (X.σsync c₂)).card := mul_le_mul_of_nonneg_left (min_le_right _ _) hε.le
  have hm₂ : X.ε * min ((X.C c₂).card : ℝ) (X.CS (X.σsync c₂)).card ≤
      X.ε * (X.CS (X.σsync c₂)).card := mul_le_mul_of_nonneg_left (min_le_right _ _) hε.le
  have hC'0 : ((X.CS (X.σsync c₂)).card : ℝ) ≤ 0 := by nlinarith
  have hempty : X.CS (X.σsync c₂) = ∅ := by
    rw [← card_eq_zero]
    exact_mod_cast le_antisymm hC'0 (Nat.cast_nonneg _)
  have hsub : ((X.C c₁ \ X.CS (X.σsync c₂)).card : ℝ) ≤ X.symmCard c₁ (X.σsync c₂) := by
    exact_mod_cast card_le_card subset_union_left
  rw [hempty, sdiff_empty] at hsub
  rw [hempty, card_empty, Nat.cast_zero, min_eq_right (Nat.cast_nonneg _), mul_zero] at h₁
  have hpos : (0 : ℝ) < (X.C c₁).card := by exact_mod_cast (H.cluster_nonempty hc₁'.1).card_pos
  linarith

theorem σcl_mem (c : Fin X.I.m) : X.σcl c ∈ X.S := by
  unfold Ctx.σcl
  rw [dif_pos H.S_nonempty]
  exact Instance.near_mem _ _

theorem dF_σcl (c : Fin X.I.m) : X.dF c (X.σcl c) = X.dOS c := by
  unfold Ctx.σcl
  rw [dif_pos H.S_nonempty]
  exact Instance.dd_near _ _

theorem σ₀_mem (c : Fin X.I.m) : X.σ₀ c ∈ X.S := by
  unfold Ctx.σ₀
  split_ifs with h
  · exact (H.σsync_spec h).1
  · exact H.σcl_mem c

end Hyp

end BCFGJPSSV26.Stable


