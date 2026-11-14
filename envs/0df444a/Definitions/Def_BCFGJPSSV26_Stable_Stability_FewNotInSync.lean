-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
-- name    : BCFGJPSSV26_Stable_Stability_FewNotInSync
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:00:40.468337+00:00
-- url     : https://prove2.me/theorems/b300af79-0e6a-4138-b358-81ff02fe8331
-- title:
--   BCFGJPSSV26.Stable.Stability.FewNotInSync — Few clusters are not in sync
-- statement:
--   This is module `BCFGJPSSV26.Stable.Stability.FewNotInSync` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Lemma 4.2] with the bound `632/(εβ)`: fewer than `632/(εβ)` optimal centers are
--   unsynced (`BCFGJPSSV26.Stable.Hyp.card_unsynced_lt`), so at most `s = 632 N L`
--   (`BCFGJPSSV26.Stable.Hyp.card_O1_le`), the bound on the special clusters that the algorithm uses.
--
--   The proof is along the lines of [CGLSS25, Lemma 4.3], for `ε`-synced clusters and every
--   `ε < 1/200`, with `a₀ = 1/30`, `b₀ = 1/10` and `τ = ε/90`. It uses only `cost(S) ≤ 4 opt`
--   (`BCFGJPSSV26.Stable.costF_le_four_opt`), not local optimality: at most `90/(εβ)` expensive
--   clusters; at most `240/β` cheap clusters far from `S`; as many again as these two kinds together
--   with two local-search centers near them, by pigeonhole on `|S| = |O| = k`; at most `360/(εβ)` of
--   the others whose local-search cluster has more than `(ε/3)|C_o|` clients far from `o`; all others
--   are synced. In total at most `540/(εβ) + 480/β < 632/(εβ)`.
--
--   Consequences: `|O₁| ≤ s` and `|S \ σ_sync(O_sync)| ≤ s`
--   (`BCFGJPSSV26.Stable.Hyp.card_S_sdiff_sync_le`).
--
--   **Contents.** The module is published as a whole: 25 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Hyp.card_O1_le`, `BCFGJPSSV26.Stable.Hyp.card_S_sdiff_sync_le`, `BCFGJPSSV26.Stable.Hyp.card_unsynced_lt` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Stability/FewNotInSync.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Stability.FewNotInSync` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Few clusters are not in sync

[BCFGJPSSV26b, Lemma 4.2] with the bound `632/(εβ)`: fewer than `632/(εβ)` optimal centers are
unsynced (`BCFGJPSSV26.Stable.Hyp.card_unsynced_lt`), so at most `s = 632 N L`
(`BCFGJPSSV26.Stable.Hyp.card_O1_le`), the bound on the special clusters that the algorithm uses.

The proof is along the lines of [CGLSS25, Lemma 4.3], for `ε`-synced clusters and every
`ε < 1/200`, with `a₀ = 1/30`, `b₀ = 1/10` and `τ = ε/90`. It uses only `cost(S) ≤ 4 opt`
(`BCFGJPSSV26.Stable.costF_le_four_opt`), not local optimality: at most `90/(εβ)` expensive
clusters; at most `240/β` cheap clusters far from `S`; as many again as these two kinds together
with two local-search centers near them, by pigeonhole on `|S| = |O| = k`; at most `360/(εβ)` of
the others whose local-search cluster has more than `(ε/3)|C_o|` clients far from `o`; all others
are synced. In total at most `540/(εβ) + 480/β < 632/(εβ)`.

Consequences: `|O₁| ≤ s` and `|S \ σ_sync(O_sync)| ≤ s`
(`BCFGJPSSV26.Stable.Hyp.card_S_sdiff_sync_le`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-! ### The classes of the proof

For `o ∈ O`, with `d_o = sep o`: `o` is *cheap* if `cost_OPT(C_o) ≤ (ε/90) β opt`, *near `S`* if
`d(o, S) ≤ d_o/15`, and has a *second* center if some `c ∈ S` other than `σ_cl(o) = near(S, o)` is
within `d_o/3` of `o`. The classes are `O_exp` (not cheap), `Õ₁` (cheap, not near `S`), `O₂'`
(cheap, near `S`), `Õ₂ ⊆ O₂'` (with a second center), `O₃ = O₂' \ Õ₂` and `Õ₃ ⊆ O₃` (more than
`(ε/3)|C_o|` clients of the local-search cluster of `σ_cl(o)` farther than `d_o/10` from `o`). -/

namespace FewNotInSync

variable (X : Ctx)

/-- `o` is cheap: `cost_OPT(C_o) ≤ (ε/90) β opt`. -/
private def Cheap (o : Fin X.I.m) : Prop := X.costO o ≤ X.ε / 90 * X.β * X.opt

/-- `o` is near `S`: `d(o, S) ≤ d_o/15`. -/
private def NearS (o : Fin X.I.m) : Prop := X.dOS o ≤ X.sep o / 15

/-- A second center of `S` within `d_o/3` of `o`. -/
private def Second (o : Fin X.I.m) : Prop := ∃ c ∈ X.S, c ≠ X.σcl o ∧ X.dF o c ≤ X.sep o / 3

open Classical in
/-- The clients of the local-search cluster of `σ_cl(o)` farther than `d_o/10` from `o`. -/
private noncomputable def far (o : Fin X.I.m) : Finset (Fin X.I.n) :=
  (X.CS (X.σcl o)).filter fun j ↦ X.sep o / 10 < X.dist j o

/-- Many far clients: more than `(ε/3)|C_o|`. -/
private def Bad (o : Fin X.I.m) : Prop := X.ε / 3 * (X.C o).card < (far X o).card

open Classical in
/-- `O_exp`: the expensive centers. -/
private noncomputable def Oexp : Finset (Fin X.I.m) := X.O.filter fun o ↦ ¬ Cheap X o

open Classical in
/-- The cheap centers. -/
private noncomputable def Och : Finset (Fin X.I.m) := X.O.filter (Cheap X)

open Classical in
/-- `Õ₁`: cheap, not near `S`. -/
private noncomputable def O1t : Finset (Fin X.I.m) := (Och X).filter fun o ↦ ¬ NearS X o

open Classical in
/-- `O₂'`: cheap, near `S`. -/
private noncomputable def O2p : Finset (Fin X.I.m) := (Och X).filter (NearS X)

open Classical in
/-- `Õ₂`: in `O₂'`, with a second center. -/
private noncomputable def O2t : Finset (Fin X.I.m) := (O2p X).filter (Second X)

open Classical in
/-- `O₃`: in `O₂'`, without a second center. -/
private noncomputable def O3 : Finset (Fin X.I.m) := (O2p X).filter fun o ↦ ¬ Second X o

open Classical in
/-- `Õ₃`: in `O₃`, with many far clients. -/
private noncomputable def O3t : Finset (Fin X.I.m) := (O3 X).filter (Bad X)

end FewNotInSync

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

open FewNotInSync

/-- The local-search costs of disjoint sets of clients add up to at most `cost(S)`. -/
private theorem sum_costOn_le {ι : Type*} (T : Finset ι) (F : ι → Finset (Fin X.I.n))
    (hF : (T : Set ι).PairwiseDisjoint F) :
    ∑ o ∈ T, X.costS (F o) ≤ X.I.costF X.S := by
  classical
  calc ∑ o ∈ T, X.costS (F o) = X.I.costOn X.S (T.biUnion F) := by
        change ∑ o ∈ T, ∑ j ∈ F o, X.I.dSet (.inl j) X.S =
          ∑ j ∈ T.biUnion F, X.I.dSet (.inl j) X.S
        rw [sum_biUnion hF]
    _ ≤ X.I.costF X.S := Instance.costOn_le_costF H.valid _ _

/-- **The balls `B(o, d_o/3)` of distinct optimal centers are disjoint.** -/
private theorem ball_unique {o o' c : Fin X.I.m} (ho : o ∈ X.O) (ho' : o' ∈ X.O)
    (h : X.dF o c ≤ X.sep o / 3) (h' : X.dF o' c ≤ X.sep o' / 3) : o = o' := by
  by_contra hne
  have hv := H.valid
  have h1 : X.sep o ≤ X.dF o o' := Instance.dSet_le (mem_erase.2 ⟨Ne.symm hne, ho'⟩) _
  have h2 : X.sep o' ≤ X.dF o' o := Instance.dSet_le (mem_erase.2 ⟨hne, ho⟩) _
  have h3 : X.dF o o' ≤ X.dF o c + X.dF o' c := by
    have := Instance.dd_triangle hv (.inr o) (.inr c) (.inr o')
    rw [Instance.dd_comm hv (.inr c) (.inr o')] at this
    exact this
  have h4 : X.dF o' o = X.dF o o' := Instance.dd_comm hv _ _
  have := H.sep_pos ho
  linarith

/-- **Step 2.** For a cheap `o`, at most `(ε/3)|C_o|` clients of `C_o` are farther than `d_o/30`
from `o`. -/
private theorem card_farO_le {o : Fin X.I.m} (ho : o ∈ X.O) (hch : Cheap X o) :
    (((X.C o).filter fun j ↦ X.sep o / 30 < X.dist j o).card : ℝ) ≤ X.ε / 3 * (X.C o).card := by
  classical
  have hv := H.valid
  have hsep := H.sep_pos ho
  have hβ := H.card_mul_sep_ge ho
  have hε := H.eps_pos
  have h1 : (((X.C o).filter fun j ↦ X.sep o / 30 < X.dist j o).card : ℝ) * (X.sep o / 30) ≤
      X.costO o := by
    calc _ = ∑ _j ∈ (X.C o).filter (fun j ↦ X.sep o / 30 < X.dist j o), X.sep o / 30 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ (X.C o).filter (fun j ↦ X.sep o / 30 < X.dist j o), X.dist j o :=
          sum_le_sum fun j hj ↦ (mem_filter.1 hj).2.le
      _ ≤ ∑ j ∈ X.C o, X.dist j o :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ ↦
            Instance.dd_nonneg hv _ _
  have h2 : X.costO o ≤ X.ε / 90 * ((X.C o).card * X.sep o) := by
    calc X.costO o ≤ X.ε / 90 * X.β * X.opt := hch
      _ = X.ε / 90 * (X.β * X.opt) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hβ (by positivity)
  have h3 : (((X.C o).filter fun j ↦ X.sep o / 30 < X.dist j o).card : ℝ) * X.sep o ≤
      (X.ε / 3 * (X.C o).card) * X.sep o := by linarith
  exact le_of_mul_le_mul_right h3 hsep

/-- **Step 1.** `|O_exp| (ε/90) β opt ≤ opt`. -/
private theorem card_Oexp_le : ((Oexp X).card : ℝ) * (X.ε / 90 * X.β * X.opt) ≤ X.opt := by
  classical
  calc ((Oexp X).card : ℝ) * (X.ε / 90 * X.β * X.opt)
      = (Oexp X).card • (X.ε / 90 * X.β * X.opt) := (nsmul_eq_mul _ _).symm
    _ ≤ ∑ o ∈ Oexp X, X.costO o := card_nsmul_le_sum _ _ _ fun o ho ↦ by
        have h := (mem_filter.1 ho).2
        unfold Cheap at h
        push Not at h
        exact h.le
    _ ≤ ∑ o ∈ X.O, X.costO o :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun o _ _ ↦
          sum_nonneg fun j _ ↦ Instance.dd_nonneg H.valid _ _
    _ = X.opt := H.opt_eq_sum.symm

/-- **Step 3.** A cheap center far from `S` has local-search cost at least
`(1 - ε/3) β opt / 30`. -/
private theorem costS_ge_of_O1t {o : Fin X.I.m} (ho : o ∈ O1t X) :
    (1 - X.ε / 3) * X.β * X.opt / 30 ≤ X.costS (X.C o) := by
  classical
  simp only [O1t, Och, mem_filter] at ho
  obtain ⟨⟨hoO, hch⟩, hfar⟩ := ho
  unfold NearS at hfar
  push Not at hfar
  have hv := H.valid
  have hsep := H.sep_pos hoO
  have hβ := H.card_mul_sep_ge hoO
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hF := H.card_farO_le hoO hch
  have hsplit : (((X.C o).filter fun j ↦ X.sep o / 30 < X.dist j o).card : ℝ) +
      ((X.C o).filter fun j ↦ ¬ X.sep o / 30 < X.dist j o).card = (X.C o).card := by
    exact_mod_cast card_filter_add_card_filter_not _
  have hNr : ∀ j ∈ (X.C o).filter (fun j ↦ ¬ X.sep o / 30 < X.dist j o),
      X.sep o / 30 ≤ X.I.dSet (.inl j) X.S := by
    intro j hj
    have hj' := not_lt.1 (mem_filter.1 hj).2
    have h1 := Instance.dSet_triangle hv (.inr o) (.inl j) X.S
    rw [Instance.dd_comm hv] at h1
    unfold Ctx.dOS at hfar
    unfold Ctx.dist at hj'
    linarith
  have hcost : (((X.C o).filter fun j ↦ ¬ X.sep o / 30 < X.dist j o).card : ℝ) *
      (X.sep o / 30) ≤ X.costS (X.C o) := by
    calc _ = ∑ _j ∈ (X.C o).filter (fun j ↦ ¬ X.sep o / 30 < X.dist j o), X.sep o / 30 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ (X.C o).filter (fun j ↦ ¬ X.sep o / 30 < X.dist j o),
            X.I.dSet (.inl j) X.S := sum_le_sum hNr
      _ ≤ ∑ j ∈ X.C o, X.I.dSet (.inl j) X.S :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ ↦
            Instance.dSet_nonneg hv _ _
  have hN : (1 - X.ε / 3) * (X.C o).card ≤
      ((X.C o).filter fun j ↦ ¬ X.sep o / 30 < X.dist j o).card := by linarith
  have h1 : (1 - X.ε / 3) * ((X.C o).card * X.sep o) ≤
      ((X.C o).filter fun j ↦ ¬ X.sep o / 30 < X.dist j o).card * X.sep o := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hN hsep.le
  have h2 : (1 - X.ε / 3) * (X.β * X.opt) ≤ (1 - X.ε / 3) * ((X.C o).card * X.sep o) :=
    mul_le_mul_of_nonneg_left hβ (by linarith)
  linarith

/-- **Step 3.** `|Õ₁| (1 - ε/3) β opt / 30 ≤ cost(S)`. -/
private theorem card_O1t_le :
    ((O1t X).card : ℝ) * ((1 - X.ε / 3) * X.β * X.opt / 30) ≤ X.I.costF X.S := by
  classical
  calc ((O1t X).card : ℝ) * ((1 - X.ε / 3) * X.β * X.opt / 30)
      = (O1t X).card • ((1 - X.ε / 3) * X.β * X.opt / 30) := (nsmul_eq_mul _ _).symm
    _ ≤ ∑ o ∈ O1t X, X.costS (X.C o) :=
        card_nsmul_le_sum _ _ _ fun o ho ↦ H.costS_ge_of_O1t ho
    _ ≤ X.I.costF X.S := H.sum_costOn_le _ _ fun c _ c' _ h ↦ Instance.disjoint_cluster _ h

/-- A center of `O₂'` is within `d_o/3` of its nearest local-search center. -/
private theorem mem_O2p {o : Fin X.I.m} (ho : o ∈ O2p X) :
    o ∈ X.O ∧ X.dF o (X.σcl o) ≤ X.sep o / 3 := by
  classical
  simp only [O2p, Och, mem_filter] at ho
  obtain ⟨⟨hoO, -⟩, hn⟩ := ho
  refine ⟨hoO, ?_⟩
  rw [H.dF_σcl]
  have := H.sep_pos hoO
  unfold NearS at hn
  linarith

/-- **Step 4 (pigeonhole).** `|O₂'| + |Õ₂| ≤ k`: the nearest local-search centers of `O₂'` and the
second centers of `Õ₂` are distinct elements of `S`. -/
private theorem card_O2p_add_O2t_le : (O2p X).card + (O2t X).card ≤ X.I.k := by
  classical
  have hsec : ∀ o ∈ O2t X, ∃ c ∈ X.S, c ≠ X.σcl o ∧ X.dF o c ≤ X.sep o / 3 :=
    fun o ho ↦ (mem_filter.1 ho).2
  choose! c2 hc2S hc2ne hc2d using hsec
  have hsub' : O2t X ⊆ O2p X := filter_subset _ _
  have hinj1 : Set.InjOn X.σcl (O2p X) := by
    intro o ho o' ho' h
    have h1 := H.mem_O2p ho
    have h2 := H.mem_O2p ho'
    rw [h] at h1
    exact H.ball_unique h1.1 h2.1 h1.2 h2.2
  have hinj2 : Set.InjOn c2 (O2t X) := by
    intro o ho o' ho' h
    have h1 := hc2d o ho
    have h2 := hc2d o' ho'
    rw [h] at h1
    exact H.ball_unique (H.mem_O2p (hsub' ho)).1 (H.mem_O2p (hsub' ho')).1 h1 h2
  have hdisj : Disjoint ((O2p X).image X.σcl) ((O2t X).image c2) := by
    rw [disjoint_left]
    intro c hc hc'
    obtain ⟨o, ho, rfl⟩ := mem_image.1 hc
    obtain ⟨o', ho', h⟩ := mem_image.1 hc'
    have h1 := H.mem_O2p ho
    have h2 := hc2d o' ho'
    rw [h] at h2
    have heq := H.ball_unique h1.1 (H.mem_O2p (hsub' ho')).1 h1.2 h2
    subst heq
    exact hc2ne o ho' h
  have hsub : (O2p X).image X.σcl ∪ (O2t X).image c2 ⊆ X.S := by
    intro c hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨o, _, rfl⟩ := mem_image.1 hc
      exact H.σcl_mem o
    · obtain ⟨o, ho, rfl⟩ := mem_image.1 hc
      exact hc2S o ho
  have h := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_image_of_injOn hinj1, card_image_of_injOn hinj2,
    H.alo.1] at h
  exact h

/-- **Step 6.** A center of `Õ₃` has a local-search cluster of cost at least `ε β opt / 90`. -/
private theorem costS_ge_of_O3t {o : Fin X.I.m} (ho : o ∈ O3t X) :
    X.ε * X.β * X.opt / 90 ≤ X.costS (X.CS (X.σcl o)) := by
  classical
  simp only [O3t, O3, O2p, Och, mem_filter] at ho
  obtain ⟨⟨⟨⟨hoO, -⟩, hn⟩, -⟩, hbad⟩ := ho
  have hv := H.valid
  have hsep := H.sep_pos hoO
  have hβ := H.card_mul_sep_ge hoO
  have hε := H.eps_pos
  unfold NearS at hn
  unfold Bad at hbad
  have hfar : ∀ j ∈ far X o, X.sep o / 30 ≤ X.I.dSet (.inl j) X.S := by
    intro j hj
    obtain ⟨hjC, hjd⟩ := mem_filter.1 hj
    rw [Instance.dSet_of_mem_cluster hjC]
    have h1 := Instance.dd_triangle hv (.inl j) (.inr (X.σcl o)) (.inr o)
    have h2 := H.dF_σcl o
    have h3 : X.I.dd (.inr (X.σcl o)) (.inr o) = X.dF o (X.σcl o) := Instance.dd_comm hv _ _
    unfold Ctx.dist at hjd
    linarith
  have hcost : ((far X o).card : ℝ) * (X.sep o / 30) ≤ X.costS (X.CS (X.σcl o)) := by
    calc _ = ∑ _j ∈ far X o, X.sep o / 30 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ far X o, X.I.dSet (.inl j) X.S := sum_le_sum hfar
      _ ≤ ∑ j ∈ X.CS (X.σcl o), X.I.dSet (.inl j) X.S :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ ↦
            Instance.dSet_nonneg hv _ _
  have h1 : X.ε / 3 * ((X.C o).card * X.sep o) ≤ (far X o).card * X.sep o := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hbad.le hsep.le
  have h2 : X.ε / 3 * (X.β * X.opt) ≤ X.ε / 3 * ((X.C o).card * X.sep o) :=
    mul_le_mul_of_nonneg_left hβ (by positivity)
  linarith

/-- **Step 6.** `|Õ₃| ε β opt / 90 ≤ cost(S)`: the local-search clusters of the `σ_cl(o)`,
`o ∈ Õ₃`, are distinct. -/
private theorem card_O3t_le : ((O3t X).card : ℝ) * (X.ε * X.β * X.opt / 90) ≤ X.I.costF X.S := by
  classical
  have hsub : O3t X ⊆ O2p X := fun o ho ↦ by
    simp only [O3t, O3, mem_filter] at ho
    exact ho.1.1
  have hinj : Set.InjOn X.σcl (O3t X) := by
    intro o ho o' ho' h
    have h1 := H.mem_O2p (hsub ho)
    have h2 := H.mem_O2p (hsub ho')
    rw [h] at h1
    exact H.ball_unique h1.1 h2.1 h1.2 h2.2
  calc ((O3t X).card : ℝ) * (X.ε * X.β * X.opt / 90)
      = (O3t X).card • (X.ε * X.β * X.opt / 90) := (nsmul_eq_mul _ _).symm
    _ ≤ ∑ o ∈ O3t X, X.costS (X.CS (X.σcl o)) :=
        card_nsmul_le_sum _ _ _ fun o ho ↦ H.costS_ge_of_O3t ho
    _ = ∑ c ∈ (O3t X).image X.σcl, X.costS (X.CS c) :=
        (sum_image (f := fun c ↦ X.costS (X.CS c)) hinj).symm
    _ ≤ X.I.costF X.S := H.sum_costOn_le _ _ fun c _ c' _ h ↦ Instance.disjoint_cluster _ h

/-- **Steps 5 and 7.** A center of `O₃ \ Õ₃` is synced with `σ_cl(o)`: the clients within
`d_o/10` of `o` are in both `C_o` and the local-search cluster of `σ_cl(o)` (strictly nearest,
whatever the tie-break), so the two clusters differ in at most `(2ε/3)|C_o|` clients. -/
private theorem isSynced_of_good {o : Fin X.I.m} (ho : o ∈ O3 X) (hgood : ¬ Bad X o) :
    X.IsSynced o := by
  classical
  simp only [O3, O2p, Och, mem_filter] at ho
  obtain ⟨⟨⟨hoO, hch⟩, hn⟩, hsec⟩ := ho
  unfold NearS at hn
  unfold Second at hsec
  push Not at hsec
  unfold Bad at hgood
  push Not at hgood
  have hv := H.valid
  have hsep := H.sep_pos hoO
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hOne := H.O_nonempty
  have hSne := H.S_nonempty
  have hdσ : X.dF o (X.σcl o) ≤ X.sep o / 15 := by rw [H.dF_σcl]; exact hn
  have hkey : ∀ j, X.dist j o ≤ X.sep o / 10 → j ∈ X.C o ∧ j ∈ X.CS (X.σcl o) := by
    intro j hj
    constructor
    · refine (Instance.mem_cluster hOne).2 (Instance.near_eq_of_lt hOne hoO fun o' ho' hne ↦ ?_)
      have h1 : X.sep o ≤ X.dF o o' := Instance.dSet_le (mem_erase.2 ⟨hne, ho'⟩) _
      have h2 := Instance.dd_triangle hv (.inr o) (.inl j) (.inr o')
      rw [Instance.dd_comm hv (.inr o) (.inl j)] at h2
      unfold Ctx.dist at hj
      unfold Ctx.dF at h1
      linarith
    · refine (Instance.mem_cluster hSne).2
        (Instance.near_eq_of_lt hSne (H.σcl_mem o) fun c' hc' hne ↦ ?_)
      have h1 := hsec c' hc' hne
      have h2 := Instance.dd_triangle hv (.inr o) (.inl j) (.inr c')
      rw [Instance.dd_comm hv (.inr o) (.inl j)] at h2
      have h3 := Instance.dd_triangle hv (.inl j) (.inr o) (.inr (X.σcl o))
      unfold Ctx.dist at hj
      unfold Ctx.dF at h1 hdσ
      linarith
  have hsub1 : X.C o \ X.CS (X.σcl o) ⊆ (X.C o).filter fun j ↦ X.sep o / 30 < X.dist j o := by
    intro j hj
    obtain ⟨hjC, hjC'⟩ := mem_sdiff.1 hj
    refine mem_filter.2 ⟨hjC, ?_⟩
    by_contra hle
    push Not at hle
    exact hjC' (hkey j (by linarith)).2
  have hsub2 : X.CS (X.σcl o) \ X.C o ⊆ far X o := by
    intro j hj
    obtain ⟨hjC', hjC⟩ := mem_sdiff.1 hj
    refine mem_filter.2 ⟨hjC', ?_⟩
    by_contra hle
    push Not at hle
    exact hjC (hkey j hle).1
  have h1 : ((X.C o \ X.CS (X.σcl o)).card : ℝ) ≤ X.ε / 3 * (X.C o).card :=
    le_trans (by exact_mod_cast card_le_card hsub1) (H.card_farO_le hoO hch)
  have h2 : ((X.CS (X.σcl o) \ X.C o).card : ℝ) ≤ X.ε / 3 * (X.C o).card :=
    le_trans (by exact_mod_cast card_le_card hsub2) hgood
  have hsym : (X.symmCard o (X.σcl o) : ℝ) ≤ 2 * X.ε / 3 * (X.C o).card := by
    have h3 : X.symmCard o (X.σcl o) ≤
        (X.C o \ X.CS (X.σcl o)).card + (X.CS (X.σcl o) \ X.C o).card := card_union_le _ _
    have h4 : (X.symmCard o (X.σcl o) : ℝ) ≤
        (X.C o \ X.CS (X.σcl o)).card + (X.CS (X.σcl o) \ X.C o).card := by exact_mod_cast h3
    linarith
  have hC' : (1 - X.ε / 3) * (X.C o).card ≤ (X.CS (X.σcl o)).card := by
    have h3 : ((X.C o ∩ X.CS (X.σcl o)).card : ℝ) + (X.C o \ X.CS (X.σcl o)).card =
        (X.C o).card := by exact_mod_cast card_inter_add_card_sdiff _ _
    have h4 : ((X.C o ∩ X.CS (X.σcl o)).card : ℝ) ≤ (X.CS (X.σcl o)).card := by
      exact_mod_cast card_le_card inter_subset_right
    linarith
  have hC0 : (0 : ℝ) ≤ (X.C o).card := Nat.cast_nonneg _
  refine ⟨X.σcl o, H.σcl_mem o, ?_⟩
  rw [mul_min_of_nonneg _ _ hε.le]
  refine le_min ?_ ?_
  · have : 0 ≤ X.ε * (X.C o).card := mul_nonneg hε.le hC0
    linarith
  · have h3 : X.ε * ((1 - X.ε / 3) * (X.C o).card) ≤ X.ε * (X.CS (X.σcl o)).card :=
      mul_le_mul_of_nonneg_left hC' hε.le
    have h4 : 0 ≤ X.ε * (X.C o).card * (1 - X.ε) :=
      mul_nonneg (mul_nonneg hε.le hC0) (by linarith)
    linarith

open Classical in
/-- Every unsynced center is in `O_exp ∪ Õ₁ ∪ Õ₂ ∪ Õ₃`. -/
private theorem unsynced_subset :
    (X.O.filter fun c ↦ ¬ X.IsSynced c) ⊆ Oexp X ∪ O1t X ∪ O2t X ∪ O3t X := by
  classical
  intro o ho
  obtain ⟨hoO, hns⟩ := mem_filter.1 ho
  by_cases hch : Cheap X o
  · by_cases hn : NearS X o
    · by_cases hs : Second X o
      · refine mem_union_left _ (mem_union_right _ ?_)
        simp only [O2t, O2p, Och, mem_filter]
        exact ⟨⟨⟨hoO, hch⟩, hn⟩, hs⟩
      · have hO3 : o ∈ O3 X := by
          simp only [O3, O2p, Och, mem_filter]
          exact ⟨⟨⟨hoO, hch⟩, hn⟩, hs⟩
        by_cases hb : Bad X o
        · refine mem_union_right _ ?_
          simp only [O3t, mem_filter]
          exact ⟨hO3, hb⟩
        · exact absurd (H.isSynced_of_good hO3 hb) hns
    · refine mem_union_left _ (mem_union_left _ (mem_union_right _ ?_))
      simp only [O1t, Och, mem_filter]
      exact ⟨⟨hoO, hch⟩, hn⟩
  · refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
    simp only [Oexp, mem_filter]
    exact ⟨hoO, hch⟩

open Classical in
/-- `|unsynced| ≤ 2 |O_exp| + 2 |Õ₁| + |Õ₃|`. -/
private theorem card_unsynced_le_nat :
    (X.O.filter fun c ↦ ¬ X.IsSynced c).card ≤
      2 * (Oexp X).card + 2 * (O1t X).card + (O3t X).card := by
  classical
  have h0 := card_le_card H.unsynced_subset
  have h1 := card_union_le (Oexp X ∪ O1t X ∪ O2t X) (O3t X)
  have h2 := card_union_le (Oexp X ∪ O1t X) (O2t X)
  have h3 := card_union_le (Oexp X) (O1t X)
  have hp1 : (Och X).card + (Oexp X).card = X.O.card := card_filter_add_card_filter_not _
  have hp2 : (O2p X).card + (O1t X).card = (Och X).card := card_filter_add_card_filter_not _
  have hpig := H.card_O2p_add_O2t_le
  have hk := H.isOpt.card
  omega

end Hyp

end BCFGJPSSV26.Stable


