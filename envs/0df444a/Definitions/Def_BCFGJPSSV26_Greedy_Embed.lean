-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Embed
-- name    : BCFGJPSSV26_Greedy_Embed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:47:36.169851+00:00
-- url     : https://prove2.me/theorems/7baae5bd-c744-454e-926d-21a3d1dced8e
-- title:
--   BCFGJPSSV26.Greedy.Embed — Embedding into the factor-revealing program
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Embed` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Appendix E.4]: for a facility `i⋆` and a nonempty set
--   `Dg` of clients with `α*_j ≥ ρ d(j, i⋆)`, the variables `r⋆` (`BCFGJPSSV26.Greedy.Run.rstar`), the
--   distances `d(j, i⋆)` and `f̂` are feasible for the factor-revealing program over `Dg`, ordered by
--   `BCFGJPSSV26.Greedy.Run.key` (`BCFGJPSSV26.Greedy.Run.embed_feasible`), except for the
--   normalization.
--
--   In the step-indexed language of `Greedy/Trace.lean`: the paper's `r_{jk}` is `Xv j (σ k)` and
--   `r_{j,n+1}` is `Xv j len`; `ζ_{jk}` is `Zv j (σ k)`. The event `FREEZING`
--   (`BCFGJPSSV26.Greedy.Run.Freezing`) is [BCFGJPSSV26a, Definition E.10]: the last client `kl` of
--   `Dg` becomes inactive at a regular opening of type 2 with `α*_kl > θ`, the opened facility `i₀⋆`
--   was openable only with respect to a strict superset, and `i⋆` is a candidate before that step;
--   `kf` is the first client of `Dg` that becomes inactive at that step with `α* > θ`.
--
--   The four constraint families are `BCFGJPSSV26.Greedy.Run.fr_facility`,
--   `BCFGJPSSV26.Greedy.Run.fr_mono`, `BCFGJPSSV26.Greedy.Run.fr_triangle` and
--   `BCFGJPSSV26.Greedy.Run.fr_metric` ([BCFGJPSSV26a, Lemmas E.13 to E.16]).
--
--   The proofs rest on a few facts about the execution (named `emb_*`), mainly that the values of the
--   clients that become inactive at the same step satisfy the triangle inequality
--   (`BCFGJPSSV26.Greedy.Run.emb_αs_triangle`, from (v) of the opening), hence that the chains `Xv` and
--   `Zv` at a step are `1`-Lipschitz in the client (`BCFGJPSSV26.Greedy.Run.emb_Xv_metric`,
--   `BCFGJPSSV26.Greedy.Run.emb_Zv_metric`); and, under FREEZING, on the explicit form of `r⋆_{jk}`
--   for `k ⪰ kf` (`BCFGJPSSV26.Greedy.Run.rstar_of_kf_le`): all such `k` become inactive at the step
--   of `kl`. The facility constraint (`BCFGJPSSV26.Greedy.Run.fr_facility`) is no overbidding before
--   the step at which `k` becomes inactive (after it, for a raise), except for a regular opening of
--   type 2 with `α*_k > θ` (`BCFGJPSSV26.Greedy.Run.facility_op2`), where it is (iv) for the opened
--   facility, by the freezing lemma. The chain lemma along the successor of a finite linear order
--   (`BCFGJPSSV26.Greedy.Embed.chain_nxt`) is used by `Greedy/LMP.lean`.
--
--   **Contents.** The module is published as a whole: 80 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.Run.Zv_ge_third`, `BCFGJPSSV26.Greedy.Run.embed_feasible`, `BCFGJPSSV26.Greedy.Run.rstar_nonneg` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Embed`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Embed.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Trace
public import Definitions.Def_BCFGJPSSV26_Greedy_FRP

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Embed` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Embedding into the factor-revealing program

[BCFGJPSSV26a, Appendix E.4]: for a facility `i⋆` and a nonempty set
`Dg` of clients with `α*_j ≥ ρ d(j, i⋆)`, the variables `r⋆` (`BCFGJPSSV26.Greedy.Run.rstar`), the
distances `d(j, i⋆)` and `f̂` are feasible for the factor-revealing program over `Dg`, ordered by
`BCFGJPSSV26.Greedy.Run.key` (`BCFGJPSSV26.Greedy.Run.embed_feasible`), except for the
normalization.

In the step-indexed language of `Greedy/Trace.lean`: the paper's `r_{jk}` is `Xv j (σ k)` and
`r_{j,n+1}` is `Xv j len`; `ζ_{jk}` is `Zv j (σ k)`. The event `FREEZING`
(`BCFGJPSSV26.Greedy.Run.Freezing`) is [BCFGJPSSV26a, Definition E.10]: the last client `kl` of
`Dg` becomes inactive at a regular opening of type 2 with `α*_kl > θ`, the opened facility `i₀⋆`
was openable only with respect to a strict superset, and `i⋆` is a candidate before that step;
`kf` is the first client of `Dg` that becomes inactive at that step with `α* > θ`.

The four constraint families are `BCFGJPSSV26.Greedy.Run.fr_facility`,
`BCFGJPSSV26.Greedy.Run.fr_mono`, `BCFGJPSSV26.Greedy.Run.fr_triangle` and
`BCFGJPSSV26.Greedy.Run.fr_metric` ([BCFGJPSSV26a, Lemmas E.13 to E.16]).

The proofs rest on a few facts about the execution (named `emb_*`), mainly that the values of the
clients that become inactive at the same step satisfy the triangle inequality
(`BCFGJPSSV26.Greedy.Run.emb_αs_triangle`, from (v) of the opening), hence that the chains `Xv` and
`Zv` at a step are `1`-Lipschitz in the client (`BCFGJPSSV26.Greedy.Run.emb_Xv_metric`,
`BCFGJPSSV26.Greedy.Run.emb_Zv_metric`); and, under FREEZING, on the explicit form of `r⋆_{jk}`
for `k ⪰ kf` (`BCFGJPSSV26.Greedy.Run.rstar_of_kf_le`): all such `k` become inactive at the step
of `kl`. The facility constraint (`BCFGJPSSV26.Greedy.Run.fr_facility`) is no overbidding before
the step at which `k` becomes inactive (after it, for a raise), except for a regular opening of
type 2 with `α*_k > θ` (`BCFGJPSSV26.Greedy.Run.facility_op2`), where it is (iv) for the opened
facility, by the freezing lemma. The chain lemma along the successor of a finite linear order
(`BCFGJPSSV26.Greedy.Embed.chain_nxt`) is used by `Greedy/LMP.lean`.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

/-! ### The successor in a finite linear order -/

namespace Embed

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem coe_lt_nxt (k : ι) : (k : WithTop ι) < FRP.nxt k := by
  unfold FRP.nxt
  rcases (univ.filter fun l ↦ k < l).eq_empty_or_nonempty with h | h
  · rw [Finset.min_eq_top.2 h]
    exact WithTop.coe_lt_top k
  · rw [← Finset.coe_min' h, WithTop.coe_lt_coe]
    exact (mem_filter.1 (Finset.min'_mem _ h)).2

theorem nxt_le_iff {k : ι} {u : WithTop ι} : FRP.nxt k ≤ u ↔ (k : WithTop ι) < u := by
  refine ⟨fun h ↦ (coe_lt_nxt k).trans_le h, fun h ↦ ?_⟩
  induction u using WithTop.recTopCoe with
  | top => exact le_top
  | coe l => exact Finset.min_le (mem_filter.2 ⟨mem_univ _, WithTop.coe_lt_coe.1 h⟩)

/-- **Chain lemma along the successor**: for times `t` monotone on `WithTop ι` and a sequence `x`
antitone on `[a, t u]`, the bids between consecutive steps from `t j` to `t u` add up to at most
the bids between the times of consecutive elements of `[j, u)`. -/
theorem chain_nxt (x : ℕ → ℚ) (t : WithTop ι → ℕ) (ht : Monotone t) (u : WithTop ι) {a : ℕ}
    (hx : ∀ s, a ≤ s → s < t u → x (s + 1) ≤ x s) (h0 : 0 ≤ x (t u)) (j : ι) (haj : a ≤ t j)
    (hju : (j : WithTop ι) ≤ u) :
    ∑ s ∈ Ico (t j) (t u), bid (x s) (x (s + 1)) ≤
      ∑ k ∈ univ.filter (fun k : ι ↦ j ≤ k ∧ (k : WithTop ι) < u),
        bid (x (t k)) (x (t (FRP.nxt k))) := by
  classical
  suffices H : ∀ N, ∀ j : ι,
      (univ.filter (fun k : ι ↦ j ≤ k ∧ (k : WithTop ι) < u)).card = N → a ≤ t j →
      (j : WithTop ι) ≤ u → ∑ s ∈ Ico (t j) (t u), bid (x s) (x (s + 1)) ≤
        ∑ k ∈ univ.filter (fun k : ι ↦ j ≤ k ∧ (k : WithTop ι) < u),
          bid (x (t k)) (x (t (FRP.nxt k))) from H _ j rfl haj hju
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro j hN haj hju
  rcases hju.lt_or_eq with hlt | heq
  · have hnu : FRP.nxt j ≤ u := nxt_le_iff.2 hlt
    have hj1 : t j ≤ t (FRP.nxt j) := ht (coe_lt_nxt j).le
    have hj2 : t (FRP.nxt j) ≤ t u := ht hnu
    have hxn : 0 ≤ x (t (FRP.nxt j)) := h0.trans (le_chain hx _ (haj.trans hj1) hj2)
    have hfirst := bid_chain_le hj1 (fun s h1 h2 ↦ hx s (haj.trans h1) (h2.trans_le hj2)) hxn
    rw [← sum_Ico_consecutive _ hj1 hj2]
    have hset : univ.filter (fun k : ι ↦ j ≤ k ∧ (k : WithTop ι) < u) =
        insert j (univ.filter (fun k : ι ↦ FRP.nxt j ≤ k ∧ (k : WithTop ι) < u)) := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_insert, nxt_le_iff, WithTop.coe_lt_coe]
      constructor
      · rintro ⟨h1, h2⟩
        rcases h1.lt_or_eq with h1 | h1
        · exact .inr ⟨h1, h2⟩
        · exact .inl h1.symm
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨le_rfl, hlt⟩
        · exact ⟨h1.le, h2⟩
    have hnot : j ∉ univ.filter (fun k : ι ↦ FRP.nxt j ≤ k ∧ (k : WithTop ι) < u) := by
      simp [nxt_le_iff]
    rw [hset, sum_insert hnot]
    have hrest : ∑ s ∈ Ico (t (FRP.nxt j)) (t u), bid (x s) (x (s + 1)) ≤
        ∑ k ∈ univ.filter (fun k : ι ↦ FRP.nxt j ≤ k ∧ (k : WithTop ι) < u),
          bid (x (t k)) (x (t (FRP.nxt k))) := by
      have hcard : (univ.filter (fun k : ι ↦ FRP.nxt j ≤ k ∧ (k : WithTop ι) < u)).card < N := by
        rw [← hN, hset, card_insert_of_notMem hnot]
        omega
      revert hcard hnu hj1 hj2
      induction FRP.nxt j using WithTop.recTopCoe with
      | top =>
        intro hnu _ _ _
        rw [top_le_iff.1 hnu, Ico_self, sum_empty]
        exact sum_nonneg fun _ _ ↦ bid_nonneg _ _
      | coe j' =>
        intro hnu hj1 _ hcard
        have := ih _ hcard j' (by simp only [WithTop.coe_le_coe]) (haj.trans hj1) hnu
        simpa only [WithTop.coe_le_coe] using this
    linarith
  · subst heq
    rw [Ico_self, sum_empty]
    exact sum_nonneg fun _ _ ↦ bid_nonneg _ _

theorem nxt_eq_top_of_max {k : ι} (h : ∀ l, l ≤ k) : FRP.nxt k = ⊤ := by
  unfold FRP.nxt
  rw [Finset.min_eq_top]
  exact filter_eq_empty_iff.2 fun l _ ↦ not_lt.2 (h l)

/-- `β(max(x, y), y) ≤ β(x, y)`. -/
theorem bid_max_le {x y : ℚ} (hy : 0 ≤ y) : bid (max x y) y ≤ bid x y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, bid_self hy]
    exact bid_nonneg _ _
  · rw [max_eq_left h]

end Embed

namespace Run

variable {n m : ℕ} (R : Run n m)

/-! ### Facts about the execution used by the embedding -/

theorem emb_θs_le_θpost (s : ℕ) : R.θs s ≤ R.θpost s := by
  unfold θpost
  split_ifs
  · have := R.one_le_θs s
    unfold Par.θplus
    nlinarith [sq_nonneg R.P.ε]
  · exact le_rfl

theorem emb_θs_nonneg (s : ℕ) : 0 ≤ R.θs s := zero_le_one.trans (R.one_le_θs s)

/-- Profiles before a step are `1`-Lipschitz. -/
theorem emb_Dpre_lip (s : ℕ) (j l : Fin n) : R.Dpre s j ≤ R.Dpre s l + R.X.dC j l :=
  profF_lipschitz R.P.K R.X (pairs (R.pre s)) j l

/-- Profiles of witnesses are `1`-Lipschitz. -/
theorem emb_Dt_lip (s : ℕ) (j l : Fin n) : R.Dt s j ≤ R.Dt s l + R.X.dC j l :=
  profF_lipschitz R.P.K R.X _ j l

/-- A client that became inactive before step `s` is inactive at the time of step `s`. -/
theorem emb_inact_before {j : Fin n} {s : ℕ} (hjs : R.σ j < s) (hs : s < R.len) :
    (1 - R.P.δ) * R.Dpre s j ≤ R.θs s := by
  have h := R.inact_mono (R.inact_σ j) (show R.σ j ≤ s - 1 by omega) (by omega)
  have e : s - 1 + 1 = s := by omega
  unfold Inact at h
  rw [R.θpost_eq (by omega), e] at h
  exact h

/-- A client that becomes inactive at or after step `s` is active before it. -/
theorem emb_active_of_le {j : Fin n} {s : ℕ} (h : s ≤ R.σ j) :
    R.θs s < (1 - R.P.δ) * R.Dpre s j := by
  rcases h.lt_or_eq with h | h
  · have h1 := R.not_inact_of_lt h
    unfold Inact at h1
    push Not at h1
    have h2 := R.Dpre_anti (Nat.le_succ s) j
    have h3 := R.emb_θs_le_θpost s
    have hδ := R.good.one_sub_δ_pos
    nlinarith
  · rw [h]
    exact R.active_before j

/-- A client active before step `s` that became inactive at or before `s` does so at `s`. -/
theorem emb_σ_eq_of_active {j : Fin n} {s : ℕ} (h : R.σ j ≤ s) (hs : s < R.len)
    (hact : R.θs s < (1 - R.P.δ) * R.Dpre s j) : R.σ j = s := by
  by_contra hne
  have := R.emb_inact_before (lt_of_le_of_ne h hne) hs
  linarith

theorem emb_σ_eq_of_active_Dt {j : Fin n} {s : ℕ} (h : R.σ j ≤ s) (hs : s < R.len)
    (hact : R.θs s < (1 - R.P.δ) * R.Dt s j) : R.σ j = s := by
  refine R.emb_σ_eq_of_active h hs (hact.trans_le ?_)
  exact mul_le_mul_of_nonneg_left (R.Dt_le s j) R.good.one_sub_δ_pos.le

theorem emb_αs_of_raise {j : Fin n} {s : ℕ} (hs : R.σ j = s) (hk : (R.step s).kind = .raise) :
    R.αs j = (1 - R.P.δ) * R.Dpre s j := by
  subst hs
  unfold αs
  rw [hk]

theorem emb_αs_of_op_θ {j : Fin n} {s : ℕ} {a : Atom m} (hs : R.σ j = s)
    (hk : (R.step s).kind = .op a) (h : typ1 (R.step s).seq = true ∨ a.free = true) :
    R.αs j = R.θs s := by
  subst hs
  unfold αs
  rw [hk]
  exact if_pos h

theorem emb_αs_of_op2 {j : Fin n} {s : ℕ} {a : Atom m} (hs : R.σ j = s) (hop : R.IsOp2 s a) :
    R.αs j = if R.θs s < (1 - R.P.δ) * R.Dt s j then
      mT R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) j else R.θs s := by
  subst hs
  unfold αs
  rw [hop.1]
  refine if_neg ?_
  rw [hop.2.1, hop.2.2]
  decide

theorem emb_αs_of_op2_active {j : Fin n} {s : ℕ} {a : Atom m} (hs : R.σ j = s) (hop : R.IsOp2 s a)
    (hact : R.θs s < (1 - R.P.δ) * R.Dt s j) :
    R.αs j = mT R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) j := by
  rw [R.emb_αs_of_op2 hs hop, if_pos hact]

/-- A client with `α* > θ` at a regular opening of type 2 is active for the witness. -/
theorem emb_active_Dt_of_lt_αs {j : Fin n} {s : ℕ} {a : Atom m} (hs : R.σ j = s)
    (hop : R.IsOp2 s a) (h : R.θs s < R.αs j) : R.θs s < (1 - R.P.δ) * R.Dt s j := by
  by_contra hc
  rw [R.emb_αs_of_op2 hs hop, if_neg hc] at h
  exact lt_irrefl _ h

theorem emb_αs_le_Dt {j : Fin n} {s : ℕ} {a : Atom m} (hs : R.σ j = s) (hop : R.IsOp2 s a)
    (hact : R.θs s < (1 - R.P.δ) * R.Dt s j) : R.αs j ≤ (1 - R.P.δ) * R.Dt s j := by
  rw [R.emb_αs_of_op2_active hs hop hact]
  exact mT_le_D _ _ _ _ _

theorem emb_Zv_of_active {j : Fin n} {s : ℕ} (hσ : R.σ j ≤ s) (hs : s < R.len)
    (hact : R.θs s < (1 - R.P.δ) * R.Dt s j) : R.Zv j s = R.αs j := by
  unfold Zv
  rw [if_pos hact, if_pos (R.emb_σ_eq_of_active_Dt hσ hs hact)]

theorem emb_Zv_of_inactive {j : Fin n} {s : ℕ} (hact : ¬ R.θs s < (1 - R.P.δ) * R.Dt s j) :
    R.Zv j s = (1 - R.P.δ) * R.Dt s j := by
  unfold Zv
  rw [if_neg hact]

theorem emb_Xv_self (j : Fin n) : R.Xv j (R.σ j) = R.αs j := by
  unfold Xv
  rw [if_pos rfl]

theorem emb_Xv_of_lt {j : Fin n} {s : ℕ} (h : R.σ j < s) : R.Xv j s = (1 - R.P.δ) * R.Dpre s j := by
  unfold Xv
  rw [if_neg (by omega)]

/-- The chain is antitone after `σ j`, over any interval. -/
theorem emb_Xv_le_of_le {j : Fin n} {s s' : ℕ} (h1 : R.σ j ≤ s) (h2 : s ≤ s') (h3 : s' ≤ R.len) :
    R.Xv j s' ≤ R.Xv j s :=
  chain_le (x := R.Xv j) (a := s) (b := R.len) (fun _ ht ht' ↦ R.Xv_anti (h1.trans ht) ht') s'
    h2 h3

theorem emb_isOp2_of {s : ℕ} {a : Atom m} (hk : (R.step s).kind = .op a)
    (h : ¬ (typ1 (R.step s).seq = true ∨ a.free = true)) : R.IsOp2 s a := by
  push Not at h
  exact ⟨hk, by simpa using h.1, by simpa using h.2⟩

theorem emb_Dpre_succ_raise {s : ℕ} (hs : s < R.len) (hk : (R.step s).kind = .raise) :
    R.Dpre (s + 1) = R.Dpre s := by
  unfold Dpre
  rw [R.pre_succ hs, hk]
  simp [Kind.atom?]

theorem emb_Xv_le_cval {j : Fin n} {s : ℕ} (h : R.σ j ≤ s) (hs : s < R.len) :
    R.Xv j s ≤ cval R.P (R.θs s) (R.Dpre s) j := by
  unfold cval
  rcases h.lt_or_eq with h | h
  · rw [R.emb_Xv_of_lt h, if_neg (not_lt.2 (R.emb_inact_before h hs))]
  · rw [if_pos (h ▸ R.active_before j), ← h, R.emb_Xv_self]
    exact R.αs_le_θplus j

/-- An atom opened before some step is an atom of the solution. -/
theorem emb_mem_flatten {s : ℕ} {a : Atom m} (h : a ∈ R.pre s) : a ∈ R.H.flatten := by
  have h' : a ∈ R.pre R.len := by
    unfold pre at h ⊢
    rw [List.mem_filterMap] at h ⊢
    obtain ⟨x, hx, hxa⟩ := h
    exact ⟨x, by rw [len, List.take_length]; exact List.mem_of_mem_take hx, hxa⟩
  rw [R.pre_len] at h'
  exact h'

/-- Clients that become inactive at the same step: `α*_j ≤ α*_l + d(j, l)`. -/
theorem emb_αs_triangle {j l : Fin n} (h : R.σ j = R.σ l) : R.αs j ≤ R.αs l + R.X.dC j l := by
  have hC : 0 ≤ R.X.dC j l := R.X.nonneg _ _
  have hδ := R.good.one_sub_δ_pos
  have hδ' := R.good.δ_pos
  have hs : R.σ l < R.len := R.σ_lt l
  rcases hk : (R.step (R.σ l)).kind with a | _
  · by_cases h12 : typ1 (R.step (R.σ l)).seq = true ∨ a.free = true
    · rw [R.emb_αs_of_op_θ h hk h12, R.emb_αs_of_op_θ rfl hk h12]
      linarith
    · have hop : R.IsOp2 (R.σ l) a := R.emb_isOp2_of hk h12
      have hT := (R.wit_spec hs hop).2.2.1
      have hθ := R.emb_θs_nonneg (R.σ l)
      by_cases hjA : R.θs (R.σ l) < (1 - R.P.δ) * R.Dt (R.σ l) j
      · by_cases hlA : R.θs (R.σ l) < (1 - R.P.δ) * R.Dt (R.σ l) l
        · rw [R.emb_αs_of_op2_active h hop hjA, R.emb_αs_of_op2_active rfl hop hlA]
          exact mT_triangle R.good R.X _ hθ hT a.fac hjA hlA
        · have h1 := R.emb_αs_le_Dt h hop hjA
          rw [R.emb_αs_of_op2 rfl hop, if_neg hlA]
          have h2 := R.emb_Dt_lip (R.σ l) j l
          push Not at hlA
          nlinarith
      · rw [R.emb_αs_of_op2 h hop, if_neg hjA]
        have := R.θs_le_αs l
        linarith
  · rw [R.emb_αs_of_raise h hk, R.emb_αs_of_raise rfl hk]
    have := R.emb_Dpre_lip (R.σ l) j l
    nlinarith

/-- The chain at a step `s` after `σ j` and `σ l` is `1`-Lipschitz in the client. -/
theorem emb_Xv_metric {j l : Fin n} {s : ℕ} (hj : R.σ j ≤ s) (hl : R.σ l ≤ s) :
    R.Xv j s ≤ R.Xv l s + R.X.dC j l := by
  have hC : 0 ≤ R.X.dC j l := R.X.nonneg _ _
  have hδ := R.good.one_sub_δ_pos
  have hδ' := R.good.δ_pos
  have hlip := R.emb_Dpre_lip s j l
  rcases hj.lt_or_eq with hj | hj <;> rcases hl.lt_or_eq with hl | hl
  · rw [R.emb_Xv_of_lt hj, R.emb_Xv_of_lt hl]
    nlinarith
  · have hslen : s < R.len := hl ▸ R.σ_lt l
    have h1 := R.emb_inact_before hj hslen
    have h2 := R.θs_le_αs l
    rw [hl] at h2
    rw [R.emb_Xv_of_lt hj, show R.Xv l s = R.αs l from hl ▸ R.emb_Xv_self l]
    linarith
  · have h1 := R.αs_le_Dpre j
    rw [hj] at h1
    rw [R.emb_Xv_of_lt hl, show R.Xv j s = R.αs j from hj ▸ R.emb_Xv_self j]
    nlinarith
  · rw [← hj, R.emb_Xv_self]
    have := R.emb_αs_triangle (j := j) (l := l) (hj.trans hl.symm)
    rw [Xv, if_pos (show R.σ j = R.σ l by omega)]
    exact this

/-- The values `Z` at a regular opening of type 2 are `1`-Lipschitz in the client. -/
theorem emb_Zv_metric {j l : Fin n} {s : ℕ} {a : Atom m} (hop : R.IsOp2 s a) (hs : s < R.len)
    (hj : R.σ j ≤ s) (hl : R.σ l ≤ s) : R.Zv j s ≤ R.Zv l s + R.X.dC j l := by
  have hC : 0 ≤ R.X.dC j l := R.X.nonneg _ _
  have hδ := R.good.one_sub_δ_pos
  have hδ' := R.good.δ_pos
  have hlip := R.emb_Dt_lip s j l
  by_cases hjA : R.θs s < (1 - R.P.δ) * R.Dt s j
  · have hσj := R.emb_σ_eq_of_active_Dt hj hs hjA
    rw [R.emb_Zv_of_active hj hs hjA]
    by_cases hlA : R.θs s < (1 - R.P.δ) * R.Dt s l
    · have hσl := R.emb_σ_eq_of_active_Dt hl hs hlA
      rw [R.emb_Zv_of_active hl hs hlA]
      exact R.emb_αs_triangle (hσj.trans hσl.symm)
    · rw [R.emb_Zv_of_inactive hlA]
      have := R.emb_αs_le_Dt hσj hop hjA
      push Not at hlA
      nlinarith
  · rw [R.emb_Zv_of_inactive hjA]
    push Not at hjA
    by_cases hlA : R.θs s < (1 - R.P.δ) * R.Dt s l
    · have hσl := R.emb_σ_eq_of_active_Dt hl hs hlA
      rw [R.emb_Zv_of_active hl hs hlA]
      have := R.θs_le_αs l
      rw [hσl] at this
      linarith
    · rw [R.emb_Zv_of_inactive hlA]
      nlinarith

/-- The clients of `Dg`, as a type, to be ordered by `key`. -/
def DgT (_R : Run n m) (Dg : Finset (Fin n)) : Type := {j : Fin n // j ∈ Dg}

variable (Dg : Finset (Fin n))

instance : Fintype (R.DgT Dg) := inferInstanceAs (Fintype {j : Fin n // j ∈ Dg})

instance : DecidableEq (R.DgT Dg) := inferInstanceAs (DecidableEq {j : Fin n // j ∈ Dg})

/-- The client of an element of `DgT`. -/
def DgT.val {R : Run n m} {Dg : Finset (Fin n)} (j : R.DgT Dg) : Fin n := Subtype.val j

theorem DgT.val_injective {R : Run n m} {Dg : Finset (Fin n)} :
    Function.Injective (DgT.val : R.DgT Dg → Fin n) := Subtype.val_injective

noncomputable instance : LinearOrder (R.DgT Dg) :=
  LinearOrder.lift' (fun j ↦ R.key j.val) (R.key_injective.comp DgT.val_injective)

theorem DgT.le_iff {j k : R.DgT Dg} : j ≤ k ↔ R.key j.val ≤ R.key k.val := Iff.rfl

theorem DgT.lt_iff {j k : R.DgT Dg} : j < k ↔ R.key j.val < R.key k.val := Iff.rfl

/-- The sum over `DgT` is the sum over `Dg`. -/
theorem sum_DgT (g : Fin n → ℚ) : ∑ j : R.DgT Dg, g j.val = ∑ j ∈ Dg, g j :=
  Finset.sum_coe_sort Dg g

variable {Dg}

/-- The step of a time `k`: `σ k` for a client, `len` for `⊤`. -/
noncomputable def time (k : WithTop (R.DgT Dg)) : ℕ := WithTop.recTopCoe R.len (fun k ↦ R.σ k.val) k

/-- The paper's `r_{jk}`. -/
noncomputable def r (j : R.DgT Dg) (k : WithTop (R.DgT Dg)) : ℚ := R.Xv j.val (R.time k)

/-- The paper's `ζ_{jk}`. -/
noncomputable def ζ (j : R.DgT Dg) (k : WithTop (R.DgT Dg)) : ℚ :=
  WithTop.recTopCoe (R.Xv j.val R.len) (fun k ↦ R.Zv j.val (R.σ k.val)) k

theorem emb_σ_le_of_le {j k : R.DgT Dg} (h : j ≤ k) : R.σ j.val ≤ R.σ k.val := by
  have h' : R.key j.val ≤ R.key k.val := h
  unfold key at h'
  rcases Prod.Lex.toLex_le_toLex.1 h' with h1 | ⟨h1, _⟩
  · exact h1.le
  · exact h1.le

theorem emb_αs_le_of_le {j k : R.DgT Dg} (h : j ≤ k) (hσ : R.σ j.val = R.σ k.val) :
    R.αs j.val ≤ R.αs k.val := by
  have h' : R.key j.val ≤ R.key k.val := h
  unfold key at h'
  rcases Prod.Lex.toLex_le_toLex.1 h' with h1 | ⟨_, h2⟩
  · exact absurd hσ (ne_of_lt h1)
  · rcases Prod.Lex.toLex_le_toLex.1 h2 with h3 | ⟨h3, _⟩
    · exact h3.le
    · exact h3.le

theorem time_top : R.time (⊤ : WithTop (R.DgT Dg)) = R.len := rfl

theorem time_coe (k : R.DgT Dg) : R.time (k : WithTop (R.DgT Dg)) = R.σ k.val := rfl

theorem time_le_len (k : WithTop (R.DgT Dg)) : R.time k ≤ R.len := by
  induction k using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe k => exact (R.σ_lt _).le

theorem time_mono : Monotone (R.time (Dg := Dg)) := by
  intro k k' h
  induction k' using WithTop.recTopCoe with
  | top => exact R.time_le_len k
  | coe k' =>
    induction k using WithTop.recTopCoe with
    | top => exact absurd h (by simp)
    | coe k => exact R.emb_σ_le_of_le (WithTop.coe_le_coe.1 h)

theorem r_eq (j : R.DgT Dg) (k : WithTop (R.DgT Dg)) : R.r j k = R.Xv j.val (R.time k) := rfl

theorem ζ_coe (j k : R.DgT Dg) : R.ζ j k = R.Zv j.val (R.σ k.val) := rfl

theorem σ_le_time {j : R.DgT Dg} {k : WithTop (R.DgT Dg)} (h : (j : WithTop (R.DgT Dg)) ≤ k) :
    R.σ j.val ≤ R.time k := R.time_mono h

variable (hne : Dg.Nonempty)
include hne

theorem DgT_nonempty : Nonempty (R.DgT Dg) := ⟨⟨hne.choose, hne.choose_spec⟩⟩

/-- The last client of `Dg`. -/
noncomputable def kl : R.DgT Dg :=
  haveI := R.DgT_nonempty hne
  (univ : Finset (R.DgT Dg)).max' univ_nonempty

/-- The time of the step at which the last client becomes inactive. -/
noncomputable def θl : ℚ := R.θs (R.σ (R.kl hne).val)

omit hne in
/-- The facility opened at step `s` (`i` if the step is a raise). -/
def opened (s : ℕ) (i : Fin m) : Fin m :=
  match (R.step s).kind with
  | .op a => a.fac
  | .raise => i

/-- The event **FREEZING** for `i⋆` and `Dg`. -/
def Freezing (istar : Fin m) : Prop :=
  ∃ a, R.IsOp2 (R.σ (R.kl hne).val) a ∧ R.θl hne < R.αs (R.kl hne).val ∧
    (¬ ∃ T, R.WitOK (R.σ (R.kl hne).val) a (pairs (R.pre (R.σ (R.kl hne).val))) T) ∧
    Cand R.P R.X.d R.f R.P.η (R.θl hne) (R.Dpre (R.σ (R.kl hne).val)) istar

open Classical in
/-- The first client of `Dg` that becomes inactive at the step of the last one with `α* > θ`
(the last one if there is none). -/
noncomputable def kf : R.DgT Dg :=
  if h : ((univ : Finset (R.DgT Dg)).filter fun j ↦
      R.σ j.val = R.σ (R.kl hne).val ∧ R.θl hne < R.αs j.val).Nonempty then
    Finset.min' _ h
  else R.kl hne

open Classical in
/-- The variables **`r⋆`** of the factor-revealing program. -/
noncomputable def rstar (istar : Fin m) (j : R.DgT Dg) (k : WithTop (R.DgT Dg)) : ℚ :=
  if R.Freezing hne istar ∧ k = ⊤ then 0
  else if R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ k then
    (if R.X.d j.val (R.opened (R.σ (R.kl hne).val) istar) ≤ R.θl hne / 3 then R.ζ j k
      else min (R.r j k) (max (R.ζ j k) (R.X.d j.val istar)))
  else R.r j k

/-! ### The last client, the first frozen client and `r⋆` -/

omit hne in
theorem opened_eq {s : ℕ} {a : Atom m} (hop : R.IsOp2 s a) (i : Fin m) : R.opened s i = a.fac := by
  unfold opened
  rw [hop.1]

theorem le_kl (j : R.DgT Dg) : j ≤ R.kl hne := by
  unfold kl
  exact le_max' _ _ (mem_univ j)

theorem σ_le_σkl (j : R.DgT Dg) : R.σ j.val ≤ R.σ (R.kl hne).val := R.emb_σ_le_of_le (R.le_kl hne j)

theorem θl_pos : 0 < R.θl hne := zero_lt_one.trans_le (R.one_le_θs _)

theorem kf_mem (hgt : R.θl hne < R.αs (R.kl hne).val) :
    R.σ (R.kf hne).val = R.σ (R.kl hne).val ∧ R.θl hne < R.αs (R.kf hne).val := by
  classical
  unfold kf
  split_ifs with h
  · exact (mem_filter.1 (min'_mem _ h)).2
  · exact ⟨rfl, hgt⟩

theorem kf_le {j : R.DgT Dg} (hσ : R.σ j.val = R.σ (R.kl hne).val) (hα : R.θl hne < R.αs j.val) :
    R.kf hne ≤ j := by
  classical
  unfold kf
  split_ifs with h
  · exact min'_le _ _ (mem_filter.2 ⟨mem_univ _, hσ, hα⟩)
  · exact absurd ⟨j, mem_filter.2 ⟨mem_univ _, hσ, hα⟩⟩ h

/-- The clients after `kf` become inactive at the step of `kl`, with `α* > θ`. -/
theorem of_kf_le (hgt : R.θl hne < R.αs (R.kl hne).val) {k : R.DgT Dg} (h : R.kf hne ≤ k) :
    R.σ k.val = R.σ (R.kl hne).val ∧ R.θl hne < R.αs k.val := by
  obtain ⟨h1, h2⟩ := R.kf_mem hne hgt
  have a := R.emb_σ_le_of_le h
  have b := R.σ_le_σkl hne k
  have hσ : R.σ k.val = R.σ (R.kl hne).val := by omega
  exact ⟨hσ, h2.trans_le (R.emb_αs_le_of_le h (h1.trans hσ.symm))⟩

section

variable {istar : Fin m}

theorem freezing_gt (hF : R.Freezing hne istar) : R.θl hne < R.αs (R.kl hne).val := by
  obtain ⟨_, _, h, _⟩ := hF
  exact h

theorem rstar_top_of (hF : R.Freezing hne istar) (j : R.DgT Dg) : R.rstar hne istar j ⊤ = 0 := by
  unfold rstar
  rw [if_pos ⟨hF, rfl⟩]

theorem rstar_of_not_freezing (hF : ¬ R.Freezing hne istar) (j : R.DgT Dg)
    (k : WithTop (R.DgT Dg)) : R.rstar hne istar j k = R.r j k := by
  unfold rstar
  rw [if_neg fun h ↦ hF h.1, if_neg fun h ↦ hF h.1]

theorem rstar_coe_of_not {k : R.DgT Dg}
    (h : ¬ (R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ k)) (j : R.DgT Dg) :
    R.rstar hne istar j k = R.r j k := by
  unfold rstar
  rw [if_neg fun h' ↦ WithTop.coe_ne_top h'.2, if_neg h]

theorem rstar_of_kf_le (hF : R.Freezing hne istar) {k : R.DgT Dg} (hk : R.kf hne ≤ k)
    (j : R.DgT Dg) : R.rstar hne istar j k =
      if R.X.d j.val (R.opened (R.σ (R.kl hne).val) istar) ≤ R.θl hne / 3 then
        R.Zv j.val (R.σ (R.kl hne).val)
      else min (R.Xv j.val (R.σ (R.kl hne).val))
        (max (R.Zv j.val (R.σ (R.kl hne).val)) (R.X.d j.val istar)) := by
  have hσ := (R.of_kf_le hne (R.freezing_gt hne hF) hk).1
  unfold rstar
  rw [if_neg fun h' ↦ WithTop.coe_ne_top h'.2,
    if_pos ⟨hF, WithTop.coe_le_coe.2 hk⟩]
  simp only [ζ_coe, r_eq, time_coe, hσ]

theorem Zv_le_Xv_kl (j : R.DgT Dg) :
    R.Zv j.val (R.σ (R.kl hne).val) ≤ R.Xv j.val (R.σ (R.kl hne).val) :=
  R.Zv_le_Xv (R.σ_le_σkl hne j) (R.σ_lt _)

theorem rstar_ge_Zv (hF : R.Freezing hne istar) {k : R.DgT Dg} (hk : R.kf hne ≤ k)
    (j : R.DgT Dg) : R.Zv j.val (R.σ (R.kl hne).val) ≤ R.rstar hne istar j k := by
  rw [R.rstar_of_kf_le hne hF hk]
  have := R.Zv_le_Xv_kl hne j
  split_ifs
  · exact le_rfl
  · exact le_min this (le_max_left _ _)

theorem rstar_le_max (hF : R.Freezing hne istar) {k : R.DgT Dg} (hk : R.kf hne ≤ k)
    (j : R.DgT Dg) :
    R.rstar hne istar j k ≤ max (R.Zv j.val (R.σ (R.kl hne).val)) (R.X.d j.val istar) := by
  rw [R.rstar_of_kf_le hne hF hk]
  split_ifs
  · exact le_max_left _ _
  · exact min_le_right _ _

/-- `r⋆ ≤ r`. -/
theorem rstar_le_r (j : R.DgT Dg) (k : WithTop (R.DgT Dg)) :
    R.rstar hne istar j k ≤ R.r j k := by
  by_cases hF : R.Freezing hne istar
  · induction k using WithTop.recTopCoe with
    | top =>
      rw [R.rstar_top_of hne hF]
      exact R.Xv_nonneg _ _
    | coe k =>
      by_cases hk : R.kf hne ≤ k
      · rw [R.rstar_of_kf_le hne hF hk, r_eq, time_coe,
          (R.of_kf_le hne (R.freezing_gt hne hF) hk).1]
        have := R.Zv_le_Xv_kl hne j
        split_ifs
        · exact this
        · exact min_le_left _ _
      · rw [R.rstar_coe_of_not hne (fun h' ↦ hk (WithTop.coe_le_coe.1 h'.2))]
  · rw [R.rstar_of_not_freezing hne hF]

/-- Under **FREEZING**, `r⋆ = α*` for a client active for the witness. -/
theorem rstar_of_active (hF : R.Freezing hne istar) {k : R.DgT Dg} (hk : R.kf hne ≤ k)
    (j : R.DgT Dg) (hact : R.θs (R.σ (R.kl hne).val) <
      (1 - R.P.δ) * R.Dt (R.σ (R.kl hne).val) j.val) :
    R.rstar hne istar j k = R.αs j.val := by
  have hs := R.σ_lt (R.kl hne).val
  have hσ := R.emb_σ_eq_of_active_Dt (R.σ_le_σkl hne j) hs hact
  have hZ := R.emb_Zv_of_active (R.σ_le_σkl hne j) hs hact
  have hX : R.Xv j.val (R.σ (R.kl hne).val) = R.αs j.val := hσ ▸ R.emb_Xv_self j.val
  rw [R.rstar_of_kf_le hne hF hk, hZ, hX]
  split_ifs
  · rfl
  · exact min_eq_left (le_max_left _ _)

/-- The facility constraint at `k` from a bound of each term by a nonnegative `g j`. -/
theorem facility_le_sum (k : R.DgT Dg) (g : Fin n → ℚ) (hg : ∀ j, 0 ≤ g j)
    (h1 : ∀ j : R.DgT Dg, j < k → bid (R.rstar hne istar j k) (R.X.d j.val istar) ≤ g j.val)
    (h2 : ∀ j : R.DgT Dg, k ≤ j → bid (R.αs k.val) (R.X.d j.val istar) ≤ g j.val) :
    (∑ j ∈ univ.filter (· < k), bid (R.rstar hne istar j k) (R.X.d j.val istar)) +
      (∑ j ∈ univ.filter (k ≤ ·), bid (R.αs k.val) (R.X.d j.val istar)) ≤ ∑ j, g j := by
  have e1 : ∑ j ∈ univ.filter (· < k), bid (R.rstar hne istar j k) (R.X.d j.val istar) ≤
      ∑ j ∈ univ.filter (· < k), g j.val := sum_le_sum fun j hj ↦ h1 j (mem_filter.1 hj).2
  have e2 : ∑ j ∈ univ.filter (k ≤ ·), bid (R.αs k.val) (R.X.d j.val istar) ≤
      ∑ j ∈ univ.filter (k ≤ ·), g j.val := sum_le_sum fun j hj ↦ h2 j (mem_filter.1 hj).2
  have e3 : ∑ j ∈ univ.filter (· < k), g j.val + ∑ j ∈ univ.filter (k ≤ ·), g j.val =
      ∑ j : R.DgT Dg, g j.val := by
    rw [← sum_filter_add_sum_filter_not univ (· < k)]
    congr 1
    exact sum_congr (filter_congr fun j _ ↦ not_lt.symm) fun _ _ ↦ rfl
  have e4 : ∑ j : R.DgT Dg, g j.val ≤ ∑ j, g j := by
    rw [R.sum_DgT Dg g]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ ↦ hg j
  linarith

end

/-! ### Feasibility -/

variable {istar : Fin m} (hD : ∀ j ∈ Dg, ρ * R.X.d j istar ≤ R.αs j)
include hD

set_option linter.unusedSectionVars false in
/-- On the diagonal, `r⋆_{jj} = α*_j`. -/
theorem rstar_diag (j : R.DgT Dg) : R.rstar hne istar j j = R.αs j.val := by
  by_cases h : R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ j
  · obtain ⟨hF, hk⟩ := h
    have hk' := WithTop.coe_le_coe.1 hk
    obtain ⟨hσ, hα⟩ := R.of_kf_le hne (R.freezing_gt hne hF) hk'
    obtain ⟨a, hop, -⟩ := id hF
    exact R.rstar_of_active hne hF hk' j (R.emb_active_Dt_of_lt_αs hσ hop hα)
  · rw [R.rstar_coe_of_not hne h, r_eq, time_coe, R.emb_Xv_self]

/-- The facility constraint at a client `k` with `α*_k > θ` that becomes inactive at a regular
opening of type 2: otherwise `i⋆` would be a candidate, and then the freezing lemma and (iv) for
the opened facility give the bound. -/
theorem facility_op2 (k : R.DgT Dg) {a : Atom m} (hop : R.IsOp2 (R.σ k.val) a)
    (hgt : R.θs (R.σ k.val) < R.αs k.val) :
    (∑ j ∈ univ.filter (· < k), bid (R.rstar hne istar j k) (R.X.d j.val istar)) +
      (∑ j ∈ univ.filter (k ≤ ·), bid (R.αs k.val) (R.X.d j.val istar)) ≤ R.f := by
  have hs : R.σ k.val < R.len := R.σ_lt _
  have hδ := R.good.δ_pos
  have hhalf : ∀ j, (1 - R.P.δ / 2) * R.X.d j istar ≤ R.X.d j istar := fun j ↦ by
    have := R.X.d_nonneg j istar
    nlinarith
  by_contra hcon
  push Not at hcon
  -- `i⋆` is a candidate before the step
  have hc2 : ∀ j : R.DgT Dg, k ≤ j → bid (R.αs k.val) (R.X.d j.val istar) ≤
      bid (cval R.P (R.θs (R.σ k.val)) (R.Dpre (R.σ k.val)) j.val)
        ((1 - R.P.δ / 2) * R.X.d j.val istar) := by
    intro j hkj
    refine (bid_anti_right _ (hhalf j.val)).trans (bid_mono_left ?_ _)
    unfold cval
    rw [if_pos (R.emb_active_of_le (R.emb_σ_le_of_le hkj))]
    exact R.αs_le_θplus k.val
  have hc1 : ∀ j : R.DgT Dg, j < k → bid (R.rstar hne istar j k) (R.X.d j.val istar) ≤
      bid (cval R.P (R.θs (R.σ k.val)) (R.Dpre (R.σ k.val)) j.val)
        ((1 - R.P.δ / 2) * R.X.d j.val istar) := fun j hjk ↦
    (bid_anti_right _ (hhalf j.val)).trans (bid_mono_left ((R.rstar_le_r hne j k).trans
      (R.emb_Xv_le_cval (R.emb_σ_le_of_le hjk.le) hs)) _)
  have hcand : Cand R.P R.X.d R.f R.P.η (R.θs (R.σ k.val)) (R.Dpre (R.σ k.val)) istar := by
    have hle := R.facility_le_sum hne k (fun j ↦ bid (cval R.P (R.θs (R.σ k.val))
      (R.Dpre (R.σ k.val)) j) ((1 - R.P.δ / 2) * R.X.d j istar)) (fun j ↦ bid_nonneg _ _) hc1 hc2
    have : (0 : ℚ) ≤ n * R.P.η := by
      have := R.good.η_nonneg
      positivity
    unfold Cand candSum
    linarith
  -- the freezing lemma
  obtain ⟨-, hfrz⟩ := R.freezing hD k.2 hop hgt hcand
  have hσkl : R.σ (R.kl hne).val = R.σ k.val :=
    hfrz _ (R.kl hne).2 (R.emb_σ_le_of_le (R.le_kl hne k))
  -- if `i₀⋆` was openable only for a strict superset, **FREEZING** happens and `kf ≤ k`
  have hstrict : (¬ ∃ T, R.WitOK (R.σ k.val) a (pairs (R.pre (R.σ k.val))) T) →
      R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ k := by
    intro hstr
    have hαkl : R.αs k.val ≤ R.αs (R.kl hne).val :=
      R.emb_αs_le_of_le (R.le_kl hne k) hσkl.symm
    have hθl : R.θl hne = R.θs (R.σ k.val) := by
      unfold θl
      rw [hσkl]
    refine ⟨⟨a, by rw [hσkl]; exact hop, by rw [hθl]; linarith, by rw [hσkl]; exact hstr,
      by rw [hθl, hσkl]; exact hcand⟩,
      WithTop.coe_le_coe.2 (R.kf_le hne hσkl.symm (by rw [hθl]; exact hgt))⟩
  -- (iv) for the opened facility, at `i⋆`
  have h4 : ∑ j, bid (mT R.P R.X.d (R.θs (R.σ k.val)) (R.Dt (R.σ k.val)) a.fac
      (R.Tt (R.σ k.val)) j) (R.X.d j istar) ≤ R.f := (R.wit_spec hs hop).2.2.2.2.2 istar
  have h2 : ∀ j : R.DgT Dg, k ≤ j → bid (R.αs k.val) (R.X.d j.val istar) ≤
      bid (mT R.P R.X.d (R.θs (R.σ k.val)) (R.Dt (R.σ k.val)) a.fac (R.Tt (R.σ k.val)) j.val)
        (R.X.d j.val istar) := by
    intro j hkj
    have hσj : R.σ j.val = R.σ k.val := hfrz _ j.2 (R.emb_σ_le_of_le hkj)
    have hα := R.emb_αs_le_of_le hkj hσj.symm
    have hjA := R.emb_active_Dt_of_lt_αs hσj hop (hgt.trans_le hα)
    rw [← R.emb_αs_of_op2_active hσj hop hjA]
    exact bid_mono_left hα _
  have h1 : ∀ j : R.DgT Dg, j < k → bid (R.rstar hne istar j k) (R.X.d j.val istar) ≤
      bid (mT R.P R.X.d (R.θs (R.σ k.val)) (R.Dt (R.σ k.val)) a.fac (R.Tt (R.σ k.val)) j.val)
        (R.X.d j.val istar) := by
    intro j hjk
    have hσj := R.emb_σ_le_of_le hjk.le
    by_cases hjA : R.θs (R.σ k.val) < (1 - R.P.δ) * R.Dt (R.σ k.val) j.val
    · have hσ := R.emb_σ_eq_of_active_Dt hσj hs hjA
      refine bid_mono_left ((R.rstar_le_r hne j k).trans (le_of_eq ?_)) _
      rw [r_eq, time_coe, ← R.emb_αs_of_op2_active hσ hop hjA, ← hσ, R.emb_Xv_self]
    · rw [mT_of_inactive (not_lt.1 hjA)]
      by_cases hF : R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ k
      · have hmax := R.rstar_le_max hne hF.1 (WithTop.coe_le_coe.1 hF.2) j
        rw [hσkl, R.emb_Zv_of_inactive hjA] at hmax
        exact (bid_mono_left hmax _).trans (Embed.bid_max_le (R.X.d_nonneg _ _))
      · have hopen : ∃ T, R.WitOK (R.σ k.val) a (pairs (R.pre (R.σ k.val))) T := by
          by_contra h
          exact hF (hstrict h)
        have hDt : R.Dt (R.σ k.val) = R.Dpre (R.σ k.val) := by
          unfold Dt
          rw [R.wit_eq_of_open hop hopen]
          rfl
        rw [hDt] at hjA
        have hlt : R.σ j.val < R.σ k.val :=
          lt_of_le_of_ne hσj fun h ↦ hjA (h ▸ R.active_before j.val)
        rw [R.rstar_coe_of_not hne hF, r_eq, time_coe, R.emb_Xv_of_lt hlt, hDt]
  have hle := R.facility_le_sum hne k (fun j ↦ bid (mT R.P R.X.d (R.θs (R.σ k.val))
    (R.Dt (R.σ k.val)) a.fac (R.Tt (R.σ k.val)) j) (R.X.d j istar)) (fun j ↦ bid_nonneg _ _) h1 h2
  linarith

/-- **[BCFGJPSSV26a, Lemma E.15]**. -/
theorem fr_triangle (j k : R.DgT Dg) (hjk : j < k) :
    R.rstar hne istar k k ≤ R.rstar hne istar j k + R.X.d k.val istar + R.X.d j.val istar := by
  rw [R.rstar_diag hne hD k]
  have hC := R.X.dC_le k.val j.val istar
  have hσ := R.emb_σ_le_of_le hjk.le
  by_cases h : R.Freezing hne istar ∧ (R.kf hne : WithTop (R.DgT Dg)) ≤ k
  · obtain ⟨hF, hk⟩ := h
    have hk' := WithTop.coe_le_coe.1 hk
    obtain ⟨hσk, hα⟩ := R.of_kf_le hne (R.freezing_gt hne hF) hk'
    obtain ⟨a, hop, -⟩ := id hF
    have hs := R.σ_lt (R.kl hne).val
    have hkA := R.emb_active_Dt_of_lt_αs hσk hop hα
    have hZk := R.emb_Zv_of_active (R.σ_le_σkl hne k) hs hkA
    have hm := R.emb_Zv_metric hop hs (R.σ_le_σkl hne k) (R.σ_le_σkl hne j)
    have hZj := R.rstar_ge_Zv hne hF hk' j
    rw [hZk] at hm
    linarith
  · rw [R.rstar_coe_of_not hne h, r_eq, time_coe]
    have := R.emb_Xv_metric (j := k.val) (l := j.val) (s := R.σ k.val) le_rfl hσ
    rw [R.emb_Xv_self] at this
    linarith

end Run

end BCFGJPSSV26.Greedy


