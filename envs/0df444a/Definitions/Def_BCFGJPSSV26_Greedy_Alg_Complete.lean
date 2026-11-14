-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
-- name    : BCFGJPSSV26_Greedy_Alg_Complete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:11.447972+00:00
-- url     : https://prove2.me/theorems/7301a065-f46c-4100-9a72-70c65031e4db
-- title:
--   BCFGJPSSV26.Greedy.Alg.Complete — CompleteSequence and CompleteSolution
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Alg.Complete` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The completion procedures of `Greedy/Alg/Defs.lean` produce valid sequences and solutions
--   ([BCFGJPSSV26a, Observation D.8]), and depend only on the length and the profile of the prefix:
--
--   * **Structure** (no hypotheses): `BCFGJPSSV26.Greedy.Ctx.complete_length`,
--     `BCFGJPSSV26.Greedy.Ctx.complete_take`, `BCFGJPSSV26.Greedy.Ctx.complete_congr` (the completion
--     depends only on the length and profile of the prefix), `BCFGJPSSV26.Greedy.Ctx.complete_idem`,
--     `BCFGJPSSV26.Greedy.Ctx.complete_succ` (completing after the completion of the next sequence
--     changes nothing).
--   * **Validity**: `BCFGJPSSV26.Greedy.Ctx.completeSeq_validSeq` (each added atom passes the exact
--     test with respect to its prefix, and after `L ≥ m + 1` steps nothing passes: an added facility
--     cannot pass again), `BCFGJPSSV26.Greedy.Ctx.complete_sol` (completing an `η`-valid partial
--     solution gives an `η`-valid solution).
--   * **Parameters**: the grid of `f̂` (`BCFGJPSSV26.Greedy.Ctx.fhat_succ_sub_le`), the endpoint
--     `f̂ = 4 n M` opens at most one regular facility (`BCFGJPSSV26.Greedy.Ctx.nRegA_sol_top_le_one`),
--     and the hypotheses hold for the context of a good input (`BCFGJPSSV26.Greedy.hyp_ctx`).
--
--   **Contents.** The module is published as a whole: 65 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.Ctx.completeSeq_validSeq`, `BCFGJPSSV26.Greedy.Ctx.complete_sol`, `BCFGJPSSV26.Greedy.Ctx.sol_sol` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Complete.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Bridge

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Alg.Complete` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# CompleteSequence and CompleteSolution

The completion procedures of `Greedy/Alg/Defs.lean` produce valid sequences and solutions
([BCFGJPSSV26a, Observation D.8]), and depend only on the length and the profile of the prefix:

* **Structure** (no hypotheses): `BCFGJPSSV26.Greedy.Ctx.complete_length`,
  `BCFGJPSSV26.Greedy.Ctx.complete_take`, `BCFGJPSSV26.Greedy.Ctx.complete_congr` (the completion
  depends only on the length and profile of the prefix), `BCFGJPSSV26.Greedy.Ctx.complete_idem`,
  `BCFGJPSSV26.Greedy.Ctx.complete_succ` (completing after the completion of the next sequence
  changes nothing).
* **Validity**: `BCFGJPSSV26.Greedy.Ctx.completeSeq_validSeq` (each added atom passes the exact
  test with respect to its prefix, and after `L ≥ m + 1` steps nothing passes: an added facility
  cannot pass again), `BCFGJPSSV26.Greedy.Ctx.complete_sol` (completing an `η`-valid partial
  solution gives an `η`-valid solution).
* **Parameters**: the grid of `f̂` (`BCFGJPSSV26.Greedy.Ctx.fhat_succ_sub_le`), the endpoint
  `f̂ = 4 n M` opens at most one regular facility (`BCFGJPSSV26.Greedy.Ctx.nRegA_sol_top_le_one`),
  and the hypotheses hold for the context of a good input (`BCFGJPSSV26.Greedy.hyp_ctx`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

variable (C : Ctx)

/-! ### Structure of the completion -/

/-- One step of CompleteSequence either changes nothing or appends a regular atom of a facility
that passes the test. -/
theorem seqStep_cases (b : Bool) (f θ : ℚ) (pre W : List AAtom) :
    (C.firstOpen b f θ (pre ++ W) = none ∧ C.seqStep b f θ pre W = W) ∨
      ∃ i, C.firstOpen b f θ (pre ++ W) = some i ∧ i < C.ip.m ∧
        C.testT b f θ (C.prof (pre ++ W)) i = true ∧ C.seqStep b f θ pre W = W ++ [(i, 0)] := by
  unfold seqStep
  rcases h : C.firstOpen b f θ (pre ++ W) with _ | i
  · exact .inl ⟨rfl, rfl⟩
  · refine .inr ⟨i, rfl, ?_, List.find?_some h, rfl⟩
    exact List.mem_range.1 (List.mem_of_find?_eq_some h)

/-- The iterates of CompleteSequence append regular atoms of facilities `< m`. -/
theorem seqStep_iter (b : Bool) (f θ : ℚ) (pre cur : List AAtom) (k : ℕ) :
    ∃ N, (C.seqStep b f θ pre)^[k] cur = cur ++ N ∧ ∀ a ∈ N, a.2 = 0 ∧ a.1 < C.ip.m := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨N, hN, hN'⟩ := ih
    rw [Function.iterate_succ_apply', hN]
    rcases C.seqStep_cases b f θ pre (cur ++ N) with ⟨-, h⟩ | ⟨i, -, hi, -, h⟩
    · exact ⟨N, h, hN'⟩
    · refine ⟨N ++ [(i, 0)], by rw [h, List.append_assoc], fun a ha ↦ ?_⟩
      rcases List.mem_append.1 ha with ha | ha
      · exact hN' a ha
      · rw [List.mem_singleton.1 ha]
        exact ⟨rfl, hi⟩

theorem completeSeq_prefix (b : Bool) (f θ : ℚ) (pre cur : List AAtom) :
    cur <+: C.completeSeq b f θ pre cur := by
  obtain ⟨N, hN, -⟩ := C.seqStep_iter b f θ pre cur C.ip.L
  exact ⟨N, hN.symm⟩

/-- CompleteSequence adds only regular atoms of facilities `< m`. -/
theorem completeSeq_new (b : Bool) (f θ : ℚ) (pre cur : List AAtom) :
    ∀ a ∈ (C.completeSeq b f θ pre cur).drop cur.length, a.2 = 0 ∧ a.1 < C.ip.m := by
  obtain ⟨N, hN, hN'⟩ := C.seqStep_iter b f θ pre cur C.ip.L
  unfold completeSeq
  rw [hN, List.drop_left]
  exact hN'

/-- One step of CompleteSolution. -/
def cstep (f : ℚ) (H : List (List AAtom)) (p : ℕ) : List (List AAtom) :=
  if H.length = p then H ++ [C.completeSeq (typ1 p) f (C.θseq p) H.flatten []] else H

/-- The first `k` steps of CompleteSolution. -/
def compUpTo (f : ℚ) (H : List (List AAtom)) (k : ℕ) : List (List AAtom) :=
  (List.range k).foldl (C.cstep f) H

theorem complete_eq_compUpTo (f : ℚ) (H : List (List AAtom)) :
    C.complete f H = C.compUpTo f H (2 * C.ip.R) := rfl

theorem compUpTo_succ (f : ℚ) (H : List (List AAtom)) (k : ℕ) :
    C.compUpTo f H (k + 1) = C.cstep f (C.compUpTo f H k) k := by
  simp only [compUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem compUpTo_of_le (f : ℚ) {H : List (List AAtom)} {k : ℕ} (hk : k ≤ H.length) :
    C.compUpTo f H k = H := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [compUpTo_succ, ih (by omega), cstep, if_neg (by omega)]

theorem prefix_compUpTo (f : ℚ) (H : List (List AAtom)) {k k' : ℕ} (hk : k ≤ k') :
    C.compUpTo f H k <+: C.compUpTo f H k' := by
  induction k', hk using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih =>
    refine ih.trans ?_
    rw [compUpTo_succ, cstep]
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

theorem compUpTo_length (f : ℚ) {H : List (List AAtom)} {k : ℕ} (hk : H.length ≤ k) :
    (C.compUpTo f H k).length = k := by
  induction k, hk using Nat.le_induction with
  | base => rw [C.compUpTo_of_le f le_rfl]
  | succ k _ ih =>
    rw [compUpTo_succ, cstep, if_pos ih, List.length_append, ih, List.length_singleton]

theorem compUpTo_succ_of_le (f : ℚ) {H : List (List AAtom)} {p : ℕ} (hp : H.length ≤ p) :
    C.compUpTo f H (p + 1) = C.compUpTo f H p ++
      [C.completeSeq (typ1 p) f (C.θseq p) (C.compUpTo f H p).flatten []] := by
  rw [compUpTo_succ, cstep, if_pos (C.compUpTo_length f hp)]

theorem take_compUpTo (f : ℚ) {H : List (List AAtom)} {p k : ℕ} (hp : H.length ≤ p)
    (hk : p ≤ k) : (C.compUpTo f H k).take p = C.compUpTo f H p := by
  have h := List.prefix_iff_eq_take.1 (C.prefix_compUpTo f H hk)
  rw [C.compUpTo_length f hp] at h
  exact h.symm

theorem prefix_complete (f : ℚ) (H : List (List AAtom)) : H <+: C.complete f H := by
  have h := C.prefix_compUpTo f H (Nat.zero_le (2 * C.ip.R))
  rwa [C.compUpTo_of_le f (Nat.zero_le _)] at h

theorem complete_eq_append (f : ℚ) (H : List (List AAtom)) :
    C.complete f H = H ++ (C.complete f H).drop H.length :=
  (List.prefix_iff_eq_append.1 (C.prefix_complete f H)).symm

theorem complete_length (f : ℚ) {H : List (List AAtom)} (hH : H.length ≤ 2 * C.ip.R) :
    (C.complete f H).length = 2 * C.ip.R :=
  C.compUpTo_length f hH

theorem complete_take (f : ℚ) {H : List (List AAtom)} (_hH : H.length ≤ 2 * C.ip.R) :
    (C.complete f H).take H.length = H :=
  (List.prefix_iff_eq_take.1 (C.prefix_complete f H)).symm

/-- Sequence `p ≥ H.length` of the completion is the completion of sequence `p` after the
completion of the earlier ones. -/
theorem complete_getD (f : ℚ) {H : List (List AAtom)} {p : ℕ} (hp : H.length ≤ p)
    (hp' : p < 2 * C.ip.R) :
    (C.complete f H).getD p [] =
      C.completeSeq (typ1 p) f (C.θseq p) ((C.complete f H).take p).flatten [] := by
  rw [complete_eq_compUpTo, C.take_compUpTo f hp hp'.le]
  have h1 : (C.compUpTo f H (2 * C.ip.R)).take (p + 1) = C.compUpTo f H (p + 1) :=
    C.take_compUpTo f (by omega) hp'
  have h2 : (C.compUpTo f H (2 * C.ip.R))[p]? = (C.compUpTo f H (p + 1))[p]? := by
    rw [← h1, List.getElem?_take_of_lt (by omega)]
  rw [List.getD_eq_getElem?_getD, h2, C.compUpTo_succ_of_le f hp, List.getElem?_append_right
    (by rw [C.compUpTo_length f hp]), C.compUpTo_length f hp, Nat.sub_self]
  rfl

theorem complete_idem (f : ℚ) {H : List (List AAtom)} (hH : H.length = 2 * C.ip.R) :
    C.complete f H = H :=
  C.compUpTo_of_le f hH.ge

/-- Completing after the completion of the next sequence changes nothing. -/
theorem complete_succ (f : ℚ) {H : List (List AAtom)} (hH : H.length < 2 * C.ip.R) :
    C.complete f (H ++ [C.completeSeq (typ1 H.length) f (C.θseq H.length) H.flatten []]) =
      C.complete f H := by
  set H₁ := H ++ [C.completeSeq (typ1 H.length) f (C.θseq H.length) H.flatten []]
  have hH₁ : H₁.length = H.length + 1 := by simp [H₁]
  have key : ∀ k, H.length + 1 ≤ k → C.compUpTo f H₁ k = C.compUpTo f H k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rw [C.compUpTo_of_le f hH₁.ge, C.compUpTo_succ_of_le f le_rfl, C.compUpTo_of_le f le_rfl]
    | succ k _ ih => rw [compUpTo_succ, compUpTo_succ, ih]
  exact key _ hH

theorem firstOpen_congr (b : Bool) (f θ : ℚ) {pre₁ pre₂ : List AAtom}
    (h : C.prof pre₁ = C.prof pre₂) (W : List AAtom) :
    C.firstOpen b f θ (pre₁ ++ W) = C.firstOpen b f θ (pre₂ ++ W) := by
  unfold firstOpen
  rw [prof_append, prof_append, h]

/-- CompleteSequence depends only on the profile of the prefix. -/
theorem completeSeq_congr (b : Bool) (f θ : ℚ) {pre₁ pre₂ : List AAtom}
    (h : C.prof pre₁ = C.prof pre₂) (cur : List AAtom) :
    C.completeSeq b f θ pre₁ cur = C.completeSeq b f θ pre₂ cur := by
  have : C.seqStep b f θ pre₁ = C.seqStep b f θ pre₂ := by
    funext W
    unfold seqStep
    rw [C.firstOpen_congr b f θ h W]
  unfold completeSeq
  rw [this]

theorem compUpTo_congr (f : ℚ) {H₁ H₂ : List (List AAtom)} (hlen : H₁.length = H₂.length)
    (hprof : C.prof H₁.flatten = C.prof H₂.flatten) (k : ℕ) :
    ∃ E, C.compUpTo f H₁ k = H₁ ++ E ∧ C.compUpTo f H₂ k = H₂ ++ E := by
  induction k with
  | zero => exact ⟨[], by simp [compUpTo], by simp [compUpTo]⟩
  | succ k ih =>
    obtain ⟨E, h₁, h₂⟩ := ih
    rw [compUpTo_succ, compUpTo_succ, h₁, h₂]
    unfold cstep
    have hl : (H₁ ++ E).length = (H₂ ++ E).length := by simp [hlen]
    by_cases hk : (H₂ ++ E).length = k
    · rw [if_pos (hl.trans hk), if_pos hk]
      have hp : C.prof (H₁ ++ E).flatten = C.prof (H₂ ++ E).flatten := by
        rw [List.flatten_append, List.flatten_append, prof_append, prof_append, hprof]
      refine ⟨E ++ [C.completeSeq (typ1 k) f (C.θseq k) (H₂ ++ E).flatten []], ?_, by simp⟩
      rw [C.completeSeq_congr _ _ _ hp, List.append_assoc]
    · rw [if_neg (fun h ↦ hk (hl.symm.trans h)), if_neg hk]
      exact ⟨E, rfl, rfl⟩

/-- **The completion depends only on the length and the profile of the prefix.** -/
theorem complete_congr (f : ℚ) {H₁ H₂ : List (List AAtom)} (hlen : H₁.length = H₂.length)
    (hprof : C.prof H₁.flatten = C.prof H₂.flatten) :
    (C.complete f H₁).drop H₁.length = (C.complete f H₂).drop H₂.length := by
  obtain ⟨E, h₁, h₂⟩ := C.compUpTo_congr f hlen hprof (2 * C.ip.R)
  rw [complete_eq_compUpTo, complete_eq_compUpTo, h₁, h₂, List.drop_left, List.drop_left]

theorem nRegA_append (H H' : List (List AAtom)) : nRegA (H ++ H') = nRegA H + nRegA H' := by
  simp [nRegA, List.flatten_append, List.filter_append]

theorem nRegA_singleton (W : List AAtom) : nRegA [W] = nRegSeq W := by
  simp [nRegA, nRegSeq]

/-- Counting form of `BCFGJPSSV26.Greedy.Ctx.complete_congr`: if two sequences after the same
prefix have the same profile, their counts differ by their numbers of regular atoms. -/
theorem cnt_congr (f : ℚ) (pre : List (List AAtom)) {W₁ W₂ : List AAtom}
    (hprof : C.prof (pre.flatten ++ W₁) = C.prof (pre.flatten ++ W₂)) :
    C.cnt f pre W₁ + nRegSeq W₂ = C.cnt f pre W₂ + nRegSeq W₁ := by
  have h := C.complete_congr f (H₁ := pre ++ [W₁]) (H₂ := pre ++ [W₂]) (by simp)
    (by simpa using hprof)
  unfold cnt
  rw [C.complete_eq_append f (pre ++ [W₁]), C.complete_eq_append f (pre ++ [W₂]), h,
    nRegA_append, nRegA_append, nRegA_append, nRegA_append, nRegA_singleton, nRegA_singleton]
  omega

/-- A free copy at offset `K` is invisible. -/
theorem prof_append_top (hd : ∀ j i, 0 ≤ C.dist j i) (hK : C.off (2 ^ C.ip.Pu) = C.ip.K)
    (S : List AAtom) (z : ℕ) : C.prof (S ++ [(z, 2 ^ C.ip.Pu + 1)]) = C.prof S := by
  unfold prof
  refine List.map_congr_left fun j _ ↦ ?_
  rw [List.foldr_append, List.foldr_cons, List.foldr_nil]
  congr 1
  apply min_eq_right
  rw [adist, aoff_free, hK]
  linarith [hd j z]

theorem le_foldr_min_iff (g : AAtom → ℚ) (S : List AAtom) (K x : ℚ) :
    x ≤ S.foldr (fun a acc ↦ min (g a) acc) K ↔ x ≤ K ∧ ∀ a ∈ S, x ≤ g a := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.foldr_cons, le_min_iff, ih, List.mem_cons, forall_eq_or_imp]
    tauto

theorem foldr_min_congr (g : AAtom → ℚ) {S T : List AAtom} (K : ℚ)
    (h₁ : ∀ a ∈ S, ∃ b ∈ T, g b ≤ g a) (h₂ : ∀ b ∈ T, ∃ a ∈ S, g a ≤ g b) :
    S.foldr (fun a acc ↦ min (g a) acc) K = T.foldr (fun a acc ↦ min (g a) acc) K := by
  have hS := (le_foldr_min_iff g S K _).1 le_rfl
  have hT := (le_foldr_min_iff g T K _).1 le_rfl
  refine le_antisymm ((le_foldr_min_iff g T K _).2 ⟨hS.1, fun b hb ↦ ?_⟩)
    ((le_foldr_min_iff g S K _).2 ⟨hT.1, fun a ha ↦ ?_⟩)
  · obtain ⟨a, ha, hab⟩ := h₂ b hb
    exact (hS.2 a ha).trans hab
  · obtain ⟨b, hb, hab⟩ := h₁ a ha
    exact (hT.2 b hb).trans hab

/-- Profiles depend only on the distances of the atoms. -/
theorem prof_congr {S T : List AAtom} (h₁ : ∀ a ∈ S, ∃ b ∈ T, ∀ j, C.adist j b ≤ C.adist j a)
    (h₂ : ∀ b ∈ T, ∃ a ∈ S, ∀ j, C.adist j a ≤ C.adist j b) : C.prof S = C.prof T := by
  unfold prof
  refine List.map_congr_left fun j _ ↦ foldr_min_congr _ _ (fun a ha ↦ ?_) (fun b hb ↦ ?_)
  · obtain ⟨b, hb, h⟩ := h₁ a ha
    exact ⟨b, hb, h j⟩
  · obtain ⟨a, ha, h⟩ := h₂ b hb
    exact ⟨a, ha, h j⟩

/-- A regular facility and a free copy at offset `0` have the same profile, wherever they are. -/
theorem prof_swapFree (X Y : List AAtom) (z : ℕ) :
    C.prof (X ++ (z, 0) :: Y) = C.prof (X ++ Y ++ [(z, 1)]) := by
  have he : ∀ j, C.adist j (z, 1) = C.adist j (z, 0) := by
    intro j
    simp [adist, aoff, off]
  apply prof_congr
  · intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact ⟨a, by simp [ha], fun _ ↦ le_rfl⟩
    · exact ⟨(z, 1), by simp, fun j ↦ (he j).le⟩
    · exact ⟨a, by simp [ha], fun _ ↦ le_rfl⟩
  · intro b hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with (hb | hb) | rfl
    · exact ⟨b, by simp [hb], fun _ ↦ le_rfl⟩
    · exact ⟨b, by simp [hb], fun _ ↦ le_rfl⟩
    · exact ⟨(z, 0), by simp, fun j ↦ (he j).ge⟩

/-- Profiles depend only on the set of atoms. -/
theorem prof_perm {S T : List AAtom} (h : ∀ a, a ∈ S ↔ a ∈ T) : C.prof S = C.prof T :=
  C.prof_congr (fun a ha ↦ ⟨a, (h a).1 ha, fun _ ↦ le_rfl⟩)
    (fun b hb ↦ ⟨b, (h b).2 hb, fun _ ↦ le_rfl⟩)

/-! ### The grids -/

variable {C} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

theorem fhat_zero : C.fhat 0 = C.ip.δ := by
  simp [fhat, hX.fmin_eq]

theorem fmin_le_fmax : C.ip.fmin ≤ C.ip.fmax := by
  rw [hX.fmin_eq, hX.fmax_eq]
  have : C.ip.δ ≤ 1 / 100 := hX.good.δ_le
  have := hX.one_le_M
  have : (2 : ℚ) ≤ C.ip.n := by exact_mod_cast hX.two_le_n
  nlinarith

omit hX in
theorem fhat_top : C.fhat (2 ^ C.ip.Pf) = C.ip.fmax := by
  unfold fhat
  push_cast
  field_simp
  ring

theorem fhat_mono {b b' : ℕ} (h : b ≤ b') : C.fhat b ≤ C.fhat b' := by
  unfold fhat
  have h1 := fmin_le_fmax hX
  have h2 : (b : ℚ) ≤ b' := by exact_mod_cast h
  have h3 : (0 : ℚ) < 2 ^ C.ip.Pf := by positivity
  have : (C.ip.fmax - C.ip.fmin) * b / 2 ^ C.ip.Pf ≤ (C.ip.fmax - C.ip.fmin) * b' / 2 ^ C.ip.Pf :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by linarith)) h3.le
  linarith

theorem fhat_le_fmax {b : ℕ} (h : b ≤ 2 ^ C.ip.Pf) : C.fhat b ≤ C.ip.fmax :=
  (fhat_top (C := C)) ▸ fhat_mono hX h

theorem fhat_succ_sub_le (b : ℕ) : C.fhat (b + 1) - C.fhat b ≤ C.ip.η := by
  have h : C.fhat (b + 1) - C.fhat b = (C.ip.fmax - C.ip.fmin) / 2 ^ C.ip.Pf := by
    unfold fhat
    push_cast
    ring
  rw [h]
  exact hX.fstep

omit hX in
theorem off_top : C.off (2 ^ C.ip.Pu) = C.ip.K := by
  unfold off
  push_cast
  field_simp

theorem off_succ_sub_le (g : ℕ) : C.off (g + 1) - C.off g ≤ C.ip.η := by
  have h : C.off (g + 1) - C.off g = C.ip.K / 2 ^ C.ip.Pu := by
    unfold off
    push_cast
    ring
  rw [h]
  exact hX.ustep

/-- The opening costs of the grid are above `n η`. -/
theorem nη_lt_fhat (b : ℕ) : (C.ip.n : ℚ) * C.ip.η < C.fhat b := by
  have h1 : (C.ip.n : ℚ) * C.ip.η < C.ip.δ := hX.good.nη_lt_δ
  have h2 : C.ip.fmin ≤ C.fhat b := by
    have := fhat_mono hX (Nat.zero_le b)
    rwa [show C.fhat 0 = C.ip.fmin by simp [fhat]] at this
  rw [hX.fmin_eq] at h2
  linarith

/-! ### Validity of the completion -/

theorem Hyp.f_pos {f : ℚ} (hf : C.ip.n * C.ip.η < f) : 0 < f := by
  have h1 : (0 : ℚ) ≤ C.ip.n * C.ip.η := mul_nonneg (Nat.cast_nonneg _) hX.good.η_nonneg
  linarith

omit hX in
theorem atomOK_reg {i : ℕ} (hi : i < C.ip.m) : C.AtomOK (i, 0) := ⟨hi, Nat.zero_le _⟩

/-- A facility open as a regular atom does not pass the test again. -/
theorem testT_false_of_mem (b : Bool) {f : ℚ} (hf : 0 < f) (θ : ℚ) {S : List AAtom}
    (hS : ∀ a ∈ S, C.AtomOK a) {i : ℕ} (hi : (i, 0) ∈ S) :
    C.testT b f θ (C.prof S) i = false := by
  have him : i < C.ip.m := (hS _ hi).1
  have hD : ∀ j : Fin C.ip.n, (C.prof S).getD j 0 = profL C.par.K X.d (decS hX S) j :=
    prof_getD hX hS
  have hle : ∀ j, profL C.par.K X.d (decS hX S) j ≤ X.d j ⟨i, him⟩ := by
    intro j
    have hmem : (⟨i, him⟩, (0 : ℚ)) ∈ pairs (decS hX S) := by
      simp only [pairs, decS, List.map_map, List.mem_toFinset, List.mem_map]
      refine ⟨(i, 0), hi, ?_⟩
      rw [Function.comp_apply, decA_pair hX (a := (i, 0)) him]
      simp [aoff]
    have := profF_le C.par.K X.d hmem j
    simpa [profL] using this
  have h : C.testT b f θ (C.prof S) i =
      Greedy.testT C.par X.d b f θ (profL C.par.K X.d (decS hX S)) ⟨i, him⟩ :=
    testT_eq hX b f θ hD (prof_length _) ⟨i, him⟩
  rw [h]
  have hd : ∀ j, 0 ≤ X.d j ⟨i, him⟩ := fun j ↦ X.d_nonneg j _
  cases b
  · simp only [Greedy.testT, Bool.cond_false, Greedy.test2, decide_eq_false_iff_not]
    rintro ⟨-, h3, -⟩
    rw [lhs3_eq_zero hX.good hd hle] at h3
    linarith
  · simp only [Greedy.testT, Bool.cond_true, Greedy.test1, decide_eq_false_iff_not, not_le]
    rw [lhs1_eq_zero hX.good hd hle]
    exact hf

section Iter

variable {b : Bool} {f θ : ℚ} {pre cur : List AAtom}

omit hX in
theorem seqStep_iter_ok (hok : ∀ a ∈ pre ++ cur, C.AtomOK a) (k : ℕ) :
    ∀ a ∈ pre ++ (C.seqStep b f θ pre)^[k] cur, C.AtomOK a := by
  obtain ⟨N, hN, hN'⟩ := C.seqStep_iter b f θ pre cur k
  intro a ha
  rw [hN, ← List.append_assoc] at ha
  rcases List.mem_append.1 ha with ha | ha
  · exact hok a ha
  · obtain ⟨h1, h2⟩ := hN' a ha
    exact ⟨h2, by rw [h1]; exact Nat.zero_le _⟩

omit hX in
theorem completeSeq_ok (hok : ∀ a ∈ pre ++ cur, C.AtomOK a) :
    ∀ a ∈ pre ++ C.completeSeq b f θ pre cur, C.AtomOK a :=
  C.seqStep_iter_ok hok C.ip.L

/-- The new atoms of the iterates of CompleteSequence are distinct facilities. -/
theorem seqStep_iter_nodup (hf : 0 < f) (hok : ∀ a ∈ pre ++ cur, C.AtomOK a) (k : ℕ) :
    ∃ N, (C.seqStep b f θ pre)^[k] cur = cur ++ N ∧ (∀ a ∈ N, a.2 = 0 ∧ a.1 < C.ip.m) ∧
      (N.map Prod.fst).Nodup := by
  induction k with
  | zero => exact ⟨[], by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨N, hN, hN', hnd⟩ := ih
    have hokN := C.seqStep_iter_ok (b := b) (f := f) (θ := θ) hok k
    rw [Function.iterate_succ_apply', hN]
    rw [hN] at hokN
    rcases C.seqStep_cases b f θ pre (cur ++ N) with ⟨-, h⟩ | ⟨i, -, hi, ht, h⟩
    · exact ⟨N, h, hN', hnd⟩
    · have hnot : (i, 0) ∉ pre ++ (cur ++ N) := fun hmem ↦ by
        rw [testT_false_of_mem hX b hf θ hokN hmem] at ht
        exact Bool.false_ne_true ht
      have hiN : i ∉ N.map Prod.fst := by
        intro hmem
        obtain ⟨a, ha, hai⟩ := List.mem_map.1 hmem
        have hia : (i, 0) = a := Prod.ext hai.symm (hN' a ha).1.symm
        exact hnot (List.mem_append_right _ (List.mem_append_right _ (hia ▸ ha)))
      refine ⟨N ++ [(i, 0)], by rw [h, List.append_assoc], fun a ha ↦ ?_, ?_⟩
      · rcases List.mem_append.1 ha with ha | ha
        · exact hN' a ha
        · rw [List.mem_singleton.1 ha]
          exact ⟨rfl, hi⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, fun x hx y hy hxy ↦ ?_⟩
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
        exact hiN (hy ▸ hxy ▸ hx)

omit hX in
theorem length_le_of_nodup {N : List AAtom} (hN : ∀ a ∈ N, a.1 < C.ip.m)
    (hnd : (N.map Prod.fst).Nodup) : N.length ≤ C.ip.m := by
  have h1 : (N.map Prod.fst).toFinset ⊆ Finset.range C.ip.m := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact Finset.mem_range.2 (hN a ha)
  have h2 := Finset.card_le_card h1
  rwa [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_range] at h2

omit hX in
theorem seqStep_iter_none_or_length (k : ℕ) :
    C.firstOpen b f θ (pre ++ (C.seqStep b f θ pre)^[k] cur) = none ∨
      ((C.seqStep b f θ pre)^[k] cur).length = cur.length + k := by
  induction k with
  | zero => exact .inr rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases C.seqStep_cases b f θ pre ((C.seqStep b f θ pre)^[k] cur) with
      ⟨h0, h⟩ | ⟨i, h0, -, -, h⟩
    · left
      rw [h]
      exact h0
    · right
      rcases ih with ih | ih
      · rw [ih] at h0
        exact absurd h0 (by simp)
      · rw [h, List.length_append, ih, List.length_singleton]
        omega

/-- After `L ≥ m + 1` steps, no facility passes the test. -/
theorem firstOpen_completeSeq (hf : 0 < f) (hok : ∀ a ∈ pre ++ cur, C.AtomOK a) :
    C.firstOpen b f θ (pre ++ C.completeSeq b f θ pre cur) = none := by
  rcases C.seqStep_iter_none_or_length (b := b) (f := f) (θ := θ) (pre := pre) (cur := cur)
    C.ip.L with h | h
  · exact h
  · exfalso
    obtain ⟨N, hN, hN', hnd⟩ := seqStep_iter_nodup hX (b := b) (θ := θ) hf hok C.ip.L
    have h1 := length_le_of_nodup (fun a ha ↦ (hN' a ha).2) hnd
    rw [hN, List.length_append] at h
    have := hX.L_ge
    omega

end Iter

omit hX in
theorem compUpTo_atoms (f : ℚ) (H : List (List AAtom)) (k : ℕ) :
    ∀ a ∈ (C.compUpTo f H k).flatten, a ∈ H.flatten ∨ (a.2 = 0 ∧ a.1 < C.ip.m) := by
  induction k with
  | zero => exact fun a ha ↦ .inl ha
  | succ k ih =>
    rw [compUpTo_succ, cstep]
    split_ifs
    · intro a ha
      rw [List.flatten_append, List.mem_append] at ha
      rcases ha with ha | ha
      · exact ih a ha
      · right
        have := C.completeSeq_new (typ1 k) f (C.θseq k) (C.compUpTo f H k).flatten [] a
        simp only [List.length_nil, List.drop_zero] at this
        exact this (by simpa using ha)
    · exact ih

omit hX in
/-- The atoms of a completion are those of the partial solution and regular atoms in range. -/
theorem complete_atoms (f : ℚ) (H : List (List AAtom)) :
    ∀ a ∈ (C.complete f H).flatten, a ∈ H.flatten ∨ (a.2 = 0 ∧ a.1 < C.ip.m) :=
  C.compUpTo_atoms f H _

omit hX in
theorem complete_solOK (f : ℚ) {H : List (List AAtom)} (hok : C.SolOK H) :
    C.SolOK (C.complete f H) := fun a ha ↦
  (C.complete_atoms f H a ha).elim (hok a) fun h ↦ ⟨h.2, by rw [h.1]; exact Nat.zero_le _⟩

omit hX in
theorem mem_flatten_of_mem_getD {H : List (List AAtom)} {q : ℕ} {a : AAtom}
    (ha : a ∈ H.getD q []) : a ∈ H.flatten := by
  rw [List.getD_eq_getElem?_getD] at ha
  rcases h : H[q]? with _ | S
  · simp [h] at ha
  · rw [h, Option.getD_some] at ha
    exact List.mem_flatten.2 ⟨S, List.mem_of_getElem? h, ha⟩

/-- A solution with at least one client has at least one atom; one without free atoms has a
regular atom. -/
theorem one_le_nRegA_of_sol {f η : ℚ} {H : List (List AAtom)}
    (hH : Sol C.par X.d f η (decH hX H)) (hfree : ∀ a ∈ H.flatten, a.2 = 0) : 1 ≤ nRegA H := by
  have hn : 0 < C.ip.n := by have := hX.two_le_n; omega
  have hlt := Sol.profL_lt_K hX.good hH ⟨0, hn⟩
  unfold nRegA
  rw [List.filter_eq_self.2 fun a ha ↦ by simp [hfree a ha]]
  rcases hflat : H.flatten with _ | ⟨a, l⟩
  · rw [decH_flatten, hflat] at hlt
    simp [profL, pairs, decS, profF_empty] at hlt
  · simp

omit hX in
theorem bid_le_max (x : ℚ) {y : ℚ} (hy : 0 ≤ y) : bid x y ≤ max x 0 :=
  max_le_max (by nlinarith [one_le_γ]) le_rfl

/-- At `f̂ = 4 n M`, no facility passes the test after a regular atom. -/
theorem testT_false_top (b : Bool) (θ : ℚ) {S : List AAtom} (hS : ∀ a ∈ S, C.AtomOK a)
    {i₁ : ℕ} (hi₁ : (i₁, 0) ∈ S) {i : ℕ} (hi : i < C.ip.m) :
    C.testT b C.ip.fmax θ (C.prof S) i = false := by
  have hi₁m : i₁ < C.ip.m := (hS _ hi₁).1
  have hD : ∀ j : Fin C.ip.n, (C.prof S).getD j 0 = profL C.par.K X.d (decS hX S) j :=
    prof_getD hX hS
  have hδ : 0 < C.ip.δ := hX.good.δ_pos
  have hδ' : C.ip.δ ≤ 1 / 100 := hX.good.δ_le
  have hM := hX.one_le_M
  have hle : ∀ j, (1 - C.par.δ) * profL C.par.K X.d (decS hX S) j ≤ (1 - C.par.δ) * C.ip.M := by
    intro j
    have hmem : (⟨i₁, hi₁m⟩, (0 : ℚ)) ∈ pairs (decS hX S) := by
      simp only [pairs, decS, List.map_map, List.mem_toFinset, List.mem_map]
      refine ⟨(i₁, 0), hi₁, ?_⟩
      rw [Function.comp_apply, decA_pair hX (a := (i₁, 0)) hi₁m]
      simp [aoff]
    have h1 := profF_le C.par.K X.d hmem j
    have h2 := hX.dM j ⟨i₁, hi₁m⟩
    have h3 : profL C.par.K X.d (decS hX S) j ≤ C.ip.M := by simp only [profL]; linarith
    exact mul_le_mul_of_nonneg_left h3 (by change 0 ≤ 1 - C.ip.δ; linarith)
  have hsum : ∀ g : Fin C.ip.n → ℚ, (∀ j, g j ≤ (1 - C.par.δ) * C.ip.M) →
      ∑ j, g j < C.ip.fmax := by
    intro g hg
    have h1 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hg j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    rw [hX.fmax_eq]
    have hn : (2 : ℚ) ≤ C.ip.n := by exact_mod_cast hX.two_le_n
    have : (C.ip.n : ℚ) * ((1 - C.par.δ) * C.ip.M) < 4 * C.ip.n * C.ip.M := by
      change (C.ip.n : ℚ) * ((1 - C.ip.δ) * C.ip.M) < 4 * C.ip.n * C.ip.M
      have hnM : 0 < (C.ip.n : ℚ) * C.ip.M := mul_pos (by linarith) (by linarith)
      nlinarith [mul_pos hnM (by linarith : (0 : ℚ) < 3 + C.ip.δ)]
    linarith
  have hnn : 0 ≤ (1 - C.par.δ) * C.ip.M := by
    change 0 ≤ (1 - C.ip.δ) * C.ip.M
    nlinarith
  have h : C.testT b C.ip.fmax θ (C.prof S) i =
      Greedy.testT C.par X.d b C.ip.fmax θ (profL C.par.K X.d (decS hX S)) ⟨i, hi⟩ :=
    testT_eq hX b _ θ hD (prof_length _) ⟨i, hi⟩
  rw [h]
  cases b
  · simp only [Greedy.testT, Bool.cond_false, Greedy.test2, decide_eq_false_iff_not]
    rintro ⟨-, h3, -⟩
    refine absurd h3 (not_le.2 (hsum _ fun j ↦ ?_))
    refine (bid_le_max _ ?_).trans (max_le ((mT_le_D _ _ _ _ _).trans (hle j)) hnn)
    have := X.d_nonneg j ⟨i, hi⟩
    change 0 ≤ (1 - C.ip.δ / 2) * X.d j ⟨i, hi⟩
    nlinarith
  · simp only [Greedy.testT, Bool.cond_true, Greedy.test1, decide_eq_false_iff_not, not_le]
    refine hsum _ fun j ↦ ?_
    refine (bid_le_max _ ?_).trans (max_le ((min_le_right _ _).trans (hle j)) hnn)
    have := X.d_nonneg j ⟨i, hi⟩
    change 0 ≤ (1 - C.ip.δ) * X.d j ⟨i, hi⟩
    nlinarith

theorem completeSeq_top_nil (b : Bool) (θ : ℚ) {pre : List AAtom}
    (hpre : ∀ a ∈ pre, C.AtomOK a) {i₁ : ℕ} (hi₁ : (i₁, 0) ∈ pre) :
    C.completeSeq b C.ip.fmax θ pre [] = [] := by
  unfold completeSeq
  apply Function.iterate_fixed
  rcases C.seqStep_cases b C.ip.fmax θ pre [] with ⟨-, h⟩ | ⟨i, -, hi, ht, -⟩
  · exact h
  · rw [List.append_nil, testT_false_top hX b θ hpre hi₁ hi] at ht
    exact absurd ht Bool.false_ne_true

theorem completeSeq_top_length (b : Bool) (θ : ℚ) :
    (C.completeSeq b C.ip.fmax θ [] []).length ≤ 1 := by
  unfold completeSeq
  rcases C.seqStep_cases b C.ip.fmax θ [] [] with ⟨-, h⟩ | ⟨i, -, hi, -, h⟩
  · rw [Function.iterate_fixed h]
    simp
  · have hL : C.ip.L = (C.ip.L - 1) + 1 := by have := hX.L_ge; omega
    have hfix : C.seqStep b C.ip.fmax θ [] [(i, 0)] = [(i, 0)] := by
      rcases C.seqStep_cases b C.ip.fmax θ [] [(i, 0)] with ⟨-, h'⟩ | ⟨i', -, hi', ht, -⟩
      · exact h'
      · rw [testT_false_top hX b θ (S := [] ++ [(i, 0)]) (by simp [AtomOK, hi]) (i₁ := i)
          (by simp) hi']
          at ht
        exact absurd ht Bool.false_ne_true
    rw [hL, Function.iterate_succ_apply, h, List.nil_append, Function.iterate_fixed hfix]
    simp

/-- **At `f̂ = 4 n M` at most one regular facility opens**: after one, every client pays at most
`(1 - δ) d(j, S) ≤ M`, so nothing else can be paid for. -/
theorem nRegA_sol_top_le_one : nRegA (C.sol (2 ^ C.ip.Pf)) ≤ 1 := by
  have key : ∀ k, ((C.compUpTo C.ip.fmax [] k).flatten).length ≤ 1 := by
    intro k
    induction k with
    | zero => simp [compUpTo]
    | succ k ih =>
      rw [compUpTo_succ, cstep]
      split_ifs
      · rw [List.flatten_append, List.length_append]
        rcases hfl : (C.compUpTo C.ip.fmax [] k).flatten with _ | ⟨a, l⟩
        · simpa using completeSeq_top_length hX _ _
        · have ha := C.compUpTo_atoms C.ip.fmax [] k a (by rw [hfl]; simp)
          have ha' : a.2 = 0 ∧ a.1 < C.ip.m := ha.resolve_left (by simp)
          have hl : l = [] := by
            rw [hfl] at ih
            simpa using ih
          subst hl
          have hok : ∀ y ∈ [a], C.AtomOK y := by
            intro y hy
            rw [List.mem_singleton.1 hy]
            exact ⟨ha'.2, by rw [ha'.1]; exact Nat.zero_le _⟩
          have hmem : (a.1, 0) ∈ [a] := by
            rw [List.mem_singleton]
            exact Prod.ext rfl ha'.1.symm
          rw [completeSeq_top_nil hX _ _ hok hmem]
          simp
      · exact ih
  unfold sol
  rw [fhat_top]
  exact (List.length_filter_le _ _).trans (key _)

end Ctx

/-- The hypotheses of a core input: the table holds the distances of the space `X`, which lie
in `[1, M]`; `2 ≤ n` and `1 ≤ k < min (n, m)`. -/
structure CoreOK (c : Consts) (x : CoreIn) (X : Space x.1 x.2.1) : Prop where
  dist_eq : ∀ (j : Fin x.1) (i : Fin x.2.1), (x.2.2.2.getD j []).getD i 0 = X.d j i
  dist_nonneg : ∀ j i : ℕ, 0 ≤ (x.2.2.2.getD j []).getD i 0
  d1 : ∀ j i, 1 ≤ X.d j i
  dM : ∀ j i, X.d j i ≤ Mof c x.1
  two_le_n : 2 ≤ x.1
  one_le_k : 1 ≤ x.2.2.1
  k_lt_n : x.2.2.1 < x.1
  k_lt_m : x.2.2.1 < x.2.1

/-- A grid with `2^⌈log₂ ⌈A / η⌉⌉` steps over a length `A` has steps at most `η`. -/
theorem hyp_ctx_step_le {A η : ℚ} (hη : 0 < η) :
    A / 2 ^ Nat.clog 2 ⌈A / η⌉₊ ≤ η := by
  have h1 : A / η ≤ ⌈A / η⌉₊ := Nat.le_ceil _
  have h2 : (⌈A / η⌉₊ : ℚ) ≤ 2 ^ Nat.clog 2 ⌈A / η⌉₊ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  rw [div_le_iff₀ (by positivity)]
  have h3 : η * (A / η) = A := mul_div_cancel₀ _ hη.ne'
  nlinarith

/-- Bernoulli: `(1 + ε²)^(⌈1/ε²⌉ a) ≥ 2^a`. -/
theorem hyp_ctx_bernoulli {ε : ℚ} (hε : 0 < ε) (a : ℕ) :
    (2 : ℚ) ^ a ≤ (1 + ε ^ 2) ^ (⌈1 / ε ^ 2⌉₊ * a) := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have h1 : (1 : ℚ) / ε ^ 2 ≤ ⌈1 / ε ^ 2⌉₊ := Nat.le_ceil _
  have h2 : (2 : ℚ) ≤ (1 + ε ^ 2) ^ ⌈1 / ε ^ 2⌉₊ := by
    have h3 := one_add_mul_le_pow (a := ε ^ 2) (by linarith) ⌈1 / ε ^ 2⌉₊
    have h4 : 1 ≤ (⌈1 / ε ^ 2⌉₊ : ℚ) * ε ^ 2 := by
      rw [div_le_iff₀ hε2] at h1
      linarith
    linarith
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) h2 a

/-- **The hypotheses hold for the context of a good input** (the parameter arithmetic:
`θ (R - 1) ≥ 2^⌈log₂ ⌈5 n M⌉⌉ ≥ 5 n M ≥ 4 n M + γ M` by Bernoulli's inequality, the grid steps
by the choice of `Pf` and `Pu`). -/
theorem hyp_ctx {c : Consts} (hc : c.Good) {x : CoreIn} {X : Space x.1 x.2.1}
    (hx : CoreOK c x X) : (ctx c x).Hyp X := by
  have hn : (2 : ℚ) ≤ x.1 := by exact_mod_cast hx.two_le_n
  have hδ := hc.δ_pos
  have hδ' := hc.δ_le
  have hε : c.εg = c.δ / 10 := hc.εg_eq
  have hεpos : 0 < c.εg := by rw [hε]; positivity
  have hM1 : 1 ≤ Mof c x.1 := by
    unfold Mof
    have := hc.εp_pos
    have : 0 ≤ 8 * (x.1 : ℚ) ^ 2 / c.εp := by positivity
    linarith
  have hη : 0 < c.δ ^ 2 / (100 * (x.1 : ℚ) ^ 2) := by positivity
  have hθ : ∀ r, 0 < (1 + c.εg ^ 2) ^ r := fun r ↦ by positivity
  refine
    { dist_eq := hx.dist_eq
      dist_nonneg := hx.dist_nonneg
      d1 := hx.d1
      dM := hx.dM
      two_le_n := hx.two_le_n
      one_le_k := hx.one_le_k
      k_lt_n := hx.k_lt_n
      k_lt_m := hx.k_lt_m
      good := ?_
      one_le_M := hM1
      η_eq := rfl
      fmin_eq := rfl
      fmax_eq := rfl
      one_le_R := Nat.le_add_left 1 _
      θ_last := ?_
      K_eq := rfl
      fstep := ?_
      ustep := ?_
      L_ge := le_rfl }
  · refine ⟨hδ, hδ', hεpos, hε.le, hη.le, ?_, le_rfl⟩
    change (x.1 : ℚ) * (c.δ ^ 2 / (100 * (x.1 : ℚ) ^ 2)) ≤ c.δ * c.εg / 10
    have e : (x.1 : ℚ) * (c.δ ^ 2 / (100 * (x.1 : ℚ) ^ 2)) = c.δ ^ 2 / (100 * x.1) := by
      field_simp
    rw [e, hε, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg c.δ]
  · change 4 * (x.1 : ℚ) * Mof c x.1 + γ * Mof c x.1 ≤ (1 + c.εg ^ 2) ^ (Rof c x.1 - 1)
    have hR : Rof c x.1 - 1 = ⌈1 / c.εg ^ 2⌉₊ * Nat.clog 2 ⌈5 * (x.1 : ℚ) * Mof c x.1⌉₊ := by
      simp [Rof]
    rw [hR]
    refine le_trans ?_ (hyp_ctx_bernoulli hεpos _)
    have h1 : 5 * (x.1 : ℚ) * Mof c x.1 ≤ ⌈5 * (x.1 : ℚ) * Mof c x.1⌉₊ := Nat.le_ceil _
    have h2 : (⌈5 * (x.1 : ℚ) * Mof c x.1⌉₊ : ℚ) ≤
        2 ^ Nat.clog 2 ⌈5 * (x.1 : ℚ) * Mof c x.1⌉₊ := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    have h3 : γ * Mof c x.1 ≤ x.1 * Mof c x.1 :=
      mul_le_mul_of_nonneg_right (by norm_num [γ]; linarith) (by linarith)
    linarith
  · change (4 * (x.1 : ℚ) * Mof c x.1 - c.δ) / 2 ^ Nat.clog 2
      ⌈4 * (x.1 : ℚ) * Mof c x.1 / (c.δ ^ 2 / (100 * (x.1 : ℚ) ^ 2))⌉₊ ≤
        c.δ ^ 2 / (100 * (x.1 : ℚ) ^ 2)
    refine le_trans ?_ (hyp_ctx_step_le (A := 4 * (x.1 : ℚ) * Mof c x.1) hη)
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · exact hyp_ctx_step_le hη

end BCFGJPSSV26.Greedy


