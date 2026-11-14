-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Alg_Merge
-- name    : BCFGJPSSV26_Greedy_Alg_Merge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:00:41.147041+00:00
-- url     : https://prove2.me/theorems/3c73a246-20e8-46b7-a830-91780e9aa290
-- title:
--   BCFGJPSSV26.Greedy.Alg.Merge — Correctness of the merge
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Alg.Merge` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Appendix D] and [CGLSS25, Section 3.5], for the procedure of `Greedy/Alg/Defs.lean`:
--   the merge ends with an `η`-valid solution with exactly `k` regular atoms and at most three free
--   atoms per sequence, or with the solution at the smallest opening cost if that one has at most `k`
--   (`BCFGJPSSV26.Greedy.Ctx.merge_spec`).
--
--   * **The promise** (`BCFGJPSSV26.Greedy.Ctx.Promise`) before phase `p`: two `η`-valid solutions
--     `H, H'` whose numbers of regular atoms sandwich `k`, determined by their first `p` sequences
--     (each later sequence is the completion of the earlier ones), whose first `p` sequences agree
--     except for the parameters: either `H` has the next larger opening cost (`f̂ - f̂' ≤ η`), or the
--     same opening cost and one free atom at an offset `η` smaller. `H` is the dominant one.
--   * **Bisection** gives the promise before phase `0` (`BCFGJPSSV26.Greedy.Ctx.bisect_spec`); each
--     phase keeps it for the next phase or ends (`BCFGJPSSV26.Greedy.Ctx.phase_spec`); and it cannot
--     hold after the last phase, since two solutions that agree except for an offset have the same
--     number of regular atoms (`BCFGJPSSV26.Greedy.Ctx.not_promise_end`).
--   * The steps of a phase: step A (`BCFGJPSSV26.Greedy.Ctx.stepA_spec`, [BCFGJPSSV26a,
--     Claim D.12]), the walk of step B with its dispatch
--     (`BCFGJPSSV26.Greedy.Ctx.walkPhase_spec`), step C (`BCFGJPSSV26.Greedy.Ctx.stepC_spec`), and the
--     offset search (`BCFGJPSSV26.Greedy.Ctx.binSearch_spec`). The counts change by exactly one when a
--     regular atom becomes a free copy at offset `0` (`BCFGJPSSV26.Greedy.Ctx.cnt_swapFree`), which is
--     why step C and the walk also test the count `k` after such a change, and not at all when a free
--     copy is at offset `K` (`BCFGJPSSV26.Greedy.Ctx.cnt_append_top`).
--
--   Generic lemmas (searches, flips, validity of the atoms of a list) are in
--   `Greedy/Alg/MergeAux.lean`, the invariants of the walk of step B in `Greedy/Alg/MergeWalk.lean`
--   (namespace `BCFGJPSSV26.Greedy.Ctx.MergeH`).
--
--   **Contents.** The module is published as a whole: 14 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.Ctx.merge_spec` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Merge`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Merge.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Alg.Merge` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Correctness of the merge

[BCFGJPSSV26a, Appendix D] and [CGLSS25, Section 3.5], for the procedure of `Greedy/Alg/Defs.lean`:
the merge ends with an `η`-valid solution with exactly `k` regular atoms and at most three free
atoms per sequence, or with the solution at the smallest opening cost if that one has at most `k`
(`BCFGJPSSV26.Greedy.Ctx.merge_spec`).

* **The promise** (`BCFGJPSSV26.Greedy.Ctx.Promise`) before phase `p`: two `η`-valid solutions
  `H, H'` whose numbers of regular atoms sandwich `k`, determined by their first `p` sequences
  (each later sequence is the completion of the earlier ones), whose first `p` sequences agree
  except for the parameters: either `H` has the next larger opening cost (`f̂ - f̂' ≤ η`), or the
  same opening cost and one free atom at an offset `η` smaller. `H` is the dominant one.
* **Bisection** gives the promise before phase `0` (`BCFGJPSSV26.Greedy.Ctx.bisect_spec`); each
  phase keeps it for the next phase or ends (`BCFGJPSSV26.Greedy.Ctx.phase_spec`); and it cannot
  hold after the last phase, since two solutions that agree except for an offset have the same
  number of regular atoms (`BCFGJPSSV26.Greedy.Ctx.not_promise_end`).
* The steps of a phase: step A (`BCFGJPSSV26.Greedy.Ctx.stepA_spec`, [BCFGJPSSV26a,
  Claim D.12]), the walk of step B with its dispatch
  (`BCFGJPSSV26.Greedy.Ctx.walkPhase_spec`), step C (`BCFGJPSSV26.Greedy.Ctx.stepC_spec`), and the
  offset search (`BCFGJPSSV26.Greedy.Ctx.binSearch_spec`). The counts change by exactly one when a
  regular atom becomes a free copy at offset `0` (`BCFGJPSSV26.Greedy.Ctx.cnt_swapFree`), which is
  why step C and the walk also test the count `k` after such a change, and not at all when a free
  copy is at offset `K` (`BCFGJPSSV26.Greedy.Ctx.cnt_append_top`).

Generic lemmas (searches, flips, validity of the atoms of a list) are in
`Greedy/Alg/MergeAux.lean`, the invariants of the walk of step B in `Greedy/Alg/MergeWalk.lean`
(namespace `BCFGJPSSV26.Greedy.Ctx.MergeH`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

/-! ### Searches -/

/-- **Binary search**: on counts `c` with `c 0` and `c (2^P)` on both sides of `k`, after `P`
steps either a point with count `k` is found or two adjacent points sandwich `k`. -/
theorem searchStep_spec {k : ℕ} {c : ℕ → ℕ} {P : ℕ} (hs : sandwich (c 0) (c (2 ^ P)) k = true) :
    (∃ lo, (searchStep k c)^[P] (0, 2 ^ P, none) = (lo, lo + 1, none) ∧ lo + 1 ≤ 2 ^ P ∧
      sandwich (c lo) (c (lo + 1)) k = true ∧ (decide (c lo < k) = decide (c 0 < k))) ∨
    (∃ lo hi g, (searchStep k c)^[P] (0, 2 ^ P, none) = (lo, hi, some g) ∧ c g = k ∧
      g ≤ 2 ^ P) := by
  have hs' : sandwich (c 0) (c (0 + 2 ^ P)) k = true := by rwa [Nat.zero_add]
  rcases MergeH.searchStep_iter P 0 hs' with ⟨lo, h1, -, h3, h4, h5⟩ |
    ⟨lo, hi, g, h1, h2, -, h4⟩
  · rw [Nat.zero_add] at h1 h3
    exact .inl ⟨lo, h1, h3, h4, h5⟩
  · rw [Nat.zero_add] at h1 h4
    exact .inr ⟨lo, hi, g, h1, h2, h4⟩

/-- The first flip, when it exists, is a flip. -/
theorem firstFlip_some {k : ℕ} {cs : List ℕ} {t : ℕ} (h : firstFlip k cs = some t) :
    t + 1 < cs.length ∧ sandwich (cs.getD t 0) (cs.getD (t + 1) 0) k = true :=
  MergeH.firstFlip_some' h

/-- **A flip exists** between the endpoints of a list of counts that sandwich `k`, none of them
equal to `k`. (Without the last hypothesis it fails: `[k - 1, k, k + 1]` has no flip.) -/
theorem firstFlip_isSome {k : ℕ} {cs : List ℕ} {a b : ℕ} (ha : cs.head? = some a)
    (hb : cs.getLast? = some b) (hs : sandwich a b k = true) (hk : ∀ x ∈ cs, x ≠ k) :
    (firstFlip k cs).isSome := by
  cases h : firstFlip k cs with
  | some t => rfl
  | none =>
    exfalso
    have hne : cs ≠ [] := by
      rintro rfl
      simp at ha
    have hlen : 0 < cs.length := List.length_pos_of_ne_nil hne
    have h1 := MergeH.firstFlip_none' h hk (cs.length - 1) (by omega)
    have ha' : cs.getD 0 0 = a := by
      rw [List.head?_eq_getElem?] at ha
      simp [List.getD_eq_getElem?_getD, ha]
    have hb' : cs.getD (cs.length - 1) 0 = b := by
      rw [List.getLast?_eq_getElem?] at hb
      simp [List.getD_eq_getElem?_getD, hb]
    rw [ha', hb', decide_eq_decide] at h1
    have hak : a ≠ k := hk a (List.mem_of_mem_head? ha)
    have hbk : b ≠ k := hk b (List.mem_of_getLast? hb)
    rw [MergeH.sandwich_iff] at hs
    rcases hs with hs | hs
    · exact absurd (h1.2 hs.1) (by omega)
    · exact absurd (h1.1 hs.1) (by omega)

variable {C : Ctx} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

/-! ### Good outputs and the promise -/

/-- A **good output**: an `η`-valid solution at `f̂ b` with atoms in range and at most three free
atoms per sequence, with exactly `k` regular atoms, or with at most `k` at `b = 0` and no free
atoms, and at least one regular atom. -/
def GoodOut (H : List (List AAtom)) (b : ℕ) : Prop :=
  Sol C.par X.d (C.fhat b) C.ip.η (decH hX H) ∧ C.SolOK H ∧ b ≤ 2 ^ C.ip.Pf ∧
    (∀ q, nFreeSeqA (H.getD q []) ≤ 3) ∧
    (nRegA H = C.ip.k ∨ (nRegA H ≤ C.ip.k ∧ b = 0 ∧ ∀ q, nFreeSeqA (H.getD q []) = 0)) ∧
    1 ≤ nRegA H

/-- **The promise** before phase `p`. -/
structure Promise (p : ℕ) (pr : Pair) : Prop where
  sol : Sol C.par X.d (C.fhat pr.b) C.ip.η (decH hX pr.H)
  sol' : Sol C.par X.d (C.fhat pr.b') C.ip.η (decH hX pr.H')
  ok : C.SolOK pr.H
  ok' : C.SolOK pr.H'
  b_le : pr.b ≤ 2 ^ C.ip.Pf
  b'_le : pr.b' ≤ 2 ^ C.ip.Pf
  sand : sandwich (nRegA pr.H) (nRegA pr.H') C.ip.k = true
  diff : (pr.b' < pr.b ∧ C.fhat pr.b - C.fhat pr.b' ≤ C.ip.η ∧ pr.H.take p = pr.H'.take p) ∨
    (pr.b = pr.b' ∧ ∃ q < p, ∃ t z g, g + 1 ≤ 2 ^ C.ip.Pu ∧
      (pr.H.getD q []).getD t (0, 0) = (z, g + 1) ∧
      pr.H'.take p = (pr.H.take p).modify q (·.set t (z, g + 2)))
  det : C.complete (C.fhat pr.b) (pr.H.take p) = pr.H
  det' : C.complete (C.fhat pr.b') (pr.H'.take p) = pr.H'
  free3 : ∀ q, nFreeSeqA (pr.H.getD q []) ≤ 3 ∧ nFreeSeqA (pr.H'.getD q []) ≤ 3

/-- A prefix of `p` sequences of an `η`-valid solution at `f̂ b`, before phase `p`. -/
structure PreOK (p b : ℕ) (pre : List (List AAtom)) : Prop where
  len : pre.length = p
  lt : p < 2 * C.ip.R
  b_le : b ≤ 2 ^ C.ip.Pf
  valid : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)
  ok : C.SolOK pre
  free3 : ∀ q, nFreeSeqA (pre.getD q []) ≤ 3

/-! ### Counting identities -/

include hX in
/-- A free copy at offset `K` does not change the count. -/
theorem cnt_append_top (f : ℚ) (pre : List (List AAtom)) (W : List AAtom) (z : ℕ) :
    C.cnt f pre (W ++ [(z, 2 ^ C.ip.Pu + 1)]) = C.cnt f pre W :=
  MergeH.cnt_append_top' hX f pre W z

/-- Replacing a regular atom by a free copy at offset `0` lowers the count by exactly one. -/
theorem cnt_swapFree (f : ℚ) (pre : List (List AAtom)) (A B : List AAtom) (z : ℕ) :
    C.cnt f pre (A ++ (z, 0) :: B) = C.cnt f pre (A ++ B ++ [(z, 1)]) + 1 :=
  MergeH.cnt_swapFree' f pre A B z

/-! ### Outputs after a good prefix -/

/-- The completion after a good prefix and a sequence with at most three free atoms has at most
three free atoms per sequence. -/
theorem PreOK.free_complete {p b : ℕ} {pre : List (List AAtom)} (hpre : PreOK hX p b pre)
    (f : ℚ) {W : List AAtom} (hW : nFreeSeqA W ≤ 3) (q : ℕ) :
    nFreeSeqA ((C.complete f (pre ++ [W])).getD q []) ≤ 3 := by
  rcases lt_trichotomy q p with hq | rfl | hq
  · rw [MergeH.complete_getD_lt hpre.len hpre.lt W hq]
    exact hpre.free3 q
  · rw [MergeH.complete_getD_self hpre.len hpre.lt W]
    exact hW
  · have := hpre.lt
    rw [MergeH.complete_free_gt (by simp [hpre.len]; omega) (by simp [hpre.len]; omega)]
    omega

/-- A free copy in range. -/
theorem atomOK_free {z g : ℕ} (hz : z < C.ip.m) (hg : g ≤ 2 ^ C.ip.Pu) : C.AtomOK (z, g + 1) :=
  ⟨hz, Nat.add_le_add_right hg 1⟩

/-! ### The steps of a phase -/

omit hX in
/-- The flattening of a list of sequences around a free atom, and after changing it. -/
theorem flatten_offset {L : List (List AAtom)} {q t z g : ℕ} (hq : q < L.length)
    (hat : (L.getD q []).getD t (0, 0) = (z, g + 1)) (a : AAtom) :
    ∃ A B, L.flatten = A ++ (z, g + 1) :: B ∧
      (L.modify q (·.set t a)).flatten = A ++ a :: B := by
  rw [MergeH.getD_of_lt hq] at hat
  have ht : t < L[q].length := by
    by_contra ht
    rw [MergeH.getD_of_le (by omega)] at hat
    simp at hat
  rw [MergeH.getD_of_lt ht] at hat
  refine ⟨_, _, ?_, MergeH.flatten_modify_set L hq ht a⟩
  rw [MergeH.flatten_split L hq ht, hat]

/-- Both solutions of the promise have `2R` sequences. -/
theorem Promise.length {p : ℕ} {pr : Pair} (h : Promise hX p pr) :
    pr.H.length = 2 * C.ip.R ∧ pr.H'.length = 2 * C.ip.R := by
  have h1 := h.sol.1
  have h2 := h.sol'.1
  rw [MergeH.decH_length] at h1 h2
  exact ⟨h1, h2⟩

/-! ### The phases -/

/-- Sequence `p` of the other solution is the completion of its first `p` sequences. -/
theorem Promise.getD_H' {p : ℕ} (hp : p < 2 * C.ip.R) {pr : Pair} (h : Promise hX p pr) :
    pr.H'.getD p [] =
      C.completeSeq (typ1 p) (C.fhat pr.b') (C.θseq p) (pr.H'.take p).flatten [] := by
  have := C.complete_getD (C.fhat pr.b') (H := pr.H'.take p) (p := p) (by simp) hp
  rwa [h.det'] at this

/-- **The promise cannot hold after the last phase**: the two solutions would agree except for
the parameters, hence have the same number of regular atoms. -/
theorem not_promise_end {pr : Pair} : ¬ Promise hX (2 * C.ip.R) pr := by
  intro h
  obtain ⟨hlenH, hlenH'⟩ := h.length
  have hs := h.sand
  rcases h.diff with ⟨-, -, htake⟩ | ⟨-, q, hq, t, z, g, -, hat, htake⟩
  · rw [List.take_of_length_le hlenH.le, List.take_of_length_le hlenH'.le] at htake
    rw [htake, MergeH.sandwich_iff] at hs
    omega
  · rw [List.take_of_length_le hlenH.le, List.take_of_length_le hlenH'.le] at htake
    obtain ⟨A, B, hA, hB⟩ := flatten_offset (L := pr.H) (by omega) hat (z, g + 1 + 1)
    rw [show (z, g + 2) = (z, g + 1 + 1) from rfl, ← htake] at hB
    have : nRegA pr.H = nRegA pr.H' := by
      rw [MergeH.nRegA_eq_flatten, MergeH.nRegA_eq_flatten, hA, hB, MergeH.nRegSeq_append,
        MergeH.nRegSeq_append, MergeH.nRegSeq_cons_free, MergeH.nRegSeq_cons_free]
    rw [this, MergeH.sandwich_iff] at hs
    omega

end Ctx

end BCFGJPSSV26.Greedy


