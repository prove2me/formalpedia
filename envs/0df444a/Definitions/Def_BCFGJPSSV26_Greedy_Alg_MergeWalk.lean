-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk
-- name    : BCFGJPSSV26_Greedy_Alg_MergeWalk
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:59:46.893505+00:00
-- url     : https://prove2.me/theorems/8d69fed8-a762-4e38-87bd-ae21f0a31354
-- title:
--   BCFGJPSSV26.Greedy.Alg.MergeWalk — The walk of step B
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Alg.MergeWalk` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The walk of step B of the merge (`BCFGJPSSV26.Greedy.Ctx.walkB`, after [CGLSS25, Section 3.5.2])
--   from a valid sequence `H'p` of regular atoms towards the sequence `Hp` that the greedy algorithm
--   completes after the prefix:
--
--   * every point is a valid sequence after the prefix, with atoms in range and at most one free atom
--     (`BCFGJPSSV26.Greedy.Ctx.WPt`);
--   * consecutive points differ by a free atom appended to a sequence of regular atoms, by a deletion
--     followed by a completion with regular atoms, or by a free copy at offset `0` made regular
--     (`BCFGJPSSV26.Greedy.Ctx.WTr`);
--   * each round makes the common prefix with `Hp` longer, so after `L ≥ m + 1` rounds `Hp` is a prefix
--     of the last point (`BCFGJPSSV26.Greedy.Ctx.walkB_spec`). The cut `take L` of a deletion never
--     acts, since a point has at most `m` regular atoms and one free atom.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.Ctx.MergeH.Hp_vs`, `BCFGJPSSV26.Greedy.Ctx.MergeH.walkB_spec` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/MergeWalk.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Alg.MergeWalk` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The walk of step B

The walk of step B of the merge (`BCFGJPSSV26.Greedy.Ctx.walkB`, after [CGLSS25, Section 3.5.2])
from a valid sequence `H'p` of regular atoms towards the sequence `Hp` that the greedy algorithm
completes after the prefix:

* every point is a valid sequence after the prefix, with atoms in range and at most one free atom
  (`BCFGJPSSV26.Greedy.Ctx.WPt`);
* consecutive points differ by a free atom appended to a sequence of regular atoms, by a deletion
  followed by a completion with regular atoms, or by a free copy at offset `0` made regular
  (`BCFGJPSSV26.Greedy.Ctx.WTr`);
* each round makes the common prefix with `Hp` longer, so after `L ≥ m + 1` rounds `Hp` is a prefix
  of the last point (`BCFGJPSSV26.Greedy.Ctx.walkB_spec`). The cut `take L` of a deletion never
  acts, since a point has at most `m` regular atoms and one free atom.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

variable {C : Ctx}

theorem delStep_eq (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (Xs Y : List AAtom) (h : AAtom)
    (pts : List (List AAtom × WKind)) :
    C.delStep p f pre Xs.length (Xs ++ h :: Y, pts) =
      ((Xs ++ Y ++ (C.completeSeq (typ1 p) f (C.θseq p) pre.flatten (Xs ++ Y)).drop
          (Xs.length + Y.length)).take C.ip.L,
        pts ++ [((Xs ++ Y ++ (C.completeSeq (typ1 p) f (C.θseq p) pre.flatten (Xs ++ Y)).drop
          (Xs.length + Y.length)).take C.ip.L, .removeComplete Xs h Y
          ((C.completeSeq (typ1 p) f (C.θseq p) pre.flatten (Xs ++ Y)).drop
          (Xs.length + Y.length)))]) := by
  simp [delStep, List.getD_eq_getElem?_getD]

theorem roundB_eq {p : ℕ} {f : ℚ} {pre : List (List AAtom)} {Hp S : List AAtom}
    {pts : List (List AAtom × WKind)} (hnp : ¬ Hp <+: S) {q z : ℕ}
    (hq : commonPrefixLen Hp S = q) (hz : (Hp.getD q (0, 0)).1 = z) :
    C.roundB p f pre Hp (S, pts) =
      (((C.delStep p f pre q)^[S.length - q]
          (S ++ [(z, 1)], pts ++ [(S ++ [(z, 1)], .appendFree z)])).1.set q (z, 0),
        ((C.delStep p f pre q)^[S.length - q]
          (S ++ [(z, 1)], pts ++ [(S ++ [(z, 1)], .appendFree z)])).2 ++
          [(((C.delStep p f pre q)^[S.length - q]
            (S ++ [(z, 1)], pts ++ [(S ++ [(z, 1)], .appendFree z)])).1.set q (z, 0),
            .toRegular)]) := by
  subst hq hz
  simp only [roundB]
  rw [if_neg (by rwa [List.isPrefixOf_iff_prefix])]

theorem roundB_of_prefix {p : ℕ} {f : ℚ} {pre : List (List AAtom)} {Hp : List AAtom}
    {st : List AAtom × List (List AAtom × WKind)} (h : Hp <+: st.1) :
    C.roundB p f pre Hp st = st := by
  simp only [roundB]
  rw [if_pos (List.isPrefixOf_iff_prefix.2 h)]

theorem cpl_of_prefix {l l' : List AAtom} (h : l <+: l') : commonPrefixLen l l' = l.length := by
  exact le_antisymm (cpl_le_left l l') (le_cpl l l' _ le_rfl h.length_le
    (List.take_length.trans (List.prefix_iff_eq_take.1 h)))

/-- A step of the walk, from the sequence `S` to the point `w`. -/
def WTr (S : List AAtom) (w : List AAtom × WKind) : Prop :=
  match w.2 with
  | .init => False
  | .appendFree z => w.1 = S ++ [(z, 1)] ∧ ∀ a ∈ S, a.2 = 0
  | .removeComplete Xs h Y Z => S = Xs ++ h :: Y ∧ w.1 = Xs ++ Y ++ Z ∧ h.2 = 0 ∧
      (∀ a ∈ Z, a.2 = 0) ∧ nFreeSeqA (Xs ++ Y) ≤ 1
  | .toRegular => ∃ A B z, S = A ++ (z, 1) :: B ∧ w.1 = A ++ (z, 0) :: B

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

/-- A point of the walk: a valid sequence after the prefix, with atoms in range and at most one
free atom. -/
def WPt (p b : ℕ) (pre : List (List AAtom)) (W : List AAtom) : Prop :=
  VS hX p b pre W ∧ (∀ a ∈ W, C.AtomOK a) ∧ nFreeSeqA W ≤ 1

/-- The invariant of the list of points of the walk. -/
structure WInv (p b : ℕ) (pre : List (List AAtom)) (H'p : List AAtom)
    (pts : List (List AAtom × WKind)) : Prop where
  head : pts.head? = some (H'p, .init)
  pt : ∀ w ∈ pts, WPt hX p b pre w.1
  tr : ∀ t (ht : t + 1 < pts.length), WTr pts[t].1 pts[t + 1]

variable {p b : ℕ} {pre : List (List AAtom)} {Hp H'p : List AAtom}

theorem WInv.snoc {pts : List (List AAtom × WKind)} (h : WInv hX p b pre H'p pts)
    {S : List AAtom} {κ : WKind} (hlast : pts.getLast? = some (S, κ))
    {w : List AAtom × WKind} (htr : WTr S w) (hw : WPt hX p b pre w.1) :
    WInv hX p b pre H'p (pts ++ [w]) := by
  have hne : pts ≠ [] := by
    rintro rfl
    simp at hlast
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    simpa using h.head
  · intro w' hw'
    rcases List.mem_append.1 hw' with hw' | hw'
    · exact h.pt w' hw'
    · rw [List.mem_singleton.1 hw']
      exact hw
  · intro t ht
    simp only [List.length_append, List.length_singleton] at ht
    by_cases ht' : t + 1 < pts.length
    · rw [List.getElem_append_left ht', List.getElem_append_left (by omega)]
      exact h.tr t ht'
    · have htl : t = pts.length - 1 := by omega
      have hlast' : pts[t]'(by omega) = (S, κ) := by
        rw [List.getLast?_eq_getElem?] at hlast
        subst htl
        exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hlast)
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      simp only [show t + 1 - pts.length = 0 by omega, List.getElem_singleton]
      rw [hlast']
      exact htr

/-! ### The facts about `Hp` -/

section Hp

variable (hlen : pre.length = p) (hokp : C.SolOK pre)
  (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])

include hHp in
theorem Hp_new : ∀ a ∈ Hp, a.2 = 0 ∧ a.1 < C.ip.m := by
  rw [hHp]
  intro a ha
  exact C.completeSeq_new _ _ _ _ [] a (by simpa using ha)

include hHp in
theorem Hp_ok : ∀ a ∈ Hp, C.AtomOK a := fun a ha ↦
  ⟨(Hp_new hHp a ha).2, by rw [(Hp_new hHp a ha).1]; exact Nat.zero_le _⟩

end Hp

/-! ### The deletions of a round -/

/-- A point of the walk has at most `m + 1 ≤ L` atoms. -/
theorem WPt.length_le {W : List AAtom} (h : WPt hX p b pre W) : W.length ≤ C.ip.L := by
  have h1 := h.1.nRegSeq_le hX h.2.1
  have h2 := length_eq_nReg_add_nFree W
  have h3 := hX.L_ge
  have h4 := h.2.2
  omega

/-! ### A round -/

/-! ### The walk -/

end BCFGJPSSV26.Greedy.Ctx.MergeH


