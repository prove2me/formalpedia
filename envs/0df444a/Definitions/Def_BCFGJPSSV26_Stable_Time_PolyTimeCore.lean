-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCore
-- name    : BCFGJPSSV26_Stable_Time_PolyTimeCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:33:00.627484+00:00
-- url     : https://prove2.me/theorems/b1edc44a-4766-4bc4-993f-260b73ad6e04
-- title:
--   BCFGJPSSV26.Stable.Time.PolyTimeCore — The core runs in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.PolyTimeCore` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   `BCFGJPSSV26.Stable.coreAlg_polytime`: the core is polynomial-time in
--   `(N, I, L, coins, B)`, with `N`, `L`, `B` in unary and the coins as bits, one certificate for all
--   `N`: the local search (`BCFGJPSSV26.Stable.localSearch_polytime`), `min(R, B)` trials
--   (`BCFGJPSSV26.Stable.trialAt_polytime`, mapped over the trials), `BCFGJPSSV26.sanitizeK` and the
--   choice of the cheapest (`BCFGJPSSV26.Combine.best_polytime` does the same for `Combine.best`).
--
--   The output has `min(k, m)` entries, and `k`, `m` are written in binary, so the certificate is for
--   the tuples whose table has a row for each point (as for an instance), and the empty list
--   otherwise. When `m ≤ k` the core outputs all the facilities (`BCFGJPSSV26.Stable.coreAlg_of_le`):
--   the local search keeps `0, …, k - 1`, and every candidate is made into all the facilities by
--   `BCFGJPSSV26.sanitizeK`.
--
--   **Contents.** The module is published as a whole: 21 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCore`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/PolyTimeCore.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Main
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeLS
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeTrial
public import Definitions.Def_BuhaiPapers_Background_PolyTime_Lists

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.PolyTimeCore` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The core runs in polynomial time

`BCFGJPSSV26.Stable.coreAlg_polytime`: the core is polynomial-time in
`(N, I, L, coins, B)`, with `N`, `L`, `B` in unary and the coins as bits, one certificate for all
`N`: the local search (`BCFGJPSSV26.Stable.localSearch_polytime`), `min(R, B)` trials
(`BCFGJPSSV26.Stable.trialAt_polytime`, mapped over the trials), `BCFGJPSSV26.sanitizeK` and the
choice of the cheapest (`BCFGJPSSV26.Combine.best_polytime` does the same for `Combine.best`).

The output has `min(k, m)` entries, and `k`, `m` are written in binary, so the certificate is for
the tuples whose table has a row for each point (as for an instance), and the empty list
otherwise. When `m ≤ k` the core outputs all the facilities (`BCFGJPSSV26.Stable.coreAlg_of_le`):
the local search keeps `0, …, k - 1`, and every candidate is made into all the facilities by
`BCFGJPSSV26.sanitizeK`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-- The encoding of the inputs of the core: `N`, `L` and `B` in unary, the coins as bits. -/
abbrev encCoreIn : ℕ × Raw × ℕ × List Bool × ℕ ↪ List Bool :=
  Encoding.encPair Encoding.encUnary (Encoding.encPair encRaw (Encoding.encPair Encoding.encUnary
    (Encoding.encPair Encoding.encBits Encoding.encUnary)))

/-! ### When `m ≤ k` -/

section Degenerate

variable {N L B : ℕ} {x : Raw}

theorem lsApply_range {m k : ℕ} (hmk : m ≤ k) {w : List ℕ} (hw : ∀ y ∈ w, y < k * m) :
    lsApply m w (List.range k) = List.range k := by
  unfold lsApply
  induction w with
  | nil => rfl
  | cons y w ih =>
    rw [List.foldl_cons]
    have hy : y % m ∈ List.range k := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have := hw y List.mem_cons_self
        simp at this
      · exact List.mem_range.2 (lt_of_lt_of_le (Nat.mod_lt y hm) hmk)
    rw [if_pos hy]
    exact ih fun z hz ↦ hw z (List.mem_cons_of_mem _ hz)

theorem lsStep_range (hmk : x.m ≤ x.k) : lsStep N x B (List.range x.k) = List.range x.k := by
  rw [PolyTime.lsStep_eq]
  refine lsApply_range hmk fun y hy ↦ ?_
  cases h : (Tuples.tuples B (x.k * x.m) (Par.p N)).find?
      (fun w ↦ lsImproves N x (List.range x.k) (lsApply x.m w (List.range x.k))) with
  | none => rw [h] at hy; simp at hy
  | some w =>
    rw [h, Option.getD_some] at hy
    exact (Tuples.mem_tuples_le (List.mem_of_find?_eq_some h)).2 y hy

/-- When `m ≤ k`, the local search keeps `0, …, k - 1`. -/
theorem localSearch_of_le (hmk : x.m ≤ x.k) : localSearch N x B = List.range x.k :=
  Function.iterate_fixed (lsStep_range hmk) B

theorem sanitizeK_perm {m k : ℕ} (hmk : m ≤ k) (X : List ℕ) :
    (sanitizeK m k X).Perm (List.range m) := by
  have hp := perm_sanitizeFull m X
  rw [sanitizeK, List.take_of_length_le (by rw [hp.length_eq, List.length_range]; exact hmk)]
  exact hp

theorem sanitizeK_range {m k j : ℕ} (hmk : m ≤ k) (hmj : m ≤ j) :
    sanitizeK m k (List.range j) = List.range m := by
  have hj : List.range j = List.range m ++ (List.range (j - m)).map (m + ·) := by
    rw [← List.range_add, Nat.add_sub_cancel' hmj]
  have hf : (List.range j).filter (fun i ↦ decide (i < m)) = List.range m := by
    rw [hj, List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2, List.append_nil]
    · intro a ha
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      simp
    · intro a ha
      simpa using List.mem_range.1 ha
  have hg : (List.range m).filter (fun i ↦ decide (i ∉ List.range j)) = [] := by
    refine List.filter_eq_nil_iff.2 fun a ha ↦ ?_
    have := List.mem_range.1 ha
    have h' : a ∈ List.range j := List.mem_range.2 (by omega)
    simp [h']
  rw [sanitizeK, hf, List.nodup_range.dedup, hg, List.append_nil,
    List.take_of_length_le (by rw [List.length_range]; exact hmk)]

theorem minQ_perm {l l' : List ℚ} (h : l.Perm l') : Combine.minQ l = Combine.minQ l' := by
  rcases eq_or_ne l [] with rfl | hl
  · rw [List.Perm.nil_eq h]
  have hl' : l' ≠ [] := fun h' ↦ hl (List.Perm.eq_nil (h' ▸ h))
  obtain ⟨h1, h2⟩ := Combine.minQ_spec hl
  obtain ⟨h1', h2'⟩ := Combine.minQ_spec hl'
  exact le_antisymm (h2 _ (h.symm.subset h1')) (h2' _ (h.subset h1))

theorem costQ_perm (n : ℕ) (T : List (List ℚ)) {S S' : List ℕ} (h : S.Perm S') :
    Combine.costQ n T S = Combine.costQ n T S' := by
  unfold Combine.costQ
  congr 1
  refine List.map_congr_left fun j _ ↦ minQ_perm (h.map _)

theorem bestOf_cons {n : ℕ} {T : List (List ℚ)} {Y : List ℕ} {Ys : List (List ℕ)}
    (h : ∀ Z ∈ Y :: Ys, Combine.costQ n T Y ≤ Combine.costQ n T Z) :
    Combine.bestOf n T (Y :: Ys) = Y := by
  unfold Combine.bestOf
  rw [List.find?_cons_of_pos]
  · rfl
  · rw [List.all_eq_true]
    exact fun Z hZ ↦ decide_eq_true (h Z hZ)

/-- **When `m ≤ k`, the core outputs all the facilities.** -/
theorem coreAlg_of_le {coins : List Bool} (hmk : x.m ≤ x.k) :
    coreAlg N x L coins B = List.range x.m := by
  have hcands : ∀ Z ∈ (coreCands N x L coins B).map (sanitizeK x.m x.k),
      Z.Perm (List.range x.m) := by
    intro Z hZ
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hZ
    exact sanitizeK_perm hmk X
  have hhead : sanitizeK x.m x.k (localSearch N x B) = List.range x.m := by
    rw [localSearch_of_le hmk]
    exact sanitizeK_range hmk hmk
  unfold coreAlg
  rw [coreCands, List.map_cons, hhead, bestOf_cons]
  · exact sanitizeK_range hmk le_rfl
  · intro Z hZ
    rw [← hhead]
    have hZ' : Z ∈ (coreCands N x L coins B).map (sanitizeK x.m x.k) := by
      rw [coreCands, List.map_cons, hhead]
      exact hZ
    rw [hhead, costQ_perm _ _ (hcands Z hZ')]

end Degenerate

/-! ### Certificates -/

namespace PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- The numbers below a unary number, in binary. -/
theorem rangeBin' {v : α → ℕ} (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun a ↦ List.range (v a)) input (encList encNat) := by
  have h : ComputableInPolyTime (fun a ↦ (List.range (v a)).map fun i ↦ i) input
      (encList encNat) :=
    mapWithInput (unary_range' hv) (unary_to_binary.comp (snd _ _))
  simpa only [List.map_id'] using h

/-- **`sanitizeK`**, for a number of facilities given in unary too. -/
theorem sanitizeK' {m k : α → ℕ} {X : α → List ℕ} (hm : ComputableInPolyTime m input encNat)
    (hmU : ComputableInPolyTime m input encUnary) (hk : ComputableInPolyTime k input encNat)
    (hX : ComputableInPolyTime X input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ sanitizeK (m a) (k a) (X a)) input (encList encNat) := by
  unfold sanitizeK
  have h1 : ComputableInPolyTime (fun a ↦ (X a).filter fun i ↦ decide (i < m a)) input
      (encList encNat) :=
    filterWithInput (test := fun a i ↦ decide (i < m a)) hX
      (binary_lt' (snd _ _) (hm.comp (fst _ _)))
  have h2 : ComputableInPolyTime (fun a ↦ (List.range (m a)).filter fun i ↦ decide (i ∉ X a))
      input (encList encNat) :=
    filterWithInput (test := fun a i ↦ decide (i ∉ X a)) (rangeBin' hmU)
      (decide_not (decide_mem (hX.comp (fst _ _)) (snd _ _)))
  exact listTakeBin (listAppend' (listDedup h1) h2) hk

/-- **The cheapest of a list of candidates**, by exact cost. -/
theorem bestOf' {n : α → ℕ} {T : α → List (List ℚ)} {vs : α → List (List ℕ)}
    (hn : ComputableInPolyTime n input encNat)
    (hT : ComputableInPolyTime T input (encList (encList encRat)))
    (hvs : ComputableInPolyTime vs input (encList (encList encNat))) :
    ComputableInPolyTime (fun a ↦ Combine.bestOf (n a) (T a) (vs a)) input (encList encNat) := by
  unfold Combine.bestOf
  have hc₁ : ComputableInPolyTime
      (fun q : (α × List ℕ) × List ℕ ↦ Combine.costQ (n q.1.1) (T q.1.1) q.1.2)
      (encPair (encPair input (encList encNat)) (encList encNat)) encRat :=
    Combine.costQ_polytime (hn.comp ((fst _ _).comp (fst _ _)))
      (hT.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _))
  have hc₂ : ComputableInPolyTime
      (fun q : (α × List ℕ) × List ℕ ↦ Combine.costQ (n q.1.1) (T q.1.1) q.2)
      (encPair (encPair input (encList encNat)) (encList encNat)) encRat :=
    Combine.costQ_polytime (hn.comp ((fst _ _).comp (fst _ _)))
      (hT.comp ((fst _ _).comp (fst _ _))) (snd _ _)
  have htest : ComputableInPolyTime (fun p : α × List ℕ ↦ (vs p.1).all fun S' ↦
      decide (Combine.costQ (n p.1) (T p.1) p.2 ≤ Combine.costQ (n p.1) (T p.1) S'))
      (encPair input (encList encNat)) encBool :=
    allWithInput (test := fun (p : α × List ℕ) S' ↦
      decide (Combine.costQ (n p.1) (T p.1) p.2 ≤ Combine.costQ (n p.1) (T p.1) S'))
      (hvs.comp (fst _ _)) (rat_le' hc₁ hc₂)
  exact (optionGetD (encList encNat)).comp ((findWithInput (test := fun a S ↦
    (vs a).all fun S' ↦ decide (Combine.costQ (n a) (T a) S ≤ Combine.costQ (n a) (T a) S'))
      hvs htest).prod (const [0]))

/-- A trial, on tuples whose table has a row for each point. -/
theorem trialAt' {y : α → ℕ × Raw × ℕ × List ℕ × ℕ × List Bool × ℕ}
    (hy : ComputableInPolyTime y input encTrialIn)
    (hfit : ∀ a, (y a).2.1.n + (y a).2.1.m ≤ (y a).2.1.table.length) :
    ComputableInPolyTime (fun a ↦ trialAt (y a)) input (encList (encList encNat)) :=
  (trialAt_polytime.comp hy).of_enc_eq fun a ↦ by
    simp only [Function.comp_apply, if_pos (hfit a)]
    rfl

end PolyTime

open PolyTime

/-- The tuple with no points when the table lacks rows or `m ≤ k`. -/
def fixC (x : Raw) : Raw :=
  if x.n + x.m ≤ x.table.length ∧ x.k < x.m then x else (0, 0, 0, x.table)

theorem fixC_fit (x : Raw) : (fixC x).n + (fixC x).m ≤ (fixC x).table.length := by
  unfold fixC
  split_ifs with h
  · exact h.1
  · exact Nat.zero_le _

theorem fixC_k_le (x : Raw) : (fixC x).k ≤ (fixC x).table.length := by
  unfold fixC
  split_ifs with h
  · exact (Nat.le_of_lt h.2).trans ((Nat.le_add_left _ _).trans h.1)
  · exact Nat.zero_le _

theorem fixC_polytime : ComputableInPolyTime fixC encRaw encRaw := by
  unfold fixC
  have hc : ComputableInPolyTime (fun x : Raw ↦ decide (x.n + x.m ≤ x.table.length ∧ x.k < x.m))
      encRaw encBool := by
    refine (bool_and' (binary_le' (binAdd' (raw_n' id') (raw_m' id'))
      (unary_to_binary.comp (raw_rows' id'))) (binary_lt' (raw_k' id') (raw_m' id'))).of_enc_eq
      fun x ↦ ?_
    rw [Bool.decide_and]
    rfl
  exact ite_decide hc id' ((const 0).prod ((const 0).prod ((const 0).prod (raw_table' id'))))

/-- The trials of the core, as a list of inputs of `BCFGJPSSV26.Stable.trialAt`. -/
theorem coreAlg_eq (N : ℕ) (x : Raw) (L : ℕ) (coins : List Bool) (B : ℕ) :
    coreAlg N x L coins B = sanitizeK x.m x.k (Combine.bestOf x.n x.table
      ((localSearch N x B :: (List.range (min B (Par.R N L))).flatMap fun t ↦
        trialAt (N, x, L, localSearch N x B, B, coins, t)).map (sanitizeK x.m x.k))) := by
  rw [coreAlg, coreCands, min_comm]
  rfl

/-- The core, on tuples with a row for each point and `k < m`. -/
theorem coreFix_polytime : ComputableInPolyTime
    (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦
      coreAlg y.1 (fixC y.2.1) y.2.2.1 y.2.2.2.1 y.2.2.2.2) encCoreIn encCenters := by
  simp only [coreAlg_eq]
  have hN : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ y.1) encCoreIn
      encUnary := fst _ _
  have hx : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ fixC y.2.1) encCoreIn
      encRaw := fixC_polytime.comp ((fst _ _).comp (snd _ _))
  have hL : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ y.2.2.1) encCoreIn
      encUnary := (fst _ _).comp ((snd _ _).comp (snd _ _))
  have hc : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ y.2.2.2.1) encCoreIn
      encBits := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
  have hB : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ y.2.2.2.2) encCoreIn
      encUnary := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
  have hLS := localSearch_polytime' hN hx hB fun y ↦ fixC_k_le y.2.1
  have hR : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ Par.R y.1 y.2.2.1)
      encCoreIn encNat := by
    unfold Par.R Par.s
    exact binary_pow' (unary_to_binary.comp hN) (unary_add' (unary_mul' (const 200)
      (unary_mul' (unary_mul' (const 632) hN) hL)) (const 1))
  have hts : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦
      List.range (min y.2.2.2.2 (Par.R y.1 y.2.2.1))) encCoreIn (encList encUnary) :=
    unary_range' (binary_min_unary' hB hR)
  have htr : ComputableInPolyTime (fun p : (ℕ × Raw × ℕ × List Bool × ℕ) × ℕ ↦
      trialAt (p.1.1, fixC p.1.2.1, p.1.2.2.1, localSearch p.1.1 (fixC p.1.2.1) p.1.2.2.2.2,
        p.1.2.2.2.2, p.1.2.2.2.1, p.2)) (encPair encCoreIn encUnary)
      (encList (encList encNat)) :=
    trialAt' ((hN.comp (fst _ _)).prod ((hx.comp (fst _ _)).prod ((hL.comp (fst _ _)).prod
      ((hLS.comp (fst _ _)).prod ((hB.comp (fst _ _)).prod ((hc.comp (fst _ _)).prod
        (snd _ _)))))))
      fun p ↦ fixC_fit _
  have hcands := cons' hLS (flatMapWithInput (f := fun (y : ℕ × Raw × ℕ × List Bool × ℕ) t ↦
    trialAt (y.1, fixC y.2.1, y.2.2.1, localSearch y.1 (fixC y.2.1) y.2.2.2.2, y.2.2.2.2,
      y.2.2.2.1, t)) hts htr)
  have hmU : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ (fixC y.2.1).m)
      encCoreIn encUnary :=
    le_rows_unary hx (raw_m' hx) fun y ↦ by have := fixC_fit y.2.1; omega
  have hmap := mapWithInput (f := fun (y : ℕ × Raw × ℕ × List Bool × ℕ) X ↦
    sanitizeK (fixC y.2.1).m (fixC y.2.1).k X) hcands
    (sanitizeK' (raw_m' (hx.comp (fst _ _))) (hmU.comp (fst _ _)) (raw_k' (hx.comp (fst _ _)))
      (snd _ _))
  exact sanitizeK' (raw_m' hx) hmU (raw_k' hx) (bestOf' (raw_n' hx) (raw_table' hx) hmap)

/-- **The core is polynomial-time**, on the tuples whose table has a row for each point (as for
an instance): the core enumerates the clients and the facilities, whose numbers are written in
binary. -/
theorem coreAlg_polytime :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ if y.2.1.n + y.2.1.m ≤ y.2.1.table.length then
        coreAlg y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 else [])
      encCoreIn encCenters := by
  have hx : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦ y.2.1) encCoreIn
      encRaw := (fst _ _).comp (snd _ _)
  have hfit : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦
      decide (y.2.1.n + y.2.1.m ≤ y.2.1.table.length)) encCoreIn encBool :=
    binary_le' (binAdd' (raw_n' hx) (raw_m' hx)) (unary_to_binary.comp (raw_rows' hx))
  have hlt : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦
      decide (y.2.1.n + y.2.1.m ≤ y.2.1.table.length ∧ y.2.1.k < y.2.1.m)) encCoreIn encBool := by
    refine (bool_and' hfit (binary_lt' (raw_k' hx) (raw_m' hx))).of_enc_eq fun y ↦ ?_
    rw [Bool.decide_and]
  have hrange : ComputableInPolyTime (fun y : ℕ × Raw × ℕ × List Bool × ℕ ↦
      List.range (min y.2.1.table.length y.2.1.m)) encCoreIn encCenters :=
    rangeBin' (binary_min_unary' (raw_rows' hx) (raw_m' hx))
  refine (ite_decide hlt coreFix_polytime (ite_decide hfit hrange (const []))).of_enc_eq
    fun y ↦ ?_
  by_cases h : y.2.1.n + y.2.1.m ≤ y.2.1.table.length
  · rw [if_pos h]
    by_cases hk : y.2.1.k < y.2.1.m
    · have hfix : fixC y.2.1 = y.2.1 := by
        unfold fixC
        exact if_pos ⟨h, hk⟩
      rw [if_pos ⟨h, hk⟩, hfix]
    · rw [if_neg (fun h' ↦ hk h'.2), if_pos h, coreAlg_of_le (by omega),
        min_eq_right (by omega)]
  · rw [if_neg h, if_neg (fun h' ↦ h h'.1), if_neg h]

end BCFGJPSSV26.Stable


