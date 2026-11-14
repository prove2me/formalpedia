-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeSubmod
-- name    : BCFGJPSSV26_Stable_Time_PolyTimeSubmod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:26:54.213327+00:00
-- url     : https://prove2.me/theorems/c9397be2-b053-46d5-8364-9430cfa91226
-- title:
--   BCFGJPSSV26.Stable.Time.PolyTimeSubmod — The submodular step in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.PolyTimeSubmod` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Certificates for the exact submodular functions (`BCFGJPSSV26.Raw.gQ`), the sequential greedy
--   (`BCFGJPSSV26.Stable.seqGreedyQ`) and the candidates (`BCFGJPSSV26.Stable.candidate`).
--
--   The sums of the `z` smallest values and the choice of the `z` red centers sort with `List.mergeSort`
--   (`Turing.MultiTapeTM.ComputableInPolyTime.listMergeSort`). The greedy makes `N` rounds, each
--   appending one element of a part to each of its `ρ` lists, so its states grow by a bounded amount;
--   its sums run over the at most `B + 1` tuples of `Tuples.tuples`.
--
--   **Contents.** The module is published as a whole: 30 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeSubmod`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/PolyTimeSubmod.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeKS

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.PolyTimeSubmod` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The submodular step in polynomial time

Certificates for the exact submodular functions (`BCFGJPSSV26.Raw.gQ`), the sequential greedy
(`BCFGJPSSV26.Stable.seqGreedyQ`) and the candidates (`BCFGJPSSV26.Stable.candidate`).

The sums of the `z` smallest values and the choice of the `z` red centers sort with `List.mergeSort`
(`Turing.MultiTapeTM.ComputableInPolyTime.listMergeSort`). The greedy makes `N` rounds, each
appending one element of a part to each of its `ρ` lists, so its states grow by a bounded amount;
its sums run over the at most `B + 1` tuples of `Tuples.tuples`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable.PolyTime

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### The submodular functions -/

theorem g₁Q' {x : α → Raw} {LS Y : α → List ℕ} {Λ : α → List DumQ}
    (hx : ComputableInPolyTime x input encRaw) (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hΛ : ComputableInPolyTime Λ input (encList encDum))
    (hY : ComputableInPolyTime Y input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (x a).g₁Q (LS a) (Λ a) (Y a)) input encRat := by
  unfold Raw.g₁Q
  have hx' : ComputableInPolyTime (fun p : α × ℕ ↦ x p.1) (encPair input encNat) encRaw :=
    hx.comp (fst _ _)
  exact rat_sum' (mapWithInput (f := fun a j ↦ min ((x a).dMixQ j (LS a) (Λ a))
    ((x a).dSetQ j (Y a))) (rangeN' hx (raw_n' hx) hn)
    (rat_min' (dMixQ' hx' (snd _ _) (hLS.comp (fst _ _)) (hΛ.comp (fst _ _)))
      (dSetQ' hx' (snd _ _) (hY.comp (fst _ _)))))

theorem hclQ' {x : α → Raw} {LS blue Y : α → List ℕ} {Λ : α → List DumQ} {c : α → ℕ}
    (hx : ComputableInPolyTime x input encRaw) (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hΛ : ComputableInPolyTime Λ input (encList encDum))
    (hblue : ComputableInPolyTime blue input (encList encNat))
    (hc : ComputableInPolyTime c input encNat)
    (hY : ComputableInPolyTime Y input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (x a).hclQ (LS a) (Λ a) (blue a) (c a) (Y a)) input encRat := by
  unfold Raw.hclQ
  have hcl := clusterMixQ' hx hn hLS hΛ hc
  exact rat_add' (costMixOnQ' hx hLS hΛ hcl)
    (rat_mul' (rat_natCast' (unary_to_binary.comp ((length_list encNat).comp hcl)))
      (dMixQ' hx (binAdd' (raw_n' hx) hc) (listAppend' hblue hY) hΛ))

theorem sumSmallestQ' {z : α → ℕ} {l : α → List ℚ} (hz : ComputableInPolyTime z input encNat)
    (hl : ComputableInPolyTime l input (encList encRat)) :
    ComputableInPolyTime (fun a ↦ Raw.sumSmallestQ (z a) (l a)) input encRat := by
  unfold Raw.sumSmallestQ
  have hle : ComputableInPolyTime (fun p : α × ℚ × ℚ ↦ decide (p.2.1 ≤ p.2.2))
      (encPair input (encPair encRat encRat)) encBool :=
    rat_le' ((fst _ _).comp (snd _ _)) ((snd _ _).comp (snd _ _))
  exact rat_sum' (listTakeBin (listMergeSort (le := fun _ a a' ↦ decide (a ≤ a')) hl hle
    (fun _ a b c h₁ h₂ ↦ by simp only [decide_eq_true_eq] at h₁ h₂ ⊢; exact h₁.trans h₂)
    (fun _ a b ↦ by simpa using le_total a b)) hz)

theorem g₂Q' {x : α → Raw} {LS red blue Y : α → List ℕ} {Λ : α → List DumQ} {z : α → ℕ}
    (hx : ComputableInPolyTime x input encRaw) (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hΛ : ComputableInPolyTime Λ input (encList encDum))
    (hred : ComputableInPolyTime red input (encList encNat))
    (hblue : ComputableInPolyTime blue input (encList encNat))
    (hz : ComputableInPolyTime z input encNat)
    (hY : ComputableInPolyTime Y input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (x a).g₂Q (LS a) (Λ a) (red a) (blue a) (z a) (Y a)) input
      encRat := by
  unfold Raw.g₂Q
  have hx' : ComputableInPolyTime (fun p : α × ℕ ↦ x p.1) (encPair input encNat) encRaw :=
    hx.comp (fst _ _)
  exact sumSmallestQ' hz (mapWithInput (f := fun a c ↦ (x a).hclQ (LS a) (Λ a) (blue a) c (Y a))
    hred (hclQ' hx' (fun p ↦ hn p.1) (hLS.comp (fst _ _)) (hΛ.comp (fst _ _))
      (hblue.comp (fst _ _)) (snd _ _) (hY.comp (fst _ _))))

theorem gQ' {x : α → Raw} {LS red blue Y : α → List ℕ} {Λ : α → List DumQ} {z : α → ℕ}
    (hx : ComputableInPolyTime x input encRaw) (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hΛ : ComputableInPolyTime Λ input (encList encDum))
    (hred : ComputableInPolyTime red input (encList encNat))
    (hblue : ComputableInPolyTime blue input (encList encNat))
    (hz : ComputableInPolyTime z input encNat)
    (hY : ComputableInPolyTime Y input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (x a).gQ (LS a) (Λ a) (red a) (blue a) (z a) (Y a)) input
      encRat := by
  unfold Raw.gQ
  exact rat_add' (g₁Q' hx hn hLS hΛ hY) (g₂Q' hx hn hLS hΛ hred hblue hz hY)

/-! ### First maximizers and minimizers -/

theorem argmaxBy' {β : Type} {encB : β ↪ List Bool} {f : α → β → ℚ} {l : α → List β}
    {d : α → β} (hf : ComputableInPolyTime (fun p : α × β ↦ f p.1 p.2) (encPair input encB) encRat)
    (hl : ComputableInPolyTime l input (encList encB)) (hd : ComputableInPolyTime d input encB) :
    ComputableInPolyTime (fun a ↦ argmaxBy (f a) (l a) (d a)) input encB := by
  unfold argmaxBy
  have htest : ComputableInPolyTime (fun p : α × β ↦ (l p.1).all fun a' ↦
      decide (f p.1 a' ≤ f p.1 p.2)) (encPair input encB) encBool :=
    allWithInput (test := fun (p : α × β) a' ↦ decide (f p.1 a' ≤ f p.1 p.2)) (hl.comp (fst _ _))
      (rat_le' (hf.comp (g := fun q : (α × β) × β ↦ (q.1.1, q.2))
        (((fst _ _).comp (fst _ _)).prod (snd _ _)))
        (hf.comp (g := fun q : (α × β) × β ↦ (q.1.1, q.1.2))
          (((fst _ _).comp (fst _ _)).prod ((snd _ _).comp (fst _ _)))))
  exact (optionGetD encB).comp ((findWithInput (test := fun a b ↦ (l a).all fun a' ↦
    decide (f a a' ≤ f a b)) hl htest).prod hd)

theorem argminBy' {β : Type} {encB : β ↪ List Bool} {f : α → β → ℚ} {l : α → List β}
    {d : α → β} (hf : ComputableInPolyTime (fun p : α × β ↦ f p.1 p.2) (encPair input encB) encRat)
    (hl : ComputableInPolyTime l input (encList encB)) (hd : ComputableInPolyTime d input encB) :
    ComputableInPolyTime (fun a ↦ argminBy (f a) (l a) (d a)) input encB := by
  unfold argminBy
  have htest : ComputableInPolyTime (fun p : α × β ↦ (l p.1).all fun a' ↦
      decide (f p.1 p.2 ≤ f p.1 a')) (encPair input encB) encBool :=
    allWithInput (test := fun (p : α × β) a' ↦ decide (f p.1 p.2 ≤ f p.1 a')) (hl.comp (fst _ _))
      (rat_le' (hf.comp (g := fun q : (α × β) × β ↦ (q.1.1, q.1.2))
          (((fst _ _).comp (fst _ _)).prod ((snd _ _).comp (fst _ _))))
        (hf.comp (g := fun q : (α × β) × β ↦ (q.1.1, q.2))
        (((fst _ _).comp (fst _ _)).prod (snd _ _))))
  exact (optionGetD encB).comp ((findWithInput (test := fun a b ↦ (l a).all fun a' ↦
    decide (f a b ≤ f a a')) hl htest).prod hd)

theorem argmaxBy_mem_or {β : Type} (f : β → ℚ) (l : List β) (d : β) :
    argmaxBy f l d ∈ l ∨ argmaxBy f l d = d := by
  unfold argmaxBy
  cases h : l.find? _ with
  | none => exact .inr rfl
  | some c => exact .inl (List.mem_of_find?_eq_some h)

/-! ### The sequential greedy -/

/-- Lists of lists of numbers. -/
abbrev encLL : List (List ℕ) ↪ List Bool := encList (encList encNat)

theorem greedyQL' {Lst : α → List (List ℕ)} {j t : α → ℕ} {V : α → List ℕ}
    (hLst : ComputableInPolyTime Lst input encLL) (hj : ComputableInPolyTime j input encNat)
    (ht : ComputableInPolyTime t input encNat)
    (hV : ComputableInPolyTime V input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ greedyQL (Lst a) (j a) (t a) (V a)) input (encList encNat) := by
  unfold greedyQL
  have hj' : ComputableInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encNat :=
    unary_to_binary.comp (snd _ _)
  have hv : ComputableInPolyTime (fun p : α × ℕ ↦ (V p.1).getD p.2 0) (encPair input encUnary)
      encNat := listGetDWithInput (hV.comp (fst _ _)) (snd _ _) 0
  have hcond : ComputableInPolyTime (fun p : α × ℕ ↦ decide ((p.2 < j p.1 ∧
      (V p.1).getD p.2 0 ≤ t p.1) ∨ (j p.1 < p.2 ∧ (V p.1).getD p.2 0 < t p.1)))
      (encPair input encUnary) encBool :=
    decide_or (decide_and (binary_lt' hj' (hj.comp (fst _ _))) (binary_le' hv (ht.comp (fst _ _))))
      (decide_and (binary_lt' (hj.comp (fst _ _)) hj') (binary_lt' hv (ht.comp (fst _ _))))
  have hel : ComputableInPolyTime (fun p : α × ℕ ↦ ((Lst p.1).getD p.2 []).getD
      ((V p.1).getD p.2 0) 0) (encPair input encUnary) encNat :=
    listGetD_binary (encA := encNat) 0 (listGetDWithInput (hLst.comp (fst _ _)) (snd _ _) []) hv
  exact listFilterMap (f := fun a j' ↦ if (j' < j a ∧ (V a).getD j' 0 ≤ t a) ∨
      (j a < j' ∧ (V a).getD j' 0 < t a) then some (((Lst a).getD j' []).getD ((V a).getD j' 0) 0)
      else none) 0 (unary_range' ((length_list (encList encNat)).comp hLst))
    (ite_decide hcond ((optionSome encNat).comp hel) (const none))

/-- A set function given with the input. -/
abbrev SetFn (input : α ↪ List Bool) (g : α → List ℕ → ℚ) : Prop :=
  ComputableInPolyTime (fun p : α × List ℕ ↦ g p.1 p.2) (encPair input (encList encNat)) encRat

theorem SetFn.at {g : α → List ℕ → ℚ} (hg : SetFn input g) {S : α → List ℕ}
    (hS : ComputableInPolyTime S input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ g a (S a)) input encRat :=
  hg.comp (g := fun a ↦ (a, S a)) (id'.prod hS)

theorem SetFn.comp' {β : Type} {encB : β ↪ List Bool} {g : β → List ℕ → ℚ} (hg : SetFn encB g)
    {f : α → β} (hf : ComputableInPolyTime f input encB) : SetFn input fun a ↦ g (f a) :=
  hg.comp (g := fun p : α × List ℕ ↦ (f p.1, p.2)) ((hf.comp (fst _ _)).prod (snd _ _))

theorem gainQ' {g : α → List ℕ → ℚ} {Lst : α → List (List ℕ)} {j t e : α → ℕ}
    {Vs : α → List (List ℕ)} (hg : SetFn input g) (hLst : ComputableInPolyTime Lst input encLL)
    (hj : ComputableInPolyTime j input encNat) (ht : ComputableInPolyTime t input encNat)
    (hVs : ComputableInPolyTime Vs input encLL) (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a ↦ gainQ (g a) (Lst a) (j a) (t a) (Vs a) (e a)) input encRat := by
  unfold gainQ
  have hq : ComputableInPolyTime (fun p : α × List ℕ ↦ greedyQL (Lst p.1) (j p.1) (t p.1) p.2)
      (encPair input (encList encNat)) (encList encNat) :=
    greedyQL' (hLst.comp (fst _ _)) (hj.comp (fst _ _)) (ht.comp (fst _ _)) (snd _ _)
  have hg' := hg.comp' (fst input (encList encNat))
  exact rat_sum' (mapWithInput (f := fun a V ↦ g a (greedyQL (Lst a) (j a) (t a) V) -
    g a (e a :: greedyQL (Lst a) (j a) (t a) V)) hVs
    (rat_sub' (hg'.at hq) (hg'.at (cons' (he.comp (fst _ _)) hq))))

/-- Setting an entry of a list. -/
theorem listSetGen' {β : Type} {encB : β ↪ List Bool} {l : α → List β} {i : α → ℕ} {v : α → β}
    (hl : ComputableInPolyTime l input (encList encB)) (hi : ComputableInPolyTime i input encNat)
    (hv : ComputableInPolyTime v input encB) :
    ComputableInPolyTime (fun a ↦ (l a).set (i a) (v a)) input (encList encB) := by
  have heq : ∀ (l : List β) (i : ℕ) (v : β),
      l.set i v = l.zipIdx.map fun p ↦ if p.2 = i then v else p.1 := by
    intro l i v
    refine List.ext_getElem (by simp) fun j h₁ h₂ ↦ ?_
    simp only [List.getElem_set, List.getElem_map, List.getElem_zipIdx, zero_add]
    by_cases hj : j = i
    · subst hj
      simp
    · rw [if_neg (Ne.symm hj), if_neg hj]
  simp only [heq]
  have hz : ComputableInPolyTime (fun a ↦ (l a).zipIdx) input (encList (encPair encB encUnary)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zipIdx encB).comp hl.tidy)
  exact mapWithInput (f := fun a (p : β × ℕ) ↦ if p.2 = i a then v a else p.1) hz
    (ite_decide (decide_eq' (unary_to_binary.comp ((snd _ _).comp (snd _ _)))
      (hi.comp (fst _ _))) (hv.comp (fst _ _)) ((fst _ _).comp (snd _ _)))

theorem length_encList_set_append_le (l : List (List ℕ)) (j e : ℕ) :
    (encLL (l.set j (l.getD j [] ++ [e]))).length ≤
      (encLL l).length + 2 * (2 * (encNat e).length + 1) := by
  induction l generalizing j with
  | nil => simp
  | cons a l ih =>
    cases j with
    | zero =>
      simp only [List.set_cons_zero, List.getD_cons_zero, length_encList, List.map_cons,
        List.sum_cons, List.map_append, List.sum_append, List.map_nil, List.sum_nil]
      omega
    | succ j =>
      have := ih j
      simp only [List.set_cons_succ, List.getD_cons_succ, length_encList, List.map_cons,
        List.sum_cons] at this ⊢
      omega

theorem foldl_length_le {β γ : Type} (e : β ↪ List Bool) (f : β → γ → β) (G : ℕ)
    (l : List γ) (hf : ∀ s c, c ∈ l → (e (f s c)).length ≤ (e s).length + G) (s₀ : β) :
    (e (l.foldl f s₀)).length ≤ (e s₀).length + l.length * G := by
  induction l generalizing s₀ with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, List.length_cons]
    have h1 := hf s₀ c List.mem_cons_self
    have h2 := ih (fun s c hc ↦ hf s c (List.mem_cons_of_mem _ hc)) (f s₀ c)
    rw [Nat.succ_mul]
    omega

theorem length_getD_le (parts : List (List ℕ)) (j : ℕ) :
    (encList encNat (parts.getD j [])).length ≤ (encList (encList encNat) parts).length := by
  rw [List.getD_eq_getElem?_getD]
  cases h' : parts[j]? with
  | none => simp
  | some r =>
    have hr := List.mem_of_getElem? h'
    exact SizedListEncoding.length_elem_le (encA := encList encNat)
      (encL := encList (encList encNat)) parts r hr

/-- The step of a round of the greedy. -/
def roundStep (g : List ℕ → ℚ) (parts : List (List ℕ)) (Vs : List (List ℕ)) (t : ℕ)
    (Lst : List (List ℕ)) (j : ℕ) : List (List ℕ) :=
  Lst.set j (Lst.getD j [] ++ [argmaxBy (gainQ g Lst j t Vs) (parts.getD j []) 0])

theorem roundStep_growth (g : List ℕ → ℚ) (parts Vs : List (List ℕ)) (t : ℕ)
    (Lst : List (List ℕ)) (j : ℕ) :
    (encLL (roundStep g parts Vs t Lst j)).length ≤
      (encLL Lst).length + 2 * (2 * (encLL parts).length + 1) := by
  unfold roundStep
  refine (length_encList_set_append_le _ _ _).trans (Nat.add_le_add_left ?_ _)
  have : (encNat (argmaxBy (gainQ g Lst j t Vs) (parts.getD j []) 0)).length ≤
      (encLL parts).length := by
    rcases argmaxBy_mem_or (gainQ g Lst j t Vs) (parts.getD j []) 0 with h | h
    · have hrow := length_getD_le parts j
      exact (SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat) _ _
        h).trans hrow
    · rw [h]
      exact Nat.zero_le _
  omega

theorem roundStep' {g : α → List ℕ → ℚ} {parts Vs Lst : α → List (List ℕ)} {t j : α → ℕ}
    (hg : SetFn input g) (hparts : ComputableInPolyTime parts input encLL)
    (hVs : ComputableInPolyTime Vs input encLL) (ht : ComputableInPolyTime t input encNat)
    (hLst : ComputableInPolyTime Lst input encLL) (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ roundStep (g a) (parts a) (Vs a) (t a) (Lst a) (j a)) input
      encLL := by
  unfold roundStep
  have hpj : ComputableInPolyTime (fun a ↦ (parts a).getD (j a) []) input (encList encNat) :=
    listGetD_binary (encA := encList encNat) [] hparts hj
  have hgain : ComputableInPolyTime (fun p : α × ℕ ↦ gainQ (g p.1) (Lst p.1) (j p.1) (t p.1)
      (Vs p.1) p.2) (encPair input encNat) encRat :=
    gainQ' (hg.comp' (fst _ _)) (hLst.comp (fst _ _)) (hj.comp (fst _ _)) (ht.comp (fst _ _))
      (hVs.comp (fst _ _)) (snd _ _)
  exact listSetGen' hLst hj (listAppend' (listGetD_binary (encA := encList encNat) [] hLst hj)
    (cons' (argmaxBy' hgain hpj (const 0)) (const [])))

theorem greedyRound_eq (g : List ℕ → ℚ) (parts Vs : List (List ℕ)) (t : ℕ)
    (Lst : List (List ℕ)) :
    greedyRound g parts Vs t Lst = (List.range parts.length).foldl (roundStep g parts Vs t) Lst :=
  rfl

theorem greedyRound' {g : α → List ℕ → ℚ} {parts Vs Lst : α → List (List ℕ)} {t : α → ℕ}
    (hg : SetFn input g) (hparts : ComputableInPolyTime parts input encLL)
    (hVs : ComputableInPolyTime Vs input encLL) (ht : ComputableInPolyTime t input encNat)
    (hLst : ComputableInPolyTime Lst input encLL) :
    ComputableInPolyTime (fun a ↦ greedyRound (g a) (parts a) (Vs a) (t a) (Lst a)) input
      encLL := by
  simp only [greedyRound_eq]
  have hstep : ComputableInPolyTime (fun p : (α × List (List ℕ)) × ℕ ↦ roundStep (g p.1.1)
      (parts p.1.1) (Vs p.1.1) (t p.1.1) p.1.2 p.2) (encPair (encPair input encLL) encUnary)
      encLL :=
    roundStep' (hg.comp' ((fst _ _).comp (fst _ _))) (hparts.comp ((fst _ _).comp (fst _ _)))
      (hVs.comp ((fst _ _).comp (fst _ _))) (ht.comp ((fst _ _).comp (fst _ _)))
      ((snd _ _).comp (fst _ _)) (unary_to_binary.comp (snd _ _))
  exact foldlWith_of_bounded_growth (par := fun a ↦ a)
    (list := fun a ↦ List.range (parts a).length)
    (step := fun a Lst j ↦ roundStep (g a) (parts a) (Vs a) (t a) Lst j) id'
    (unary_range' ((length_list (encList encNat)).comp hparts)) hLst hstep
    (growth := fun a ↦ 2 * (2 * (encLL (parts a)).length + 1))
    ((PolyBounded.const 2).mul (((PolyBounded.const 2).mul hparts.polyBounded_length).add
      (.const 1)))
    fun a Lst j _ ↦ roundStep_growth _ _ _ _ _ _

theorem pickQ' {Lst : α → List (List ℕ)} {V : α → List ℕ}
    (hLst : ComputableInPolyTime Lst input encLL)
    (hV : ComputableInPolyTime V input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ pickQ (Lst a) (V a)) input (encList encNat) := by
  unfold pickQ
  exact mapWithInput (f := fun a j ↦ ((Lst a).getD j []).getD ((V a).getD j 0) 0)
    (unary_range' ((length_list (encList encNat)).comp hLst))
    (listGetD_binary (encA := encNat) 0 (listGetDWithInput (hLst.comp (fst _ _)) (snd _ _) [])
      (listGetDWithInput (hV.comp (fst _ _)) (snd _ _) 0))

theorem greedyRound_growth (g : List ℕ → ℚ) (parts Vs : List (List ℕ)) (t : ℕ)
    (Lst : List (List ℕ)) :
    (encLL (greedyRound g parts Vs t Lst)).length ≤
      (encLL Lst).length + parts.length * (2 * (2 * (encLL parts).length + 1)) := by
  rw [greedyRound_eq]
  have := foldl_length_le encLL (roundStep g parts Vs t) (2 * (2 * (encLL parts).length + 1))
    (List.range parts.length) (fun s c _ ↦ roundStep_growth _ _ _ _ _ _) Lst
  rwa [List.length_range] at this

/-- **The sequential greedy.** -/
theorem seqGreedyQ' {g : α → List ℕ → ℚ} {parts : α → List (List ℕ)} {T B : α → ℕ}
    (hg : SetFn input g) (hparts : ComputableInPolyTime parts input encLL)
    (hT : ComputableInPolyTime T input encUnary) (hB : ComputableInPolyTime B input encUnary) :
    ComputableInPolyTime (fun a ↦ seqGreedyQ (g a) (parts a) (T a) (B a)) input
      (encList encNat) := by
  unfold seqGreedyQ
  have hlen : ComputableInPolyTime (fun a ↦ (parts a).length) input encUnary :=
    (length_list (encList encNat)).comp hparts
  have hVs : ComputableInPolyTime (fun a ↦ Tuples.tuples (B a) (T a) (parts a).length) input
      encLL := Tuples.tuples' hB (unary_to_binary.comp hT) hlen
  have hstep : ComputableInPolyTime (fun p : (α × List (List ℕ)) × ℕ ↦ greedyRound (g p.1.1)
      (parts p.1.1) (Tuples.tuples (B p.1.1) (T p.1.1) (parts p.1.1).length) p.2 p.1.2)
      (encPair (encPair input encLL) encUnary) encLL :=
    greedyRound' (hg.comp' ((fst _ _).comp (fst _ _))) (hparts.comp ((fst _ _).comp (fst _ _)))
      (hVs.comp ((fst _ _).comp (fst _ _))) (unary_to_binary.comp (snd _ _))
      ((snd _ _).comp (fst _ _))
  have hLst : ComputableInPolyTime (fun a ↦ (List.range (T a)).foldl (fun Lst t ↦
      greedyRound (g a) (parts a) (Tuples.tuples (B a) (T a) (parts a).length) t Lst)
      (List.replicate (parts a).length [])) input encLL :=
    foldlWith_of_bounded_growth (par := fun a ↦ a) (list := fun a ↦ List.range (T a))
      (step := fun a Lst t ↦ greedyRound (g a) (parts a)
        (Tuples.tuples (B a) (T a) (parts a).length) t Lst) id' (unary_range' hT)
      (replicate hlen (const [])) hstep
      (growth := fun a ↦ (parts a).length * (2 * (2 * (encLL (parts a)).length + 1)))
      (hlen.polyBounded.mul ((PolyBounded.const 2).mul (((PolyBounded.const 2).mul
        hparts.polyBounded_length).add (.const 1))))
      fun a Lst t _ ↦ greedyRound_growth _ _ _ _ _
  have hpick : SetFn input fun a V ↦ g a (pickQ ((List.range (T a)).foldl (fun Lst t ↦
      greedyRound (g a) (parts a) (Tuples.tuples (B a) (T a) (parts a).length) t Lst)
      (List.replicate (parts a).length [])) V) :=
    (hg.comp' (fst _ _)).at (pickQ' (hLst.comp (fst _ _)) (snd _ _))
  exact pickQ' hLst (argminBy' hpick hVs (const []))

/-! ### The candidates -/

/-- The greedy choice of a guess. -/
def candY (N : ℕ) (x : Raw) (B : ℕ) (LS' : List ℕ) (Λ : List DumQ) (col : List Bool) (p' : ℕ) :
    List ℕ :=
  seqGreedyQ (x.gQ LS' Λ (redOf LS' col) (blueOf LS' col) ((LS'.length + (Λ.length + p')) - x.k))
    (Λ.map x.ballQ ++ List.replicate p' (List.range x.m)) N B

/-- The key by which the red centers are sorted. -/
def zhKey (N : ℕ) (x : Raw) (B : ℕ) (LS' : List ℕ) (Λ : List DumQ) (col : List Bool) (p' : ℕ)
    (c : ℕ) : ℚ :=
  x.hclQ LS' Λ (blueOf LS' col) c (candY N x B LS' Λ col p')

/-- The candidate without its `let`s. -/
theorem candidate_eq (N : ℕ) (x : Raw) (s B : ℕ) (LS' : List ℕ) (Λ : List DumQ)
    (col : List Bool) (p' : ℕ) : candidate N x s B LS' Λ col p' =
    if s < Λ.length + p' ∨ (redOf LS' col).length < (LS'.length + (Λ.length + p')) - x.k ∨
        Λ.any (fun l ↦ (x.ballQ l).isEmpty) then none
    else some ((LS'.filter fun c ↦ decide (c ∉ ((redOf LS' col).mergeSort fun c c' ↦
      decide (zhKey N x B LS' Λ col p' c ≤ zhKey N x B LS' Λ col p' c')).take
        ((LS'.length + (Λ.length + p')) - x.k))) ++ candY N x B LS' Λ col p').dedup := rfl

/-- **A candidate**, when the clients and facilities are at most the rows of the table. -/
theorem candidate' {N s B p' : α → ℕ} {x : α → Raw} {LS : α → List ℕ} {Λ : α → List DumQ}
    {col : α → List Bool} (hN : ComputableInPolyTime N input encUnary)
    (hx : ComputableInPolyTime x input encRaw)
    (hfit : ∀ a, (x a).n + (x a).m ≤ (x a).table.length)
    (hs : ComputableInPolyTime s input encNat) (hB : ComputableInPolyTime B input encUnary)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hΛ : ComputableInPolyTime Λ input (encList encDum))
    (hcol : ComputableInPolyTime col input (encList encBool))
    (hp : ComputableInPolyTime p' input encUnary) :
    ComputableInPolyTime (fun a ↦ candidate (N a) (x a) (s a) (B a) (LS a) (Λ a) (col a) (p' a))
      input (encOption (encList encNat)) := by
  simp only [candidate_eq]
  have hn : ∀ a, (x a).n ≤ (x a).table.length := fun a ↦ by have := hfit a; omega
  have hm : ∀ a, (x a).m ≤ (x a).table.length := fun a ↦ by have := hfit a; omega
  have hred := redOf' hLS hcol
  have hblue := blueOf' hLS hcol
  have hρ : ComputableInPolyTime (fun a ↦ (Λ a).length + p' a) input encNat :=
    binAdd' (unary_to_binary.comp ((length_list encDum).comp hΛ)) (unary_to_binary.comp hp)
  have hz : ComputableInPolyTime (fun a ↦ ((LS a).length + ((Λ a).length + p' a)) - (x a).k)
      input encNat :=
    binary_sub' (binAdd' (unary_to_binary.comp ((length_list encNat).comp hLS)) hρ) (raw_k' hx)
  have hball : ComputableInPolyTime (fun a ↦ (Λ a).any fun l ↦ ((x a).ballQ l).isEmpty) input
      encBool :=
    anyWithInput (test := fun a l ↦ ((x a).ballQ l).isEmpty) hΛ
      ((listIsEmpty (encA := encNat)).comp (ballQ' (hx.comp (fst _ _)) (fun p ↦ hm p.1)
        (snd _ _)))
  have hcond : ComputableInPolyTime (fun a ↦ decide (s a < (Λ a).length + p' a ∨
      (redOf (LS a) (col a)).length < ((LS a).length + ((Λ a).length + p' a)) - (x a).k ∨
      (Λ a).any (fun l ↦ ((x a).ballQ l).isEmpty) = true)) input encBool :=
    decide_or (binary_lt' hs hρ) (decide_or (binary_lt' (unary_to_binary.comp
      ((length_list encNat).comp hred)) hz) (decide_eq' hball (const true)))
  have hg : SetFn input fun a Y ↦ (x a).gQ (LS a) (Λ a) (redOf (LS a) (col a))
      (blueOf (LS a) (col a)) (((LS a).length + ((Λ a).length + p' a)) - (x a).k) Y :=
    gQ' (hx.comp (fst _ _)) (fun p ↦ hn p.1) (hLS.comp (fst _ _)) (hΛ.comp (fst _ _))
      (hred.comp (fst _ _)) (hblue.comp (fst _ _)) (hz.comp (fst _ _)) (snd _ _)
  have hparts : ComputableInPolyTime (fun a ↦ (Λ a).map (x a).ballQ ++
      List.replicate (p' a) (List.range (x a).m)) input encLL :=
    listAppend' (mapWithInput (f := fun a l ↦ (x a).ballQ l) hΛ
      (ballQ' (hx.comp (fst _ _)) (fun p ↦ hm p.1) (snd _ _)))
      (replicate hp (rangeN' hx (raw_m' hx) hm))
  have hY : ComputableInPolyTime (fun a ↦ candY (N a) (x a) (B a) (LS a) (Λ a) (col a) (p' a))
      input (encList encNat) := by
    unfold candY
    exact seqGreedyQ' hg hparts hN hB
  have hK : ComputableInPolyTime (fun q : α × ℕ ↦ zhKey (N q.1) (x q.1) (B q.1) (LS q.1)
      (Λ q.1) (col q.1) (p' q.1) q.2) (encPair input encNat) encRat := by
    unfold zhKey
    exact hclQ' (hx.comp (fst _ _)) (fun p ↦ hn p.1) (hLS.comp (fst _ _)) (hΛ.comp (fst _ _))
      (hblue.comp (fst _ _)) (snd _ _) (hY.comp (fst _ _))
  have hle : ComputableInPolyTime (fun q : α × ℕ × ℕ ↦ decide
      (zhKey (N q.1) (x q.1) (B q.1) (LS q.1) (Λ q.1) (col q.1) (p' q.1) q.2.1 ≤
        zhKey (N q.1) (x q.1) (B q.1) (LS q.1) (Λ q.1) (col q.1) (p' q.1) q.2.2))
      (encPair input (encPair encNat encNat)) encBool :=
    rat_le' (hK.comp (g := fun q : α × ℕ × ℕ ↦ (q.1, q.2.1))
        ((fst _ _).prod ((fst _ _).comp (snd _ _))))
      (hK.comp (g := fun q : α × ℕ × ℕ ↦ (q.1, q.2.2))
        ((fst _ _).prod ((snd _ _).comp (snd _ _))))
  have hZh := listTakeBin (listMergeSort (le := fun a c c' ↦
      decide (zhKey (N a) (x a) (B a) (LS a) (Λ a) (col a) (p' a) c ≤
        zhKey (N a) (x a) (B a) (LS a) (Λ a) (col a) (p' a) c')) hred hle
    (fun _ a b c h₁ h₂ ↦ by simp only [decide_eq_true_eq] at h₁ h₂ ⊢; exact h₁.trans h₂)
    (fun _ a b ↦ by simpa using le_total _ _)) hz
  exact ite_decide hcond (const none) ((optionSome (encList encNat)).comp
    (listDedup (listAppend' (filterNotMem' hLS hZh) hY)))

end BCFGJPSSV26.Stable.PolyTime


