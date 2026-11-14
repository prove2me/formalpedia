-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxCore
-- name    : BCFGJPSSV26_Greedy_PolyTime_AuxCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:14:57.08025+00:00
-- url     : https://prove2.me/theorems/b8e2daf8-d802-4c19-9a10-9fd015e1d93d
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.AuxCore — Polynomial time of the core: the merge loop
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.AuxCore` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The states of the merge loop (`BCFGJPSSV26.Greedy.Ctx.mergeUpTo`) are polynomially bounded
--   (`BCFGJPSSV26.Greedy.PT.ResOK`): before phase `p`, both solutions of a pair have at most `2R`
--   sequences of at most `Λ = 9L + 5` atoms, their sequences from `p` on have at most `L` atoms (they
--   are completions), and every atom has a facility at most `m` and an offset index at most
--   `2^Pu + 1`. A phase keeps this (`BCFGJPSSV26.Greedy.PT.phase_ok`): its new solutions are
--   completions of `H.take p` and one sequence of at most `Λ` atoms built from the `p`-th sequences of
--   the pair by the walk (at most `3L + 1` atoms per point), step C and the binary search.
--
--   **Contents.** The module is published as a whole: 38 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxCore`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/AuxCore.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMerge
public import Mathlib.Data.List.GetD
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_EraseDupsBy

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.AuxCore` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of the core: the merge loop

The states of the merge loop (`BCFGJPSSV26.Greedy.Ctx.mergeUpTo`) are polynomially bounded
(`BCFGJPSSV26.Greedy.PT.ResOK`): before phase `p`, both solutions of a pair have at most `2R`
sequences of at most `Λ = 9L + 5` atoms, their sequences from `p` on have at most `L` atoms (they
are completions), and every atom has a facility at most `m` and an offset index at most
`2^Pu + 1`. A phase keeps this (`BCFGJPSSV26.Greedy.PT.phase_ok`): its new solutions are
completions of `H.take p` and one sequence of at most `Λ` atoms built from the `p`-th sequences of
the pair by the walk (at most `3L + 1` atoms per point), step C and the binary search.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### The invariant of the merge -/

/-- The atoms of the merge: facilities at most `m`, offset indices at most `2^Pu + 1`. -/
def AOK (C : Ctx) (a : AAtom) : Prop := a.1 ≤ C.ip.m ∧ a.2 ≤ 2 ^ C.ip.Pu + 1

/-- The bound on the sequences of the merge. -/
def Lam (C : Ctx) : ℕ := 9 * C.ip.L + 5

/-- A solution of the merge. -/
def SolB (C : Ctx) (H : List (List AAtom)) : Prop :=
  H.length ≤ 2 * C.ip.R ∧ ∀ S ∈ H, PSeq (AOK C) (Lam C) S

/-- A solution of the merge before phase `p`: its sequences from `p` on have at most `L`
atoms. -/
def SolT (C : Ctx) (p : ℕ) (H : List (List AAtom)) : Prop :=
  SolB C H ∧ ∀ q, p ≤ q → (H.getD q []).length ≤ C.ip.L

/-- The invariant of the merge before phase `p`. -/
def ResOK (C : Ctx) (p : ℕ) : Ctx.Res → Prop
  | .done H b => SolB C H ∧ b ≤ 2 ^ C.ip.Pf
  | .cont pr => SolT C p pr.H ∧ SolT C p pr.H' ∧ pr.b ≤ 2 ^ C.ip.Pf ∧ pr.b' ≤ 2 ^ C.ip.Pf

/-- The results of a step of a phase: the default, or completions of `pre` and one sequence of
at most `Λ` atoms. -/
def OutF (C : Ctx) (f : ℚ) (pre : List (List AAtom)) (b Λ : ℕ) (dflt r : Ctx.Res) : Prop :=
  r = dflt ∨ (∃ W, PSeq (AOK C) Λ W ∧ r = .done (C.complete f (pre ++ [W])) b) ∨
    ∃ W W', PSeq (AOK C) Λ W ∧ PSeq (AOK C) Λ W' ∧
      r = .cont ⟨C.complete f (pre ++ [W]), C.complete f (pre ++ [W']), b, b⟩

theorem OutF.mono {C : Ctx} {f : ℚ} {pre : List (List AAtom)} {b Λ Λ' : ℕ} {dflt r : Ctx.Res}
    (h : OutF C f pre b Λ dflt r) (hΛ : Λ ≤ Λ') : OutF C f pre b Λ' dflt r := by
  rcases h with h | ⟨W, hW, h⟩ | ⟨W, W', hW, hW', h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨W, hW.mono hΛ, h⟩)
  · exact Or.inr (Or.inr ⟨W, W', hW.mono hΛ, hW'.mono hΛ, h⟩)

theorem aok_fresh {C : Ctx} {a : AAtom} (h : a.1 < C.ip.m ∧ a.2 = 0) : AOK C a :=
  ⟨h.1.le, by rw [h.2]; exact Nat.zero_le _⟩

theorem elim_cases {β γ : Type} (o : Option β) (d : γ) (F : β → γ) (P : γ → Prop)
    (h1 : o = none → P d) (h2 : ∀ x, o = some x → P (F x)) : P (o.elim d F) := by
  cases o with
  | none => exact h1 rfl
  | some x => exact h2 x rfl

theorem pseq_append {P : AAtom → Prop} {N N' : ℕ} {S S' : List AAtom} (h : PSeq P N S)
    (h' : PSeq P N' S') : PSeq P (N + N') (S ++ S') :=
  ⟨by simp only [List.length_append]; exact Nat.add_le_add h.1 h'.1, fun a ha ↦ by
    rcases List.mem_append.1 ha with ha | ha
    · exact h.2 a ha
    · exact h'.2 a ha⟩

theorem pseq_single {P : AAtom → Prop} {a : AAtom} (h : P a) : PSeq P 1 [a] :=
  ⟨le_rfl, fun x hx ↦ by rw [List.mem_singleton.1 hx]; exact h⟩

theorem pseq_drop {P : AAtom → Prop} {N r : ℕ} {S : List AAtom} (h : PSeq P N S) :
    PSeq P N (S.drop r) :=
  ⟨by simp only [List.length_drop]; have := h.1; omega,
    fun a ha ↦ h.2 a (List.mem_of_mem_drop ha)⟩

theorem getD_mem_or {β : Type} (l : List β) (q : ℕ) (d : β) : l.getD q d ∈ l ∨ l.getD q d = d := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[q]? with _ | v
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem iterate_searchStep_inv (k : ℕ) (cf : ℕ → ℕ) {B : ℕ} {st : ℕ × ℕ × Option ℕ}
    (h : SInv B st) (t : ℕ) : SInv B ((Ctx.searchStep k cf)^[t] st) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [Function.iterate_succ_apply']; exact searchStep_inv k cf ih

theorem sinv_start (B : ℕ) : SInv B (0, B, none) :=
  ⟨Nat.zero_le _, le_rfl, fun v hv ↦ by cases hv⟩

/-! ### Completions -/

theorem complete_solT (C : Ctx) (f : ℚ) {pre : List (List AAtom)} {W : List AAtom} {p : ℕ}
    (hpre : ∀ S ∈ pre, PSeq (AOK C) (Lam C) S) (hW : PSeq (AOK C) (Lam C) W)
    (hlen : pre.length ≤ p) (hp : p < 2 * C.ip.R) :
    SolT C (p + 1) (C.complete f (pre ++ [W])) ∧
      (W.length ≤ C.ip.L → ∀ q, pre.length ≤ q →
        ((C.complete f (pre ++ [W])).getD q []).length ≤ C.ip.L) := by
  obtain ⟨T, hT, hlenT, hfresh⟩ := complete_eq C f (pre ++ [W])
  have hL : C.ip.L ≤ Lam C := by unfold Lam; omega
  have hTget : ∀ q, (T.getD q []).length ≤ C.ip.L := fun q ↦ by
    rcases getD_mem_or T q [] with h | h
    · exact (hfresh _ h).1
    · rw [h]; simp
  have hget : ∀ q, pre.length + 1 ≤ q →
      ((C.complete f (pre ++ [W])).getD q []).length ≤ C.ip.L := fun q hq ↦ by
    rw [hT, List.getD_append_right _ _ _ _ (by simp; omega)]
    exact hTget _
  refine ⟨⟨⟨?_, ?_⟩, fun q hq ↦ hget q (by omega)⟩, fun hWL q hq ↦ ?_⟩
  · rw [hT]
    simp only [List.length_append, List.length_singleton] at hlenT ⊢
    omega
  · intro S hS
    rw [hT] at hS
    rcases List.mem_append.1 hS with hS | hS
    · rcases List.mem_append.1 hS with hS | hS
      · exact hpre S hS
      · rw [List.mem_singleton.1 hS]; exact hW
    · exact ⟨(hfresh S hS).1.trans hL, fun a ha ↦ aok_fresh ((hfresh S hS).2 a ha)⟩
  · rcases Nat.lt_or_ge pre.length q with h | h
    · exact hget q h
    · have : q = pre.length := by omega
      subst this
      rw [hT, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      simpa using hWL

theorem sol_solT (C : Ctx) (b : ℕ) : SolT C 0 (C.sol b) := by
  obtain ⟨T, hT, hlenT, hfresh⟩ := complete_eq C (C.fhat b) []
  unfold Ctx.sol
  rw [hT]
  simp only [List.nil_append, List.length_nil] at hlenT ⊢
  refine ⟨⟨by omega, fun S hS ↦ ⟨(hfresh S hS).1.trans (by unfold Lam; omega),
    fun a ha ↦ aok_fresh ((hfresh S hS).2 a ha)⟩⟩, fun q _ ↦ ?_⟩
  rcases getD_mem_or T q [] with h | h
  · exact (hfresh _ h).1
  · rw [h]; simp

theorem bisect_ok (C : Ctx) : ResOK C 0 C.bisect := by
  have hs := iterate_searchStep_inv C.ip.k (fun b ↦ nRegA (C.sol b)) (sinv_start (2 ^ C.ip.Pf))
    C.ip.Pf
  rw [bisect_eq]
  split_ifs
  · exact ⟨(sol_solT C 0).1, Nat.zero_le _⟩
  · exact ⟨(sol_solT C _).1, le_rfl⟩
  · change SInv _ (bisIter C) at hs
    obtain ⟨hlo, hhi, ho⟩ := hs
    rcases h : (bisIter C).2.2 with _ | b
    · exact ⟨sol_solT C _, sol_solT C _, hhi, hlo⟩
    · exact ⟨(sol_solT C _).1, ho b h⟩

/-! ### The forms of the steps -/

theorem binSearch_form (C : Ctx) (f : ℚ) (b : ℕ) (pre : List (List AAtom)) {base : List AAtom}
    {z N : ℕ} (hbase : PSeq (AOK C) N base) (hz : z ≤ C.ip.m) (dflt : Ctx.Res) :
    OutF C f pre b (N + 1) dflt (C.binSearch f b pre base z) := by
  have hW : ∀ g ≤ 2 ^ C.ip.Pu, PSeq (AOK C) (N + 1) (base ++ [(z, g + 1)]) := fun g hg ↦
    pseq_append hbase (pseq_single ⟨hz, Nat.add_le_add_right hg 1⟩)
  have hs := iterate_searchStep_inv C.ip.k (fun g ↦ C.cnt f pre (base ++ [(z, g + 1)]))
    (sinv_start (2 ^ C.ip.Pu)) C.ip.Pu
  change SInv _ (binIter C f pre base z) at hs
  obtain ⟨hlo, hhi, ho⟩ := hs
  rw [binSearch_eq]
  split_ifs
  · exact Or.inr (Or.inl ⟨_, hW 0 (Nat.zero_le _), rfl⟩)
  · exact Or.inr (Or.inl ⟨_, hW _ le_rfl, rfl⟩)
  · rcases h : (binIter C f pre base z).2.2 with _ | g
    · exact Or.inr (Or.inr ⟨_, _, hW _ hlo, hW _ hhi, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, hW g (ho g h), rfl⟩)

theorem stepC_form (C : Ctx) (f : ℚ) (b : ℕ) (pre : List (List AAtom)) {Xs Ys Zs : List AAtom}
    {h : Option AAtom} {N : ℕ} (hXs : PSeq (AOK C) N Xs) (hYs : PSeq (AOK C) N Ys)
    (hZs : PSeq (AOK C) N Zs) (hh : ∀ a, h = some a → a.1 ≤ C.ip.m) (dflt : Ctx.Res) :
    OutF C f pre b (N + N + N + 2) dflt (C.stepC f b pre Xs h Ys Zs dflt) := by
  have hF : PSeq (AOK C) 1 (stF h) := by
    rcases h with _ | a
    · exact ⟨Nat.zero_le _, by simp [stF]⟩
    · exact pseq_single ⟨hh a rfl, Nat.le_add_left 1 _⟩
  have hPr : ∀ r, PSeq (AOK C) (N + N + N + 1) (stPr Xs Ys Zs h r) := fun r ↦
    pseq_append (pseq_append (pseq_append hXs hYs) (pseq_drop hZs)) hF
  have hafter : PSeq (AOK C) (N + N + N) (Xs ++ Ys ++ Zs) := pseq_append (pseq_append hXs hYs) hZs
  have hz0 : stZ h ≤ C.ip.m := by
    rcases h with _ | a
    · exact Nat.zero_le _
    · exact hh a rfl
  have hzt : ∀ t, (Zs.getD t (0, 0)).1 ≤ C.ip.m := fun t ↦ by
    rcases getD_mem_or Zs t (0, 0) with h' | h'
    · exact (hZs.2 _ h').1
    · rw [h']; exact Nat.zero_le _
  rw [stepC_eq]
  refine elim_cases _ _ _ (OutF C f pre b (N + N + N + 2) dflt) (fun _ ↦ ?_) fun W hfind ↦ ?_
  · refine elim_cases _ _ _ (OutF C f pre b (N + N + N + 2) dflt) (fun _ ↦ Or.inl rfl)
      fun t _ ↦ ?_
    unfold stAfter
    split_ifs
    · exact (binSearch_form C f b pre hafter hz0 dflt).mono (by omega)
    · exact Or.inr (Or.inl ⟨_, (pseq_append (hPr t) (pseq_single
        (a := ((Zs.getD (t - 1) (0, 0)).1, 1)) ⟨hzt _, Nat.le_add_left 1 _⟩)).mono le_rfl, rfl⟩)
    · exact (binSearch_form C f b pre (hPr t) (hzt _) dflt).mono le_rfl
  · have hmem := List.mem_of_find?_eq_some hfind
    refine Or.inr (Or.inl ⟨W, ?_, rfl⟩)
    unfold stPts at hmem
    rcases List.mem_cons.1 hmem with rfl | hmem
    · exact hafter.mono (by omega)
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hmem
      exact (hPr r).mono (by omega)

/-- The atoms of the merge satisfy what the walk needs. -/
theorem walkP_aok (C : Ctx) {Hp H'p : List AAtom} (hHp : ∀ a ∈ Hp, AOK C a)
    (hH'p : ∀ a ∈ H'p, AOK C a) : WalkP C (AOK C) Hp H'p where
  reg _ hi := aok_fresh ⟨hi, rfl⟩
  zero := ⟨Nat.zero_le _, Nat.zero_le _⟩
  zero1 := ⟨Nat.zero_le _, Nat.le_add_left 1 _⟩
  free a ha := ⟨⟨(hHp a ha).1, Nat.le_add_left 1 _⟩, ⟨(hHp a ha).1, Nat.zero_le _⟩⟩
  start := hH'p

theorem walkPhase_form (C : Ctx) (p : ℕ) (f : ℚ) (b : ℕ) (pre : List (List AAtom))
    {Hp H'p : List AAtom} (hHp : PSeq (AOK C) C.ip.L Hp) (hH'p : PSeq (AOK C) C.ip.L H'p)
    (dflt : Ctx.Res) :
    OutF C f pre b (Lam C) dflt (C.walkPhase p f b pre Hp H'p dflt) := by
  have hN : 3 * (H'p.length + 2 * C.ip.L + 1) + 2 ≤ Lam C := by
    have := hH'p.1; unfold Lam; omega
  obtain ⟨-, -, hent⟩ := walkB_inv C (walkP_aok C hHp.2 hH'p.2) p f pre C.ip.L le_rfl
  change ∀ e ∈ C.walkB p f pre Hp H'p, PEnt (AOK C) (H'p.length + 2 * C.ip.L + 1) e at hent
  set N := H'p.length + 2 * C.ip.L + 1
  have hd : PEnt (AOK C) N ([], .init) :=
    ⟨pseq_nil _ _, ⟨Nat.zero_le _, Nat.zero_le _⟩, pseq_nil _ _, pseq_nil _ _, pseq_nil _ _⟩
  have hget : ∀ t, PEnt (AOK C) N ((C.walkB p f pre Hp H'p).getD t ([], .init)) := fun t ↦ by
    rcases getD_mem_or (C.walkB p f pre Hp H'p) t ([], .init) with h | h
    · exact hent _ h
    · rw [h]; exact hd
  rw [walkPhase_eq]
  refine elim_cases _ _ _ (OutF C f pre b (Lam C) dflt) (fun _ ↦ ?_) fun w hfind ↦ ?_
  · refine elim_cases _ _ _ (OutF C f pre b (Lam C) dflt) (fun _ ↦ ?_) fun t _ ↦ ?_
    · have hlast : PEnt (AOK C) N ((C.walkB p f pre Hp H'p).reverse.headD ([], .init)) := by
        rw [List.headD_eq_head?_getD]
        rcases h : (C.walkB p f pre Hp H'p).reverse.head? with _ | e
        · exact hd
        · exact hent e (List.mem_reverse.1 (List.mem_of_mem_head? h))
      exact (stepC_form C f b pre (hHp.mono (by omega)) (pseq_nil _ _) (pseq_drop hlast.1)
        (fun a ha ↦ by cases ha) dflt).mono (by omega)
    · obtain ⟨hk1, hk2, hk3, hk4⟩ := (hget (t + 1)).2
      unfold wkElim
      split_ifs
      · exact (binSearch_form C f b pre (hget t).1 hk1.1 dflt).mono (by omega)
      · exact (stepC_form C f b pre hk2 hk3 hk4 (fun a ha ↦ by cases ha; exact hk1.1)
          dflt).mono (by omega)
      · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨w.1, (hent w (List.mem_of_find?_eq_some hfind)).1.mono (by omega),
      rfl⟩)

/-! ### Phases -/

theorem solT_mono {C : Ctx} {p : ℕ} {H : List (List AAtom)} (h : SolT C p H) :
    SolT C (p + 1) H := ⟨h.1, fun q hq ↦ h.2 q (by omega)⟩

theorem solB_take {C : Ctx} {H : List (List AAtom)} (h : SolB C H) (p : ℕ) :
    ∀ S ∈ H.take p, PSeq (AOK C) (Lam C) S := fun S hS ↦ h.2 S (List.mem_of_mem_take hS)

theorem solB_getD {C : Ctx} {H : List (List AAtom)} (h : SolB C H) (p : ℕ) :
    ∀ a ∈ H.getD p [], AOK C a := fun a ha ↦ by
  rcases getD_mem_or H p [] with h' | h'
  · exact (h.2 _ h').2 a ha
  · rw [h'] at ha; cases ha

/-- **A phase keeps the invariant of the merge.** -/
theorem phase_ok (C : Ctx) {p : ℕ} (hp : p < 2 * C.ip.R) {pr : Ctx.Pair}
    (h : ResOK C p (.cont pr)) : ResOK C (p + 1) (C.phase p pr) := by
  obtain ⟨hH, hH', hb, hb'⟩ := h
  have hpre := solB_take hH.1 p
  have hlen : (pr.H.take p).length ≤ p := List.length_take_le _ _
  have hW : PSeq (AOK C) C.ip.L (pr.H'.getD p []) := ⟨hH'.2 p le_rfl, solB_getD hH'.1 p⟩
  have hL : C.ip.L ≤ Lam C := by unfold Lam; omega
  obtain ⟨hS, hS'⟩ := complete_solT C (C.fhat pr.b) hpre (hW.mono hL) hlen hp
  have hout : ∀ r, OutF C (C.fhat pr.b) (pr.H.take p) pr.b (Lam C) (.done pr.H pr.b) r →
      ResOK C (p + 1) r := by
    intro r hr
    rcases hr with rfl | ⟨W, hW, rfl⟩ | ⟨W, W', hW, hW', rfl⟩
    · exact ⟨hH.1, hb⟩
    · exact ⟨(complete_solT C _ hpre hW hlen hp).1.1, hb⟩
    · exact ⟨(complete_solT C _ hpre hW hlen hp).1, (complete_solT C _ hpre hW' hlen hp).1, hb,
        hb⟩
  rw [phase_eq]
  split_ifs
  · exact ⟨hS.1, hb⟩
  · exact ⟨hS, solT_mono hH', hb, hb'⟩
  · refine hout _ (walkPhase_form C p _ pr.b _ ⟨hH.2 p le_rfl, solB_getD hH.1 p⟩ ?_ _)
    refine ⟨hS' hW.1 p hlen, fun a ha ↦ ?_⟩
    rcases getD_mem_or (C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []])) p [] with
      h' | h'
    · exact (hS.1.2 _ h').2 a ha
    · rw [h'] at ha; cases ha

theorem mergeStep_ok (C : Ctx) {p : ℕ} (hp : p < 2 * C.ip.R) {r : Ctx.Res} (h : ResOK C p r) :
    ResOK C (p + 1) (C.mergeStep r p) := by
  cases r with
  | done H b => exact h
  | cont pr => exact phase_ok C hp h

/-! ### Encoded lengths of the states of the merge -/

theorem len_aok {C : Ctx} {a : AAtom} (h : AOK C a) :
    (encAt a).length ≤ 2 * C.ip.m + C.ip.Pu + 3 := by
  rw [len_encAt]
  have h1 := (len_encNat_le_self a.1).trans h.1
  have h2 : (encNat a.2).length ≤ C.ip.Pu + 2 := by
    refine length_encNat_le_of_lt_two_pow ?_
    have h3 := h.2
    have h4 : 1 ≤ 2 ^ C.ip.Pu := Nat.one_le_two_pow
    rw [pow_add]
    generalize 2 ^ C.ip.Pu = B at *
    omega
  omega

/-- A bound on the encoded solutions of the merge. -/
def solBd (C : Ctx) : ℕ := 2 * C.ip.R * (2 * (Lam C * (2 * (2 * C.ip.m + C.ip.Pu + 3) + 1)) + 1)

theorem len_solB {C : Ctx} {H : List (List AAtom)} (h : SolB C H) : (encSl H).length ≤ solBd C :=
  len_encList_le_of encSq h.1 fun S hS ↦ len_encList_le_of encAt (h.2 S hS).1 fun a ha ↦
    len_aok ((h.2 S hS).2 a ha)

/-- A bound on the encoded states of the merge. -/
def resBd (C : Ctx) : ℕ := 3 + (2 * solBd C + 1 + (2 * solBd C + 1 + (3 * (C.ip.Pf + 1) + 1)))

theorem len_grid {C : Ctx} {b : ℕ} (h : b ≤ 2 ^ C.ip.Pf) : (encNat b).length ≤ C.ip.Pf + 1 := by
  refine length_encNat_le_of_lt_two_pow ?_
  rw [pow_succ]
  have : 1 ≤ 2 ^ C.ip.Pf := Nat.one_le_two_pow
  generalize 2 ^ C.ip.Pf = B at *
  omega

theorem len_resOK {C : Ctx} {p : ℕ} {r : Ctx.Res} (h : ResOK C p r) :
    (encRs r).length ≤ resBd C := by
  have e : (encRs r).length = (encPair encBool encPT (resT r)).length := rfl
  rw [e]
  unfold resBd
  cases r with
  | done H b =>
    obtain ⟨hH, hb⟩ := h
    have := len_solB hH
    have := len_grid hb
    simp only [resT, length_encPair, encBool_apply, List.length_singleton]
    have h0 : (encSl []).length = 0 := rfl
    have h0' : (encNat 0).length = 0 := by simp [encNat_apply]
    omega
  | cont pr =>
    obtain ⟨hH, hH', hb, hb'⟩ := h
    have := len_solB hH.1
    have := len_solB hH'.1
    have := len_grid hb
    have := len_grid hb'
    simp only [resT, pairT, length_encPair, encBool_apply, List.length_singleton]
    omega

theorem prefix_range {l : List ℕ} {v n : ℕ} (h : l ++ [v] <+: List.range n) :
    v = l.length ∧ v < n := by
  rw [List.prefix_iff_eq_take, List.take_range] at h
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_singleton, List.length_range] at hlen
  have hn : l.length + 1 ≤ n := by omega
  rw [show min (l ++ [v]).length n = l.length + 1 by simp; omega, List.range_succ] at h
  have := (List.append_inj' h rfl).2
  simp only [List.cons.injEq, and_true] at this
  exact ⟨this, by omega⟩

/-! ### Certificates of the merge and of the core -/

variable {α : Type} {input : α ↪ List Bool} (c : Consts) {X : α → CoreIn}

theorem mergeUpToR (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).mergeUpTo (2 * (ctx c (X a)).ip.R)) input
      encRs := by
  unfold Ctx.mergeUpTo
  have hsize : PolyBounded (fun a ↦ (input a).length) fun a ↦ resBd (ctx c (X a)) := by
    unfold resBd solBd Lam
    have hR := (RU c hX).polyBounded
    have hm := (mU c hX).polyBounded
    have hPu := (PuU c hX).polyBounded
    have hPf := (PfU c hX).polyBounded
    have hL := (LU c hX).polyBounded
    have hS : PolyBounded (fun a ↦ (input a).length) fun a ↦ 2 * (ctx c (X a)).ip.R *
        (2 * ((9 * (ctx c (X a)).ip.L + 5) * (2 * (2 * (ctx c (X a)).ip.m +
          (ctx c (X a)).ip.Pu + 3) + 1)) + 1) :=
      ((PolyBounded.const 2).mul hR).mul (((PolyBounded.const 2).mul ((((PolyBounded.const 9).mul
        hL).add (.const 5)).mul (((PolyBounded.const 2).mul ((((PolyBounded.const 2).mul hm).add
          hPu).add (.const 3))).add (.const 1)))).add (.const 1))
    exact (PolyBounded.const 3).add ((((PolyBounded.const 2).mul hS).add (.const 1)).add
      ((((PolyBounded.const 2).mul hS).add (.const 1)).add (((PolyBounded.const 3).mul
        (hPf.add (.const 1))).add (.const 1))))
  exact (foldlWith_spec (par := fun a ↦ a)
    (list := fun a ↦ List.range (2 * (ctx c (X a)).ip.R))
    (init := fun a ↦ (ctx c (X a)).bisect)
    (step := fun a r p ↦ (ctx c (X a)).mergeStep r p)
    id' (unary_range' (unary_mul' (const 2) (RU c hX))) (bisectR c hX)
    (mergeStepR c (hX.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _)) (snd _ _))
    (fun a consumed r ↦ ResOK (ctx c (X a)) consumed.length r)
    (fun a ↦ bisect_ok _)
    (fun a consumed r v hpre h ↦ by
      obtain ⟨rfl, hv⟩ := prefix_range hpre
      simpa using mergeStep_ok (ctx c (X a)) hv h)
    hsize (fun a consumed r _ h ↦ len_resOK h)).1

theorem merge_eq (C : Ctx) :
    C.merge = resElim (C.mergeUpTo (2 * C.ip.R)) (fun H b ↦ (H, b)) fun pr ↦ (pr.H, pr.b) := by
  unfold Ctx.merge
  cases C.mergeUpTo (2 * C.ip.R) <;> rfl

theorem mergeS (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).merge) input (encPair encSl encNat) := by
  simp only [merge_eq]
  exact rsElim (F := fun _ H b ↦ (H, b)) (G := fun _ pr ↦ (pr.H, pr.b)) (mergeUpToR c hX)
    (snd _ _) ((prH (snd _ _)).prod (prb (snd _ _)))

theorem coreS (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ core c (X a)) input (encList encNat) := by
  unfold core toCenters
  have hH : ComputableInPolyTime (fun a ↦ (ctx c (X a)).merge.1) input encSl :=
    (fst _ _).comp (mergeS c hX)
  exact eraseDupsByWithInput (r := fun _ i j ↦ i == j)
    (mapWithInput (f := fun _ (a : AAtom) ↦ a.1) (flattenS hH) ((fst _ _).comp (snd _ _)))
    (beq ((snd _ _).comp (fst _ _)) (snd _ _))

end BCFGJPSSV26.Greedy.PT


