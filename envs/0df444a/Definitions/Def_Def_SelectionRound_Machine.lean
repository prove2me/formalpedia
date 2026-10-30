-- Prove2me | Definitions.Def_Def_SelectionRound_Machine
-- name    : Def_SelectionRound_Machine
-- status  : Definition
-- author  : @darkhipo
-- created : 2026-10-29T21:53:37.089293+00:00
-- url     : https://prove2.me/theorems/fdc2075b-5f14-4024-8807-0ab2106eb9c0
-- title:
--   Selection-round machine: Light word-RAM closure with the canonical greedy selection round
-- statement:
--   The Light word-RAM framework closure (programs, statements, limits, tasks, cost model, timeUpTo) together with the dense score-table pass, argmin and copy utilities, and the canonical greedy selection round: a fixed six-procedure Light program that computes every candidate score, chooses a remaining minimum-score candidate, copies its complete row into the base buffer, and clears exactly its remaining flag. Proved source-time allowance 22*P*I + 62*P + 16*I + 87; task-time bound 31*n + 87. The round replaces the base by the chosen row (canonical greedy), unlike the upstream coordinatewise-minimum variant. Author: Joshua Wharton (QFEX); adapted from shreshth-s/thin-matrix-results and the anthropics/formal-math Light framework; packaged and verified by darkhipo.

/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>

The canonical greedy selection round in the Light language: a fixed six-procedure
program that computes candidate scores, selects a remaining minimum-score
candidate, copies its complete row into the base buffer, and clears exactly that
candidate's remaining flag.  Proved source-time allowance for the round:
`22 * P * I + 62 * P + 16 * I + 87` (DenseCanonicalSelectionRound.time_eq), and
`time_le_taskTime` bounds it by `31 * n + 87` on the shape size.

Adapted from shreshth-s/thin-matrix-results, DenseSelectionRound.lean at
225c37476e31bdb27594953cc1f7738496fb4afc.  The Light language, its proof rules
and the verified copying primitive are from the Apache-2.0 anthropics/formal-math
dependency (ThreeSumApsp submission), whose attribution is retained below.
Packaged for prove2.me by the BigO strike, 2026-10-29.

This definition carries the Light proof layer (rules, frames, calls, pass, copy)
and the machine programs with their execution contracts.  The Light *definitions*
(language syntax, ends, regions, tasks) come from the published platform
definitions APSPSource_ThreeSumApsp_Lang_Syntax/Logic/Regions, whose declared
names correspond exactly to the source's `Light.*` declarations.
-/

import Mathlib

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Light proof rules (Logic layer) -/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

theorem Ends.whileStep {σ c s T} {Q : State → Prop} (T₁ T₂ : ℕ) (hs : c.Safe lim σ) (hc : c.Holds σ)
    (h : Ends lim P d s σ T₁ fun σ' => Ends lim P d (.while c s) σ' T₂ Q)
    (hT : c.cost + 1 + T₁ + T₂ ≤ T) : Ends lim P d (.while c s) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .whileTrue hs hc he₁ he₂, by omega, hq⟩

theorem Ends.whileDone {σ c s T} {Q : State → Prop} (hs : c.Safe lim σ) (hc : ¬ c.Holds σ)
    (hQ : Q σ) (hT : c.cost + 1 ≤ T) : Ends lim P d (.while c s) σ T Q :=
  ⟨σ, _, .whileFalse hs hc, hT, hQ⟩

theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h

theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

theorem Cond.holds_le {σ : State} {a b : Expr} : (a ≤' b).Holds σ ↔ a.val σ ≤ b.val σ :=
  Int.lt_add_one_iff

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame



@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

end Light

/-! ## Memory regions (Regions layer) -/

namespace Light

variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl

theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl

theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)

theorem SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)

theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)

theorem SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := fun c hc => by
  rw [Function.update_of_ne (by rintro rfl; exact hb hc)]; exact h c hc

variable {dst j : ℕ} {f : ℕ → ℤ}

theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

theorem wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]

theorem sameOutside_wrote {n : ℕ} (h : j ≤ n) : SameOutside μ (wrote μ dst f j) dst n :=
  fun _ hb => wrote_rest (by omega)





end Light

/-! ## Assignments -/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

@[simp] def Stmt.assigns : Stmt → List ℕ
  | .skip => []
  | .set x _ => [x]
  | .store _ _ => []
  | .seq s t => s.assigns ++ t.assigns
  | .ite _ s t => s.assigns ++ t.assigns
  | .while _ s => s.assigns
  | .call _ _ x => [x]

theorem Exec.loc_eq_of_notMem_assigns {s : Stmt} {σ σ' : State} {c y : ℕ}
    (h : Exec lim P d s σ σ' c) (hy : y ∉ s.assigns) : σ'.loc y = σ.loc y := by
  induction h with
  | skip => rfl
  | set _ => exact Function.update_of_ne (by simpa using hy) _ _
  | store _ _ _ => rfl
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ fun h => hy (List.mem_append_right _ h)).trans
      (ih₁ fun h => hy (List.mem_append_left _ h))
  | iteTrue _ _ _ ih => exact ih fun h => hy (List.mem_append_left _ h)
  | iteFalse _ _ _ ih => exact ih fun h => hy (List.mem_append_right _ h)
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => exact (ih₂ hy).trans (ih₁ hy)
  | call _ _ _ _ _ => exact Function.update_of_ne (by simpa using hy) _ _

theorem Ends.keeping {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ s.assigns, σ'.loc y = σ.loc y := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc, hq, fun _ hy => he.loc_eq_of_notMem_assigns hy⟩

theorem Ends.keepingBut {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (xs : List ℕ) (hxs : s.assigns ⊆ xs := by simp) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ xs, σ'.loc y = σ.loc y :=
  h.keeping.mono le_rfl fun _ hq => ⟨hq.1, fun y hy => hq.2 y fun hmem => hy (hxs hmem)⟩

end Light

/-! ## Rules for blocks and loops -/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

instance Cond.decidableHolds (σ : State) : (c : Cond) → Decidable (c.Holds σ)
  | .lt a b => inferInstanceAs (Decidable (a.val σ < b.val σ))
  | .eq a b => inferInstanceAs (Decidable (a.val σ = b.val σ))

@[simp] def Stmt.after : Stmt → State → State
  | .set x e, σ => { σ with loc := Function.update σ.loc x (e.val σ) }
  | .store a e, σ => { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
  | .seq s t, σ => t.after (s.after σ)
  | .ite c s t, σ => if c.Holds σ then s.after σ else t.after σ
  | _, σ => σ

@[simp] def Stmt.blockCost : Stmt → ℕ
  | .set _ e => e.cost + 1
  | .store a e => a.cost + e.cost + 1
  | .seq s t => s.blockCost + t.blockCost
  | .ite c s t => c.cost + 1 + max s.blockCost t.blockCost
  | _ => 0

@[simp] def Stmt.BlockSafe (lim : Limits) : Stmt → State → Prop
  | .skip, _ => True
  | .set _ e, σ => e.Safe lim σ
  | .store a e, σ => a.Safe lim σ ∧ e.Safe lim σ ∧ lim.Addr (a.val σ)
  | .seq s t, σ => s.BlockSafe lim σ ∧ t.BlockSafe lim (s.after σ)
  | .ite c s t, σ =>
    c.Safe lim σ ∧ (c.Holds σ → s.BlockSafe lim σ) ∧ (¬ c.Holds σ → t.BlockSafe lim σ)
  | _, _ => False

abbrev Stmt.Runs (lim : Limits) (s : Stmt) (σ : State) (R : State → Prop) : Prop :=
  s.BlockSafe lim σ ∧ R (s.after σ)






theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R)
    (hR : ∀ σ', R σ' → R' σ') : s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩

theorem Stmt.Runs.seq {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ fun σ' => t.Runs lim σ' R) : (s ;; t).Runs lim σ R :=
  ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem Stmt.Runs.ite_pos {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ R) (hc : c.Holds σ := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hs : c.Safe lim σ := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun _ => h.1, fun hn => absurd hc hn⟩, by simpa only [Stmt.after, if_pos hc] using h.2⟩

theorem Stmt.Runs.ite_neg {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : t.Runs lim σ R) (hc : ¬ c.Holds σ := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hs : c.Safe lim σ := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun hp => absurd hp hc, fun _ => h.1⟩, by simpa only [Stmt.after, if_neg hc] using h.2⟩

theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s ;; .skip) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  h

theorem Ends.setLast {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {Q : State → Prop}
    (h : Q ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩)
    (hs : e.Safe lim ⟨loc, μ⟩ := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hT : e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set hs hT h

theorem Ends.setThen {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩ (T - (e.cost + 1)) Q)
    (hs : e.Safe lim ⟨loc, μ⟩ := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hT : e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.set x e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.set hs le_rfl h) hT

theorem Ends.storeLast {loc μ : ℕ → ℤ} {T : ℕ} {a e : Expr} {Q : State → Prop}
    (h : Q ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : a.cost + e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) : Ends lim P d (.store a e) ⟨loc, μ⟩ T Q :=
  Ends.store hs.1 hs.2.1 hs.2.2 hT h

theorem Ends.storeThen {loc μ : ℕ → ℤ} {T : ℕ} {a e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩
      (T - (a.cost + e.cost + 1)) Q)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : a.cost + e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.store a e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.storeLast h hs le_rfl) hT

theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hT : c.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d (s₁ ;; s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d (s₂ ;; s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hT : c.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.ite c s₁ s₂ ;; s) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩

abbrev Stmt.for (i : ℕ) (hi : Expr) (body : Stmt) : Stmt :=
  .set i (k 0) ;; .while (v i <' hi) (body ;; .set i (v i +' k 1))

theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (v i +' k 1).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(v i +' k 1).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

end Light

/-! ## Local variables as a list -/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

@[simp] def setLocal : List ℤ → ℕ → ℤ → List ℤ
  | [], 0, z => [z]
  | [], x + 1, z => 0 :: setLocal [] x z
  | _ :: l, 0, z => z :: l
  | a :: l, x + 1, z => a :: setLocal l x z

theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]

theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

@[simp] def Expr.Gives (lim : Limits) (σ : State) (e : Expr) (z : ℤ) : Prop :=
  e.Safe lim σ ∧ e.val σ = z

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}

theorem Ends.setVal {loc : ℕ → ℤ} {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨Function.update loc x z, μ⟩)
    (he : e.Gives lim ⟨loc, μ⟩ z := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hT : e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set he.1 hT (he.2 ▸ h)

theorem Ends.setValThen {loc : ℕ → ℤ} {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨Function.update loc x z, μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨loc, μ⟩ z := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hT : e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.set x e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.setVal z h he le_rfl) hT

theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT

theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : a.cost + e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : a.cost + e.cost + 1 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.store a e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT

theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI

theorem Ends.forShape {β : Type} {loc : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt}
    (S : ℕ → β → (ℕ → ℤ) → State) (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (s₀ : β) (start : I 0 μ)
    (round : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body (S j s μ') b fun σ' => ∃ s' μ'', σ' = S j s' μ'' ∧ I (j + 1) μ'')
    (done : ∀ (s : β) (μ' : ℕ → ℤ), I n μ' → Q (S n s μ'))
    (first : (⟨Function.update loc i 0, μ⟩ : State) = S 0 s₀ μ := by
      first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (bound : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j ≤ n → I j μ' → hi.Gives lim (S j s μ') n := by
      intros; simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (counter : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), (S j s μ').loc i = j := by intros; simp)
    (next : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ),
      (⟨Function.update (S j s μ').loc i ((j : ℤ) + 1), (S j s μ').mem⟩ : State) =
        S (j + 1) s μ' := by
      intros; first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ' => ∃ s μ', σ' = S j s μ' ∧ I j μ') n b ⟨s₀, μ, first, start⟩ ?_ ?_ ?_
    hn hT
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    refine (round j s μ' hj hI).mono le_rfl ?_
    rintro _ ⟨s', μ'', rfl, hI'⟩
    exact ⟨counter j s' μ'', s', μ'', next j s' μ'', hI'⟩
  · rintro _ - ⟨s, μ', rfl, hI⟩
    exact done s μ' hI
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    exact bound j s μ' hj hI

end rules

@[simp] def setLocals (l : List ℤ) : List (ℕ × ℤ) → List ℤ
  | [] => l
  | p :: ps => setLocals (setLocal l p.1 p.2) ps

@[simp] def updateLocals (loc : ℕ → ℤ) : List (ℕ × ℤ) → ℕ → ℤ
  | [] => loc
  | p :: ps => updateLocals (Function.update loc p.1 p.2) ps

@[simp] def refreshLocals (l : List ℤ) (loc : ℕ → ℤ) : List ℕ → List ℤ
  | [] => l
  | x :: xs => refreshLocals (setLocal l x (loc x)) loc xs

section

variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}

end

end Light

/-! ## Default-proof tactics -/

namespace Light







end Light

/-! ## Specifications of procedures -/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

def Meets (lim : Limits) (P : Program) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (T : ℕ)
    (R : ℤ → (ℕ → ℤ) → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧ Ends lim P d body ⟨frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem

section

variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

end

section

variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT

theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (.call p args x ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

/-! ## Segments -/

namespace Light

def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]

variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

end Light

/-! ## A pass over an array -/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

abbrev pass (c : ℕ) (len dst e : Expr) : Stmt := Stmt.for c len (.store (dst +' v c) e)

variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : Seg (wrote μ dst f n) dst l := fun i hi => by
  rw [wrote_done (hl ▸ hi), h i hi]

theorem Ends.pass {c x y n T : ℕ} {e : Expr} {loc : ℕ → ℤ} {Q : State → Prop} (f : ℕ → ℤ)
    (round : ∀ j < n, e.Safe lim ⟨Function.update loc c j, wrote μ dst f j⟩ ∧
      e.val ⟨Function.update loc c j, wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, wrote μ dst f n⟩)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) (hlen : loc x = n)
    (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega))) :
    Ends lim P d (pass c (v x) (v y) e) ⟨loc, μ⟩ T Q := by
  refine Ends.forMem (fun j μ' => μ' = wrote μ dst f j) n _ wrote_zero.symm
    (fun j μ' hj hμ' => Ends.block ?round le_rfl)
    (fun μ' h => by rw [h]; exact done)
    (fun j μ' _ _ => ⟨trivial, (Function.update_of_ne hx _ _).trans hlen⟩) (by omega)
    (le_trans (le_of_eq (by simp only [Stmt.blockCost, Expr.cost]; ring)) hT)
  -- Round j: dst[j] := e.
  subst hμ'
  obtain ⟨hs, hv⟩ := round j hj
  have qc : Function.update loc c (j : ℤ) c = j := Function.update_self ..
  have qy : Function.update loc c (j : ℤ) y = dst := by rw [Function.update_of_ne hy, haddr]
  refine ⟨⟨?_, hs, ?_⟩, rfl, ?_⟩
  · simp only [Expr.Safe, Expr.val, Op.eval, qc, qy, true_and, abs_le]
    omega
  · simp only [Expr.val, Op.eval, qc, qy, Limits.Addr]
    omega
  · simp only [Stmt.after, Expr.val, Op.eval, qc, qy, hv, toNat_natCast_add_natCast, wrote_succ]

end Light

/-! ## Copying and filling a segment -/

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Copy

abbrev Src : ℕ := 0

@[inherit_doc Src] abbrev Dst : ℕ := 1

@[inherit_doc Src] abbrev Len : ℕ := 2

@[inherit_doc Src] abbrev Idx : ℕ := 3

end Copy

open Copy in

def copyBody : Stmt := pass Idx (v Len) (v Dst) (M (v Src +' v Idx))

@[simp] def copyTime (n : ℕ) : ℕ := 16 * n + 6

theorem copy_meets {p : ℕ} (hp : P[p]? = some copyBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : Apart src n dst n) :
    Meets lim P p d [(src : ℤ), dst, n] μ (copyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass (fun i => μ (src + i)) (fun i hi => ?_)
    ⟨fun i hi => wrote_done (f := fun i => μ (src + i)) hi, by (unfold SameOutside wrote; intro b hb; simp only [Function.update_apply, wrote] at *; omega)⟩ hw hdst rfl rfl
    (hT := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, copyTime]; first | omega | (ring_nf; omega)) | omega | (simp [copyTime] <;> first | omega | (ring_nf; omega))))
  -- Round i reads src[i], which no earlier round has written.
  have hread : wrote μ dst (fun i => μ (src + i)) i (src + i) = μ (src + i) :=
    wrote_rest (by omega)
  simp [Limits.Addr, abs_le, -abs_mul, hread] <;> omega

namespace Fill

abbrev Dst : ℕ := 0

@[inherit_doc Dst] abbrev Len : ℕ := 1

@[inherit_doc Dst] abbrev Val : ℕ := 2

@[inherit_doc Dst] abbrev Idx : ℕ := 3

end Fill

open Fill in

def fillBody : Stmt := pass Idx (v Len) (v Dst) (v Val)

@[simp] def fillTime (n : ℕ) : ℕ := 13 * n + 6

theorem fill_meets {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n :=
  .of_body hp (Ends.pass (fun _ => x) (fun i hi => by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by (unfold SameOutside wrote; intro b hb; simp only [Function.update_apply, wrote] at *; omega)⟩
    hw hdst rfl rfl (hT := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fillTime]; first | omega | (ring_nf; omega)) | omega | (simp [fillTime] <;> first | omega | (ring_nf; omega))))

end Light

/-! ## Tasks and solvers -/

namespace Light

structure Need : Type where
  word : ℕ
  cells : ℕ
  depth : ℕ

structure Need.Ok (r : Need) (lim : Limits) (fr d : ℕ) : Prop where
  word : (r.word : ℤ) ≤ lim.word
  cells : fr + r.cells ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + r.depth ≤ lim.depth

structure Task : Type 1 where
  /-- The instances, as they lie in the memory: sizes, bound, addresses, contents. -/
  Inst : Type
  /-- The size of an instance. -/
  size : Inst → ℕ
  /-- The bound on the absolute values of its numbers that is handed to the solver. -/
  bound : Inst → ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → (ℕ → ℤ) → ℕ → Prop
  /-- The result and the final memory are right.  (That the cells below the free pointer are
  otherwise unchanged is part of this.) -/
  Post : Inst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop

def Solves (task : Task) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need) : Prop :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : ℕ → ℤ) (fr : ℕ), task.Pre x μ fr →
      (need (task.size x) (task.bound x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩
        (T (task.size x) (task.bound x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem

noncomputable def timeUpTo (Tn : ℕ → ℕ → ℕ) (n : ℕ) (u : ℝ) : ℝ :=
  ((Finset.range (⌊u⌋₊ + 1)).sup (Tn n) : ℕ)

end Light

/-! ## Active-row score (machine) -/

namespace Light.DenseScorePass

abbrev Len : ℕ := 0

abbrev Height : ℕ := 1

abbrev Active : ℕ := 2

abbrev Row : ℕ := 3

abbrev Idx : ℕ := 4

abbrev Acc : ℕ := 5

def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

def roundBody : Stmt :=
  .ite (M (v Active +' v Idx) =' k 1)
    (.set Acc (v Acc +' M (v Row +' v Idx)))
    .skip

def body : Stmt :=
  .set Acc (k 0) ;; .for Idx (v Len) roundBody ;; .set Len (v Acc)

def score (active : ℕ → Bool) (row : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => score active row j + if active j then row j else 0

theorem score_bound {active : ℕ → Bool} {row : ℕ → ℕ} {I h : ℕ}
    (hrow : ∀ i < I, row i ≤ h) : ∀ j ≤ I, score active row j ≤ j * h := by
  intro j
  induction j with
  | zero => simp [score]
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    have hr : (if active j then row j else 0) ≤ h := by
      split_ifs
      · exact hrow j (by omega)
      · exact Nat.zero_le _
    simpa only [score, Nat.succ_mul] using Nat.add_le_add hs hr

theorem round_cost : roundBody.blockCost = 14 := by rfl

theorem loop_ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {active : ℕ → Bool} {row : ℕ → ℕ}
    {I h ab rb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hrow : ∀ i < I, row i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + I ≤ lim.space) :
    Ends lim P d (.for Idx (v Len) roundBody)
      ⟨frame [I, h, ab, rb, 0, 0], μ⟩ (22 * I + 6)
      (fun σ => σ = ⟨frame [I, h, ab, rb, I, score active row I], μ⟩) := by
  refine Ends.for
    (fun j σ => σ = ⟨frame [I, h, ab, rb, j, score active row j], μ⟩)
    I roundBody.blockCost ?start ?round ?done ?bound
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case start => simp [update_frame_setLocal, score]
  case round =>
    intro j σ hj _ hσ
    subst σ
    have hra := ha j hj
    have hrr := hr j hj
    have hscore : ((score active row (j + 1) : ℕ) : ℤ) ≤ lim.word := by
      have hb := score_bound (active := active) hrow (j + 1) (by omega)
      have hm : (j + 1) * h ≤ I * h := Nat.mul_le_mul_right h (by omega)
      exact le_trans (by exact_mod_cast hb.trans hm) hsum
    unfold roundBody
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    · have hac : active j = true := by simpa [hra] using hc
      have heq : score active row (j + 1) = score active row j + row j := by
        simp [score, hac]
      refine Ends.setTo (score active row (j + 1) : ℕ) ?_ ?_ (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
      · exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add]⟩
      · simp [Limits.Addr, abs_le, -abs_mul, hrr, heq] <;> omega
    · have hac : active j ≠ true := by simpa [hra] using hc
      have heq : score active row (j + 1) = score active row j := by
        simp [score, hac]
      apply Ends.skip
      exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, heq]⟩
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    intro j σ hj _ hσ
    subst σ
    simp [Limits.Addr, abs_le, -abs_mul] <;> omega

theorem ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {active : ℕ → Bool} {row : ℕ → ℕ}
    {I h ab rb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hrow : ∀ i < I, row i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + I ≤ lim.space) :
    Ends lim P d body ⟨frame [I, h, ab, rb], μ⟩ (22 * I + 10)
      (fun σ => σ.loc 0 = score active row I ∧ σ.mem = μ) := by
  unfold body
  refine Ends.setToThen (0 : ℕ) ?_ (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
  refine Ends.next (22 * I + 6) ?_ (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
  refine (loop_ends ha hr hrow hw h1 hsum hab hrb).mono le_rfl ?_
  intro σ hσ
  subst σ
  refine Ends.setTo (score active row I : ℕ) ?_ (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
  exact ⟨by simp, rfl⟩

theorem meets {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {row : ℕ → ℕ}
    {I h ab rb : ℕ}
    (ha : ∀ i < I, μ (ab + i) = bit (active i))
    (hr : ∀ i < I, μ (rb + i) = row i)
    (hrow : ∀ i < I, row i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + I ≤ lim.space) :
    Meets lim P p d [I, h, ab, rb] μ (22 * I + 10) fun result μ' =>
      result = score active row I ∧ μ' = μ := by
  exact .of_body hbody (ends ha hr hrow hw h1 hsum hab hrb)

end Light.DenseScorePass

/-! ## Remaining argmin scan (machine) -/

namespace Light.DenseArgminPass

abbrev Len : ℕ := 0

abbrev MaxScore : ℕ := 1

abbrev Remain : ℕ := 2

abbrev Scores : ℕ := 3

abbrev Idx : ℕ := 4

abbrev BestIdx : ℕ := 5

abbrev BestScore : ℕ := 6

def bit (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by
  cases b <;> simp [bit]

def roundBody : Stmt :=
  .ite (M (v Remain +' v Idx) =' k 1)
    (.ite (M (v Scores +' v Idx) <' v BestScore)
      (.set BestIdx (v Idx) ;; .set BestScore (M (v Scores +' v Idx)))
      .skip)
    .skip

def body : Stmt :=
  .set BestIdx (k 0) ;;
  .set BestScore (v MaxScore +' k 1) ;;
  .for Idx (v Len) roundBody ;;
  .set Len (v BestIdx)

def scan (remaining : ℕ → Bool) (scores : ℕ → ℕ) (H : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, H + 1)
  | j + 1 =>
      let old := scan remaining scores H j
      if remaining j = true ∧ scores j < old.2 then (j, scores j) else old

def ScanSpec (remaining : ℕ → Bool) (scores : ℕ → ℕ) (H j : ℕ) : Prop :=
  (scan remaining scores H j).2 ≤ H + 1 ∧
  (((scan remaining scores H j).2 = H + 1 ∧ (scan remaining scores H j).1 = 0) ∨
    ((scan remaining scores H j).1 < j ∧
      remaining (scan remaining scores H j).1 = true ∧
      (scan remaining scores H j).2 = scores (scan remaining scores H j).1)) ∧
  (∀ q < j, remaining q = true → (scan remaining scores H j).2 ≤ scores q)

theorem scan_spec {remaining : ℕ → Bool} {scores : ℕ → ℕ} {H N : ℕ}
    (hscores : ∀ q < N, scores q ≤ H) : ∀ j ≤ N, ScanSpec remaining scores H j := by
  intro j
  induction j with
  | zero => simp [ScanSpec, scan]
  | succ j ih =>
    intro hj
    have hi := ih (by omega)
    rcases hi with ⟨hbound, hwitness, hlower⟩
    by_cases hu : remaining j = true ∧ scores j < (scan remaining scores H j).2
    · simp only [ScanSpec, scan, if_pos hu]
      refine ⟨?_, Or.inr ⟨by omega, hu.1, True.intro⟩, ?_⟩
      · have := hscores j (by omega)
        omega
      · intro q hq hrem
        by_cases heq : q = j
        · subst q
          exact le_rfl
        · exact hu.2.le.trans (hlower q (by omega) hrem)
    · simp only [ScanSpec, scan, if_neg hu]
      refine ⟨hbound, ?_, ?_⟩
      · rcases hwitness with hw | ⟨hb, hr, hs⟩
        · exact Or.inl hw
        · exact Or.inr ⟨by omega, hr, hs⟩
      · intro q hq hrem
        by_cases heq : q = j
        · subst q
          have hn : ¬ scores j < (scan remaining scores H j).2 := by
            intro hh
            exact hu ⟨hrem, hh⟩
          omega
        · exact hlower q (by omega) hrem

def IsArgmin (remaining : ℕ → Bool) (scores : ℕ → ℕ) (N p : ℕ) : Prop :=
  p < N ∧ remaining p = true ∧ ∀ q < N, remaining q = true → scores p ≤ scores q

theorem scan_isArgmin {remaining : ℕ → Bool} {scores : ℕ → ℕ} {H N : ℕ}
    (hscores : ∀ q < N, scores q ≤ H)
    (hne : ∃ q, q < N ∧ remaining q = true) :
    IsArgmin remaining scores N (scan remaining scores H N).1 := by
  obtain ⟨q, hq, hrem⟩ := hne
  obtain ⟨_, hwitness, hlower⟩ := scan_spec (remaining := remaining) hscores N le_rfl
  rcases hwitness with ⟨hsentinel, _⟩ | ⟨hp, hr, hs⟩
  · have := hlower q hq hrem
    have := hscores q hq
    omega
  · refine ⟨hp, hr, ?_⟩
    intro r hrr hremain
    rw [← hs]
    exact hlower r hrr hremain

theorem round_cost : roundBody.blockCost = 21 := by rfl

theorem loop_ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {scores : ℕ → ℕ}
    {N H rb sb : ℕ}
    (hr : ∀ i < N, μ (rb + i) = bit (remaining i))
    (hs : ∀ i < N, μ (sb + i) = scores i)
    (hscores : ∀ i < N, scores i ≤ H)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hrb : rb + N ≤ lim.space) (hsb : sb + N ≤ lim.space) :
    Ends lim P d (.for Idx (v Len) roundBody)
      ⟨frame [N, H, rb, sb, 0, 0, H + 1], μ⟩ (29 * N + 6)
      (fun σ => σ = ⟨frame [N, H, rb, sb, N,
        (scan remaining scores H N).1, (scan remaining scores H N).2], μ⟩) := by
  refine Ends.for
    (fun j σ => σ = ⟨frame [N, H, rb, sb, j,
      (scan remaining scores H j).1, (scan remaining scores H j).2], μ⟩)
    N roundBody.blockCost ?start ?round ?done ?bound
    (hn := by omega) (hT := by simp [round_cost]; omega)
  case start => simp [update_frame_setLocal, scan]
  case round =>
    intro j σ hj _ hσ
    subst σ
    have hrr := hr j hj
    have hrs := hs j hj
    have hwordScore : (scores j : ℤ) ≤ lim.word := by
      have := hscores j hj
      omega
    unfold roundBody
    refine Ends.iteLast (fun hcR => ?_) (fun hcR => ?_) (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
    · have hR : remaining j = true := by simpa [hrr] using hcR
      refine Ends.iteLast (fun hcS => ?_) (fun hcS => ?_) (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega)
      · have hS : scores j < (scan remaining scores H j).2 := by
          exact_mod_cast (show (scores j : ℤ) < (scan remaining scores H j).2 by
            simpa [hrs] using hcS)
        have hnext : scan remaining scores H (j + 1) = (j, scores j) := by
          simp [scan, hR, hS]
        refine Ends.setToThen (j : ℕ) ?_ (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
        refine Ends.setTo (scores j : ℕ) ?_ (by simp [Limits.Addr, abs_le, -abs_mul, hrs] <;> omega) (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
        exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
      · have hS : ¬ scores j < (scan remaining scores H j).2 := by
          intro hh
          apply hcS
          have : (scores j : ℤ) < (scan remaining scores H j).2 := by exact_mod_cast hh
          simpa [hrs] using this
        have hnext : scan remaining scores H (j + 1) = scan remaining scores H j := by
          simp [scan, hS]
        apply Ends.skip
        exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
    · have hR : remaining j ≠ true := by simpa [hrr] using hcR
      have hnext : scan remaining scores H (j + 1) = scan remaining scores H j := by
        simp [scan, hR]
      apply Ends.skip
      exact ⟨by simp, by simp [update_frame_setLocal, Nat.cast_add, hnext]⟩
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    intro j σ hj _ hσ
    subst σ
    simp [Limits.Addr, abs_le, -abs_mul] <;> omega

theorem ends {lim : Limits} {P : Program} {d : ℕ}
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {scores : ℕ → ℕ}
    {N H rb sb : ℕ}
    (hr : ∀ i < N, μ (rb + i) = bit (remaining i))
    (hs : ∀ i < N, μ (sb + i) = scores i)
    (hscores : ∀ i < N, scores i ≤ H)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hrb : rb + N ≤ lim.space) (hsb : sb + N ≤ lim.space) :
    Ends lim P d body ⟨frame [N, H, rb, sb], μ⟩ (29 * N + 14)
      (fun σ => σ.loc 0 = (scan remaining scores H N).1 ∧ σ.mem = μ) := by
  unfold body
  refine Ends.setToThen (0 : ℕ) ?_ (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
  refine Ends.setToThen (H + 1 : ℕ) ?_ (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
  refine Ends.next (29 * N + 6) ?_ (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
  refine (loop_ends hr hs hscores hw h1 hsentinel hrb hsb).mono le_rfl ?_
  intro σ hσ
  subst σ
  refine Ends.setTo ((scan remaining scores H N).1 : ℕ) ?_ (by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
  exact ⟨by simp, rfl⟩

theorem meets {lim : Limits} {P : Program} {d p : ℕ}
    (hbody : P[p]? = some body)
    {μ : ℕ → ℤ} {remaining : ℕ → Bool} {scores : ℕ → ℕ}
    {N H rb sb : ℕ}
    (hr : ∀ i < N, μ (rb + i) = bit (remaining i))
    (hs : ∀ i < N, μ (sb + i) = scores i)
    (hscores : ∀ i < N, scores i ≤ H)
    (hne : ∃ q, q < N ∧ remaining q = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hsentinel : ((H + 1 : ℕ) : ℤ) ≤ lim.word)
    (hrb : rb + N ≤ lim.space) (hsb : sb + N ≤ lim.space) :
    Meets lim P p d [N, H, rb, sb] μ (29 * N + 14) fun result μ' =>
      μ' = μ ∧ ∃ chosen : ℕ, result = chosen ∧ IsArgmin remaining scores N chosen := by
  refine .of_body hbody ?_
  refine (ends hr hs hscores hw h1 hsentinel hrb hsb).mono le_rfl ?_
  intro σ hσ
  exact ⟨hσ.2, (scan remaining scores H N).1, hσ.1, scan_isArgmin hscores hne⟩

end Light.DenseArgminPass

/-! ## Cached-score table pass (machine) -/

namespace Light.DenseScoreTablePass

abbrev Candidates : ℕ := 0

abbrev Len : ℕ := 1

abbrev Height : ℕ := 2

abbrev Active : ℕ := 3

abbrev Rows : ℕ := 4

abbrev Out : ℕ := 5

abbrev Candidate : ℕ := 6

abbrev Score : ℕ := 7

def roundBody (scoreProc : ℕ) : Stmt :=
  .call scoreProc [v Len, v Height, v Active, v Rows +' v Candidate *' v Len] Score ;;
  .store (v Out +' v Candidate) (v Score)

def body (scoreProc : ℕ) : Stmt := .for Candidate (v Candidates) (roundBody scoreProc)

def scores (active : ℕ → Bool) (rows : ℕ → ℕ → ℕ) (I p : ℕ) : ℕ :=
  DenseScorePass.score active (rows p) I

def time (P I : ℕ) : ℕ := P * (22 * I + 33) + 6

theorem ends {lim : Limits} {Prog : Program} {d scoreProc : ℕ}
    (hscore : Prog[scoreProc]? = some DenseScorePass.body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I h ab rb out : ℕ} (fr : ℤ)
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word) (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + P * I ≤ lim.space)
    (hout : out + P ≤ lim.space)
    (hsepA : Apart ab I out P) (hsepR : Apart rb (P * I) out P)
    (hdepth : d < lim.depth) :
    Ends lim Prog d (body scoreProc) ⟨frame [P, I, h, ab, rb, out, fr], μ⟩
      (time P I) fun σ =>
        σ.mem = wrote μ out (fun p => (scores active rows I p : ℤ)) P := by
  unfold body time
  refine Ends.forShape
    (fun p (z : ℤ) μ' => ⟨frame [P, I, h, ab, rb, out, p, z], μ'⟩)
    (fun p μ' => μ' = wrote μ out (fun p => (scores active rows I p : ℤ)) p)
    P (22 * I + 25) 0 wrote_zero.symm ?round ?done
    (first := by
      simp only [update_frame_setLocal, setLocal]
      congr 1
      exact (frame_append_zeros [P, I, h, ab, rb, out, 0] 1).symm)
    (hn := by omega) (hT := by simp only [Expr.cost]; ring_nf; omega)
  case round =>
    intro p z μ' hp hμ
    have hra : ∀ i < I, μ' (ab + i) = DenseScorePass.bit (active i) := by
      intro i hi
      rw [hμ, wrote_rest (by rcases hsepA with hs | hs <;> omega)]
      exact ha i hi
    have hrp : ∀ i < I, μ' (rb + p * I + i) = rows p i := by
      intro i hi
      have hpi : p * I + i < P * I := by nlinarith
      rw [hμ, wrote_rest (by rcases hsepR with hs | hs <;> omega)]
      exact hr p hp i hi
    have hrowp := hrow p hp
    have hrowaddr : rb + p * I + I ≤ lim.space := by
      have : (p + 1) * I ≤ P * I := Nat.mul_le_mul_right I (by omega)
      nlinarith
    have hmul : ((p * I : ℕ) : ℤ) ≤ lim.word := by
      have : p * I ≤ P * I := Nat.mul_le_mul_right I hp.le
      omega
    have hrowbase : ((rb + p * I : ℕ) : ℤ) ≤ lim.word := by omega
    have hval : ((scores active rows I p : ℕ) : ℤ) ≤ lim.word := by
      have hb : scores active rows I p ≤ I * h := DenseScorePass.score_bound hrowp I le_rfl
      exact (by exact_mod_cast hb : (scores active rows I p : ℤ) ≤ (I * h : ℕ)).trans hsum
    unfold roundBody
    refine Ends.callToThen
      (DenseScorePass.meets hscore hra hrp hrowp hw h1 hsum hab hrowaddr)
      (fun r μ'' hresult => ?_)
      (ha := by simp [Limits.Addr, abs_le, -abs_mul, Nat.cast_add, Nat.cast_mul] <;> omega)
      (hd := hdepth) (hT := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))
    obtain ⟨hresult, rfl⟩ := hresult
    change r = (scores active rows I p : ℤ) at hresult
    subst r
    (focus ((first | refine Ends.seqSelf ?_ | refine Ends.skipLast ?_); repeat with_unfolding_none first | refine Ends.seqAssoc ?_ | refine Ends.skipThen ?_); (refine Ends.storeToThen (out + p) (scores active rows I p) ?_ ?_ ?_); (on_goal -1 => (first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; first | omega | (ring_nf; omega)) | omega | (simp [] <;> first | omega | (ring_nf; omega)))); (on_goal -1 => (simp [Limits.Addr, abs_le, -abs_mul] <;> omega)); (try with_unfolding_none refine Ends.skip ?_))
    refine ⟨(scores active rows I p : ℤ),
      Function.update μ'' (out + p) (scores active rows I p : ℤ), ?_, ?_⟩
    · rfl
    · rw [hμ]
      exact wrote_succ
  case done =>
    intro z μ' hμ
    exact hμ

theorem meets {lim : Limits} {Prog : Program} {d proc scoreProc : ℕ}
    (hbody : Prog[proc]? = some (body scoreProc))
    (hscore : Prog[scoreProc]? = some DenseScorePass.body)
    {μ : ℕ → ℤ} {active : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I h ab rb out : ℕ} (fr : ℤ)
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word) (hsum : ((I * h : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + P * I ≤ lim.space)
    (hout : out + P ≤ lim.space)
    (hsepA : Apart ab I out P) (hsepR : Apart rb (P * I) out P)
    (hdepth : d < lim.depth) :
    Meets lim Prog proc d [P, I, h, ab, rb, out, fr] μ (time P I) fun _ μ' =>
      SameOutside μ μ' out P ∧ ∀ p < P,
        μ' (out + p) = (scores active rows I p : ℤ) ∧ scores active rows I p ≤ I * h := by
  refine .of_body hbody ?_
  refine (ends hscore fr ha hr hrow hw h1 hh hsum hab hrb hout hsepA hsepR hdepth).mono
    le_rfl ?_
  intro σ hσ
  rw [hσ]
  refine ⟨sameOutside_wrote le_rfl, ?_⟩
  intro p hp
  exact ⟨wrote_done hp, DenseScorePass.score_bound (hrow p hp) I le_rfl⟩

namespace Selection

def body (tableProc argminProc : ℕ) : Stmt :=
  .call tableProc [v 0, v 1, v 2, v 3, v 4, v 5, v 7] 8 ;;
  .call argminProc [v 0, v 1 *' v 2, v 6, v 5] 0

def time (P I : ℕ) : ℕ := DenseScoreTablePass.time P I + 29 * P + 31

theorem ends {lim : Limits} {Prog : Program} {d tableProc scoreProc argminProc : ℕ}
    (htable : Prog[tableProc]? = some (DenseScoreTablePass.body scoreProc))
    (hscore : Prog[scoreProc]? = some DenseScorePass.body)
    (hargmin : Prog[argminProc]? = some DenseArgminPass.body)
    {μ : ℕ → ℤ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I h ab rb out rem fr : ℕ}
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hne : ∃ p, p < P ∧ remaining p = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word)
    (hsentinel : ((I * h + 1 : ℕ) : ℤ) ≤ lim.word)
    (hab : ab + I ≤ lim.space) (hrb : rb + P * I ≤ lim.space)
    (hout : out + P ≤ lim.space) (hremb : rem + P ≤ lim.space)
    (_hfr : fr ≤ lim.space)
    (hsepA : Apart ab I out P) (hsepR : Apart rb (P * I) out P)
    (hsepRem : Apart rem P out P) (hdepth : d + 2 ≤ lim.depth) :
    Ends lim Prog d (body tableProc argminProc)
      ⟨frame [P, I, h, ab, rb, out, rem, fr], μ⟩ (time P I) fun σ =>
        SameOutside μ σ.mem out P ∧
        (∀ p < P, σ.mem (out + p) = (scores active rows I p : ℤ)) ∧
        ∃ chosen : ℕ, σ.loc 0 = chosen ∧
          DenseArgminPass.IsArgmin remaining (scores active rows I) P chosen := by
  have hsum : ((I * h : ℕ) : ℤ) ≤ lim.word := by omega
  unfold body
  refine Ends.callToThen
    (DenseScoreTablePass.meets htable hscore (fr : ℤ) ha hr hrow hw h1 hh hsum
      hab hrb hout hsepA hsepR (by omega))
    (fun r μ' htableResult => ?_)
    (ha := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hd := by omega) (hT := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]; first | omega | (ring_nf; omega)) | omega | (simp [time] <;> first | omega | (ring_nf; omega)))
  obtain ⟨hkeep, hscores⟩ := htableResult
  have hr' : ∀ p < P, μ' (rem + p) = DenseArgminPass.bit (remaining p) := by
    intro p hp
    rw [hkeep (rem + p) (by rcases hsepRem with hs | hs <;> omega)]
    exact hrem p hp
  refine Ends.callTo
    (DenseArgminPass.meets hargmin hr' (fun p hp => (hscores p hp).1)
      (fun p hp => (hscores p hp).2) hne hw h1 hsentinel hremb hout)
    (fun result μ'' hresult => ?_)
    (ha := by simp [Limits.Addr, abs_le, -abs_mul, Nat.cast_mul] <;> omega) (hd := by omega)
    (hT := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]; first | omega | (ring_nf; omega)) | omega | (simp [time] <;> first | omega | (ring_nf; omega)))
  obtain ⟨rfl, chosen, hresult, hchosen⟩ := hresult
  exact ⟨hkeep, fun p hp => (hscores p hp).1, chosen, by simpa using hresult, hchosen⟩

end Selection

end Light.DenseScoreTablePass

/-! ## Canonical greedy selection round (machine) -/

namespace Light.DenseCanonicalSelectionRound

abbrev Candidates : ℕ := 0

abbrev Len : ℕ := 1

abbrev Height : ℕ := 2

abbrev Active : ℕ := 3

abbrev Rows : ℕ := 4

abbrev Scores : ℕ := 5

abbrev Remaining : ℕ := 6

abbrev Base : ℕ := 7

abbrev Free : ℕ := 8

abbrev Chosen : ℕ := 9

abbrev Unused : ℕ := 10

def body (selectionProc copyProc : ℕ) : Stmt :=
  .call selectionProc
    [v Candidates, v Len, v Height, v Active, v Rows, v Scores, v Remaining, v Free] Chosen ;;
  .call copyProc [v Rows +' v Chosen *' v Len, v Base, v Len] Unused ;;
  .store (v Remaining +' v Chosen) (k 0) ;;
  .set Candidates (v Chosen)

def time (P I : ℕ) : ℕ := DenseScoreTablePass.Selection.time P I + 16 * I + 50

def Result (μ : ℕ → ℤ) (active remaining : ℕ → Bool)
    (rows : ℕ → ℕ → ℕ) (P I sb mb rem : ℕ)
    (r : ℤ) (μ' : ℕ → ℤ) : Prop :=
  SameOutside3 μ μ' sb P mb I rem P ∧
  (∀ p < P, μ' (sb + p) = (DenseScoreTablePass.scores active rows I p : ℤ)) ∧
  ∃ chosen : ℕ, r = chosen ∧
    DenseArgminPass.IsArgmin remaining (DenseScoreTablePass.scores active rows I) P chosen ∧
    (∀ i < I, μ' (mb + i) = (rows chosen i : ℕ)) ∧
    (∀ p < P, μ' (rem + p) =
      DenseArgminPass.bit (if p = chosen then false else remaining p))

theorem ends {lim : Limits} {Prog : Program} {d sel table score argmin update : ℕ}
    (hsel : Prog[sel]? = some (DenseScoreTablePass.Selection.body table argmin))
    (htable : Prog[table]? = some (DenseScoreTablePass.body score))
    (hscore : Prog[score]? = some DenseScorePass.body)
    (hargmin : Prog[argmin]? = some DenseArgminPass.body)
    (hupdate : Prog[update]? = some copyBody)
    {μ : ℕ → ℤ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I h ab rb sb rem mb fr : ℕ}
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hne : ∃ p, p < P ∧ remaining p = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word) (hsentinel : ((I * h + 1 : ℕ) : ℤ) ≤ lim.word)
    (hlayout : InOrder lim.space [(ab,I),(rb,P*I),(sb,P),(mb,I),(rem,P)])
    (hfr : fr ≤ lim.space) (hdepth : d + 3 ≤ lim.depth) :
    Ends lim Prog d (body sel update)
      ⟨frame [P,I,h,ab,rb,sb,rem,mb,fr], μ⟩ (time P I)
      fun σ => Result μ active remaining rows P I sb mb rem (σ.loc 0) σ.mem := by
  rcases hlayout with ⟨hAR,hRS,hSM,hMR,hend⟩
  have hab : ab + I ≤ lim.space := by omega
  have hrb : rb + P * I ≤ lim.space := by omega
  have hsb : sb + P ≤ lim.space := by omega
  have hmb : mb + I ≤ lim.space := by omega
  have hSel : Meets lim Prog sel (d+1) [P,I,h,ab,rb,sb,rem,fr] μ
      (DenseScoreTablePass.Selection.time P I) (fun r μ' =>
        SameOutside μ μ' sb P ∧
        (∀ p < P, μ' (sb+p) = (DenseScoreTablePass.scores active rows I p : ℤ)) ∧
        ∃ chosen : ℕ, r = chosen ∧
          DenseArgminPass.IsArgmin remaining (DenseScoreTablePass.scores active rows I) P chosen) := by
    exact Meets.of_body hsel (DenseScoreTablePass.Selection.ends htable hscore hargmin
      ha hr hrow hrem hne hw h1 hh hsentinel hab hrb hsb hend hfr
      (by left; omega) (by left; omega) (by right; omega) (by omega))
  unfold body
  refine Ends.callToThen hSel (fun r μ₁ hselResult => ?_)
    (ha := by simp [Limits.Addr, abs_le, -abs_mul] <;> omega) (hd := by omega) (hT := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]; first | omega | (ring_nf; omega)) | omega | (simp [time] <;> first | omega | (ring_nf; omega)))
  obtain ⟨same₁,scores₁,chosen,rfl,hchosen⟩ := hselResult
  have hc : chosen < P := hchosen.1
  have hprod : (chosen + 1) * I ≤ P * I := Nat.mul_le_mul_right I hc
  have hr₁ : ∀ i < I, μ₁ (rb + chosen * I + i) = rows chosen i := by
    intro i hi
    have hpi : chosen * I + i < P * I := by nlinarith [hchosen.1]
    exact (same₁ _ (by left; omega)).trans (hr chosen hchosen.1 i hi)
  have hchosenRow : rb + chosen * I + I ≤ lim.space := by
    have : (chosen + 1) * I ≤ P * I := Nat.mul_le_mul_right I hchosen.1
    nlinarith
  have hmul : ((chosen * I : ℕ) : ℤ) ≤ lim.word := by
    have : chosen * I ≤ P * I := Nat.mul_le_mul_right I hchosen.1.le
    omega
  have hrowbase : ((rb + chosen * I : ℕ) : ℤ) ≤ lim.word := by omega
  refine Ends.callToThen
    (copy_meets hupdate hw hchosenRow hmb (by left; nlinarith))
    (fun _ μ₂ hupdateResult => ?_)
    (ha := by simp [Limits.Addr, abs_le, -abs_mul, Nat.cast_add, Nat.cast_mul] <;> omega) (hd := by omega)
    (hT := by first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]; first | omega | (ring_nf; omega)) | omega | (simp [time] <;> first | omega | (ring_nf; omega)))
  obtain ⟨copied₂,same₂⟩ := hupdateResult
  have hchosenAddr : rem + chosen < lim.space := by omega
  have hchosenWord : (chosen : ℤ) ≤ lim.word := by omega
  (focus ((first | refine Ends.seqSelf ?_ | refine Ends.skipLast ?_); repeat with_unfolding_none first | refine Ends.seqAssoc ?_ | refine Ends.skipThen ?_); (refine Ends.storeToThen (rem + chosen) (0 : ℤ) ?_ ?_ ?_); (on_goal -1 => (first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]; first | omega | (ring_nf; omega)) | omega | (simp [time] <;> first | omega | (ring_nf; omega)))); (on_goal -1 => (simp [Limits.Addr, abs_le, -abs_mul, time] <;> omega)); (try with_unfolding_none refine Ends.skip ?_))
  (focus ((first | refine Ends.seqSelf ?_ | refine Ends.skipLast ?_); repeat with_unfolding_none first | refine Ends.seqAssoc ?_ | refine Ends.skipThen ?_); (refine Ends.setToThen (chosen : ℤ) ?_ ?_ ?_); (on_goal -1 => (first | (simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, time]; first | omega | (ring_nf; omega)) | omega | (simp [time] <;> first | omega | (ring_nf; omega)))); (on_goal -1 => (simp [Limits.Addr, abs_le, -abs_mul, time] <;> omega)); (try with_unfolding_none refine Ends.skip ?_))
  change Result μ active remaining rows P I sb mb rem (chosen : ℤ)
    (Function.update μ₂ (rem + chosen) 0)
  refine ⟨?_,?_,chosen,rfl,hchosen,?_,?_⟩
  · intro x hx
    rw [Function.update_of_ne (by rcases hx.2.2 with h | h <;> omega)]
    exact (same₂ x hx.2.1).trans (same₁ x hx.1)
  · intro p hp
    rw [Function.update_of_ne (by omega)]
    exact (same₂ _ (by left; omega)).trans (scores₁ p hp)
  · intro i hi
    rw [Function.update_of_ne (by omega)]
    exact (copied₂ i hi).trans (hr₁ i hi)
  · intro p hp
    by_cases heq : p = chosen
    · subst p
      simp [DenseArgminPass.bit]
    · rw [if_neg heq, Function.update_of_ne (by omega)]
      exact (same₂ _ (by right; omega)).trans
        ((same₁ _ (by right; omega)).trans (hrem p hp))

def program : Program :=
  [DenseScorePass.body, DenseScoreTablePass.body 0, DenseArgminPass.body,
    DenseScoreTablePass.Selection.body 1 2, copyBody, body 3 4]

theorem meets {lim : Limits} {d : ℕ}
    {μ : ℕ → ℤ} {active remaining : ℕ → Bool} {rows : ℕ → ℕ → ℕ}
    {P I h ab rb sb rem mb fr : ℕ}
    (ha : ∀ i < I, μ (ab + i) = DenseScorePass.bit (active i))
    (hr : ∀ p < P, ∀ i < I, μ (rb + p * I + i) = rows p i)
    (hrow : ∀ p < P, ∀ i < I, rows p i ≤ h)
    (hrem : ∀ p < P, μ (rem + p) = DenseArgminPass.bit (remaining p))
    (hne : ∃ p, p < P ∧ remaining p = true)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : 1 ≤ lim.word)
    (hh : (h : ℤ) ≤ lim.word) (hsentinel : ((I * h + 1 : ℕ) : ℤ) ≤ lim.word)
    (hlayout : InOrder lim.space [(ab,I),(rb,P*I),(sb,P),(mb,I),(rem,P)])
    (hfr : fr ≤ lim.space) (hdepth : d + 3 ≤ lim.depth) :
    Meets lim program 5 d [P,I,h,ab,rb,sb,rem,mb,fr] μ (time P I)
      (Result μ active remaining rows P I sb mb rem) := by
  exact Meets.of_body rfl (ends (Prog:=program) rfl rfl rfl rfl rfl
    ha hr hrow hrem hne hw h1 hh hsentinel hlayout hfr hdepth)

theorem time_eq (P I : ℕ) :
    time P I = 22 * P * I + 62 * P + 16 * I + 87 := by
  unfold time DenseScoreTablePass.Selection.time DenseScoreTablePass.time
  ring

theorem time_le_controller_visits (P I : ℕ) (hP : 0 < P) :
    time P I ≤ 25 * (P * I + 6 * P + I) := by
  rw [time_eq]
  simp only [Nat.mul_assoc]
  omega

structure Instance where
  candidates : ℕ
  length : ℕ
  height : ℕ
  activeBase : ℕ
  rowsBase : ℕ
  scoresBase : ℕ
  remainingBase : ℕ
  baseBase : ℕ
  active : ℕ → Bool
  remaining : ℕ → Bool
  rows : ℕ → ℕ → ℕ

def instanceSize (x : Instance) : ℕ :=
  x.candidates * x.length + 2 * x.candidates + 2 * x.length

structure Pre (x : Instance) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  active_read : ∀ i < x.length,
    μ (x.activeBase+i) = DenseScorePass.bit (x.active i)
  rows_read : ∀ p < x.candidates, ∀ i < x.length,
    μ (x.rowsBase+p*x.length+i) = x.rows p i
  rows_bound : ∀ p < x.candidates, ∀ i < x.length, x.rows p i ≤ x.height
  remaining_read : ∀ p < x.candidates,
    μ (x.remainingBase+p) = DenseArgminPass.bit (x.remaining p)
  nonempty : ∃ p, p < x.candidates ∧ x.remaining p = true
  layout : InOrder fr [(x.activeBase,x.length),
    (x.rowsBase,x.candidates*x.length),(x.scoresBase,x.candidates),
    (x.baseBase,x.length),(x.remainingBase,x.candidates)]

def task : Task where
  Inst := Instance
  size := instanceSize
  bound x := x.height
  args x := [x.candidates,x.length,x.height,x.activeBase,x.rowsBase,
    x.scoresBase,x.remainingBase,x.baseBase]
  Pre := Pre
  Post x μ _ := Result μ x.active x.remaining x.rows
    x.candidates x.length x.scoresBase x.baseBase x.remainingBase

def need (n U : ℕ) : Need where
  word := (n+1)*(U+1)+1
  cells := 0
  depth := 3

def taskTime (n _U : ℕ) : ℕ := 31*n+87

theorem time_le_taskTime (x : Instance) :
    time x.candidates x.length ≤ taskTime (instanceSize x) x.height := by
  rw [time_eq]
  unfold taskTime instanceSize
  nlinarith

end Light.DenseCanonicalSelectionRound


