-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunFormalOK2
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRunFormalOK2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:30.753082+00:00
-- url     : https://prove2.me/theorems/e9cd4f74-17c3-4aa4-a679-9072f77df632
-- title:
--   RunsOK and E0 packaging for OneRun2 net0O
-- statement:
--   # OneRun2 RunsOK / E0 feed
--
--   Finite channel-edge family $E_0$ for corrected `OneRunNet2.ch0O`, with `EdgeQ` witnesses via `pickE`/`dfltE`, yielding $\mathrm{RunsOK}(\mathrm{net0O})$. Used by OneRun2 EOKO edge-matrix packaging.
--
--   **Formalization Note.** Namespace `IntMul.Kappa.R8.Bit.Oppbank.OneRunFormalOK2`.
-- source:
--   OneRunFormalOK 58816888 retarget to OneRun2 e0d447f6

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option linter.dupNamespace false

/-!
# OneRunFormalOK2 — RunsOK / EdgesOK packaging for `OneRunNet2.net0O`

Finite edge family `E0` of `OneRunNet2.ch0O`, `EdgeQ` via `pickE`/`dfltE`,
`runsOK0`, and `EdgesOK_large` through R6 `good_edges`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunFormalOK2

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB hiding codeBound net0 ch0 dfltE pickE S0 Si0
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open AModel AModelFac Matrix Finset

noncomputable abbrev ch0 : Pnd.Ch := OneRunNet2.ch0O

theorem codeBound_eq : OneRunNet2.codeBound = 64251 := rfl

theorem pswQ_zero {m : ℕ} : pswQ (0 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  unfold pswQ
  rw [sub_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem dfltE_Q : EdgeQ OneRunNet2.dfltE 0 := by
  refine ⟨fun ρ h => absurd h List.not_mem_nil, fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
    fun i => by rw [show OneRunNet2.dfltE.E₁ = 1 from rfl, Matrix.one_apply_eq]; exact one_ne_zero,
    fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
    fun i => by rw [show OneRunNet2.dfltE.E₂ = 1 from rfl, Matrix.one_apply_eq]; exact one_ne_zero, ?_⟩
  rw [pswQ_zero]
  show (1 : QMat2 529) * (([] : List (Fin (529 + 529) × Fin (529 + 529))).map
    fun p => Equiv.swap p.1 p.2).prod.permMatrix ℚ * 1 = 1
  simp

theorem pickE_spec {P : Edge 529 → Prop} (h : ∃ e, P e) : P (OneRunNet2.pickE P) := by
  unfold OneRunNet2.pickE; rw [dif_pos h]; exact Classical.choose_spec h

theorem pickE_Q (q : Matrix (Fin 529) (Fin 529) ℚ) (R : List (ℕ × ℕ × ℕ) → Prop) :
    ∃ q', EdgeQ (OneRunNet2.pickE (OneRunNet2.PE q R)) q' := by
  by_cases h : ∃ e, OneRunNet2.PE q R e
  · exact ⟨q, (pickE_spec h).1⟩
  · unfold OneRunNet2.pickE; rw [dif_neg h]; exact ⟨0, dfltE_Q⟩

noncomputable instance instDecEqEdge529 : DecidableEq (Edge 529) := Classical.decEq _

def I3P : Finset (ℕ × ℕ × ℕ) :=
  Finset.range 1771 ×ˢ (Finset.range OneRunNet2.codeBound ×ˢ Finset.range OneRunNet2.codeBound)

def I2P : Finset (ℕ × ℕ) := Finset.range 1771 ×ˢ Finset.range 1771

attribute [irreducible] I3P I2P

noncomputable def E0 : Finset (Edge 529) :=
  (I3P.image fun p => ch0.e1 p.1 p.2.1 p.2.2) ∪
    (I3P.image fun p => ch0.e2 p.1 p.2.1 p.2.2) ∪
    ((Finset.range v).image ch0.ex) ∪
    (I2P.image fun p => ch0.en p.1 p.2) ∪
    ((Finset.range v).image ch0.ei) ∪
    (I2P.image fun p => ch0.ec p.1 p.2) ∪ {OneRunNet2.dfltE}

attribute [irreducible] E0
attribute [local semireducible] E0 I3P I2P

theorem mem_I3P (p : ℕ × ℕ × ℕ) :
    p ∈ I3P ↔ p.1 < 1771 ∧ p.2.1 < 64251 ∧ p.2.2 < 64251 := by
  unfold I3P
  rw [Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range, Finset.mem_range]
  change _ ↔ p.1 < 1771 ∧ p.2.1 < OneRunNet2.codeBound ∧ p.2.2 < OneRunNet2.codeBound
  simp only [OneRunNet2.codeBound]

theorem mem_I2P (p : ℕ × ℕ) : p ∈ I2P ↔ p.1 < 1771 ∧ p.2 < 1771 := by
  unfold I2P
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]

attribute [local irreducible] I3P I2P

theorem dflt_mem : OneRunNet2.dfltE ∈ E0 := by
  rw [E0, Finset.mem_union]; exact Or.inr (Finset.mem_singleton_self _)

theorem e1_mem (b o c : ℕ) : ch0.e1 b o c ∈ E0 := by
  by_cases h : b < v ∧ o < OneRunNet2.codeBound ∧ c < OneRunNet2.codeBound
  · have hv : b < 1771 := by simpa [v] using h.1
    have : (b, o, c) ∈ I3P := (mem_I3P _).2 ⟨hv, by simpa [OneRunNet2.codeBound] using h.2.1,
      by simpa [OneRunNet2.codeBound] using h.2.2⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(b, o, c), this, rfl⟩)))))
  · have heq : ch0.e1 b o c = OneRunNet2.dfltE := by
      change (if b < v ∧ o < OneRunNet2.codeBound ∧ c < OneRunNet2.codeBound then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem e2_mem (a o c : ℕ) : ch0.e2 a o c ∈ E0 := by
  by_cases h : a < v ∧ o < OneRunNet2.codeBound ∧ c < OneRunNet2.codeBound
  · have hv : a < 1771 := by simpa [v] using h.1
    have : (a, o, c) ∈ I3P := (mem_I3P _).2 ⟨hv, by simpa [OneRunNet2.codeBound] using h.2.1,
      by simpa [OneRunNet2.codeBound] using h.2.2⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, o, c), this, rfl⟩)))))
  · have heq : ch0.e2 a o c = OneRunNet2.dfltE := by
      change (if a < v ∧ o < OneRunNet2.codeBound ∧ c < OneRunNet2.codeBound then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ex_mem (b : ℕ) : ch0.ex b ∈ E0 := by
  by_cases h : b < v
  · have hv : b < 1771 := by simpa [v] using h
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨b, Finset.mem_range.2 hv, rfl⟩))))
  · have heq : ch0.ex b = OneRunNet2.dfltE := by
      change (if b < v then _ else _) = _; rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem en_mem (a t : ℕ) : ch0.en a t ∈ E0 := by
  by_cases h : a < v ∧ t < v
  · have ha : a < 1771 := by simpa [v] using h.1
    have ht : t < 1771 := by simpa [v] using h.2
    have : (a, t) ∈ I2P := (mem_I2P _).2 ⟨ha, ht⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, t), this, rfl⟩)))
  · have heq : ch0.en a t = OneRunNet2.dfltE := by
      change (if a < v ∧ t < v then _ else _) = _; rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ei_mem (a : ℕ) : ch0.ei a ∈ E0 := by
  by_cases h : a < v
  · have hv : a < 1771 := by simpa [v] using h
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inr ⟨a, Finset.mem_range.2 hv, rfl⟩))
  · have heq : ch0.ei a = OneRunNet2.dfltE := by
      change (if a < v then _ else _) = _; rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ec_mem (a s : ℕ) : ch0.ec a s ∈ E0 := by
  by_cases h : a < v ∧ s < v
  · have ha : a < 1771 := by simpa [v] using h.1
    have hs : s < 1771 := by simpa [v] using h.2
    have : (a, s) ∈ I2P := (mem_I2P _).2 ⟨ha, hs⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inr ⟨(a, s), this, rfl⟩)
  · have heq : ch0.ec a s = OneRunNet2.dfltE := by
      change (if a < v ∧ s < v then _ else _) = _; rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem E0_Q : ∀ e ∈ E0, ∃ q, EdgeQ e q := by
  have k : ∀ (P : Prop) [Decidable P] (q : Matrix (Fin 529) (Fin 529) ℚ)
      (R : List (ℕ × ℕ × ℕ) → Prop),
      ∃ q', EdgeQ (if P then OneRunNet2.pickE (OneRunNet2.PE q R) else OneRunNet2.dfltE) q' := by
    intro P _ q R
    split_ifs
    · exact pickE_Q q R
    · exact ⟨0, dfltE_Q⟩
  intro e he
  simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at he
  rcases he with (((((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) |
    ⟨p, -, rfl⟩) | rfl
  · simp only [ch0, OneRunNet2.ch0O]; exact k _ _ _
  · simp only [ch0, OneRunNet2.ch0O]; exact k _ _ _
  · simp only [ch0, OneRunNet2.ch0O]; exact k _ _ _
  · simp only [ch0, OneRunNet2.ch0O]; exact k _ _ _
  · simp only [ch0, OneRunNet2.ch0O]; exact k _ _ _
  · simp only [ch0, OneRunNet2.ch0O]; exact k _ _ _
  · exact ⟨0, dfltE_Q⟩

attribute [local irreducible] E0

def Fam (ch : NB.Ch) (e : Edge 529) : Prop :=
  (∃ b o c, e = ch.e1 b o c) ∨ (∃ a o c, e = ch.e2 a o c) ∨ (∃ b, e = ch.ex b) ∨
    (∃ a t, e = ch.en a t) ∨ (∃ a, e = ch.ei a) ∨ (∃ a s, e = ch.ec a s)

theorem chunk_edges {ι : ℕ → Wr} {E : ℕ → ℕ → Edge 529} {cs : List LChunk}
    {i : Instr Wr (ZMod 2) 529}
    (hi : i ∈ chunkProg ι E cs) {e : Edge 529} (he : i.edgeOf = some e) :
    ∃ o c, e = E o c := by
  unfold chunkProg at hi
  obtain ⟨chk, -, hi⟩ := List.mem_flatMap.1 hi
  unfold chunkInstrs at hi
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨mv, -, rfl⟩ := List.mem_map.1 hi
    exact ⟨mv.2, chk.1, (Option.some.inj he).symm⟩
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hi
    have h0 : (xorG (ι p.1) (ι p.2) : Instr Wr (ZMod 2) 529).edgeOf = none := rfl
    rw [h0] at he
    cases he

theorem xorG_edgeOf (d s : Wr) : (xorG d s : NI).edgeOf = none := rfl

theorem prog_fam (ch : NB.Ch) : ∀ e ∈ (net ch).edges, Fam ch e := by
  intro e he
  obtain ⟨i, hi, hie⟩ := List.mem_filterMap.1 he
  change i ∈ (List.range v).flatMap (blk1 ch) ++ (List.range v).flatMap (blk2 ch) at hi
  rcases List.mem_append.1 hi with hi | hi
  · obtain ⟨b, -, hi⟩ := List.mem_flatMap.1 hi
    unfold blk1 at hi
    rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨o, c, rfl⟩ := chunk_edges hi hie
      exact Or.inl ⟨b, o, c, rfl⟩
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hi
      exact Or.inr (Or.inr (Or.inl ⟨b, (Option.some.inj hie).symm⟩))
  · obtain ⟨a, -, hi⟩ := List.mem_flatMap.1 hi
    unfold blk2 at hi
    rcases List.mem_append.1 hi with hi | hi
    · unfold entI at hi
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hi
      have he' : e = entE ch a w := (Option.some.inj hie).symm
      unfold entE at he'
      split_ifs at he'
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, w, he'⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, w - v, he'⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, he'⟩))))
    rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨o, c, rfl⟩ := chunk_edges hi hie
      exact Or.inr (Or.inl ⟨a, o, c, rfl⟩)
    · obtain ⟨s, -, hi⟩ := List.mem_flatMap.1 hi
      unfold corrI at hi
      rcases List.mem_cons.1 hi with rfl | hi
      · have h0 : (xorG (ι2 a (wU s)) (ι2 a (wY s)) : NI).edgeOf = none := rfl
        rw [h0] at hie; cases hie
      rcases List.mem_cons.1 hi with rfl | hi
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, s, (Option.some.inj hie).symm⟩))))
      rcases List.mem_cons.1 hi with rfl | hi
      · rw [xorG_edgeOf] at hie; cases hie
      · exact absurd hi List.not_mem_nil

theorem edges_E0 : ∀ e ∈ net0O.edges, e ∈ E0 := by
  intro e he
  have he' : e ∈ (net (OneRunNet2.toNB ch0)).edges := he
  rcases prog_fam (OneRunNet2.toNB ch0) e he' with
    ⟨b, o, c, rfl⟩ | ⟨a, o, c, rfl⟩ | ⟨b, rfl⟩ | ⟨a, t, rfl⟩ | ⟨a, rfl⟩ | ⟨a, s, rfl⟩
  · simpa [OneRunNet2.toNB] using e1_mem b o c
  · simpa [OneRunNet2.toNB] using e2_mem a o c
  · simpa [OneRunNet2.toNB] using ex_mem b
  · simpa [OneRunNet2.toNB] using en_mem a t
  · simpa [OneRunNet2.toNB] using ei_mem a
  · simpa [OneRunNet2.toNB] using ec_mem a s

theorem runsOK0 : net0O.RunsOK := by
  intro e he ρ hρ
  obtain ⟨q, hq⟩ := E0_Q e (edges_E0 e he)
  exact hq.1 ρ hρ

theorem net0O_RunsOK : RunsOK (m := 529) net0O := runsOK0

theorem EdgesOK_of_good_primes (q₀ : ℕ)
    (h : ∀ q, q.Prime → q₀ < q → ∀ f, ∀ e ∈ E0, EdgeOK (q ^ f) e)
    {q : ℕ} (hq : q.Prime) (hlt : q₀ < q) (f : ℕ) :
    EdgesOK (m := 529) net0O (q ^ f) :=
  fun e he => h q hq hlt f e (edges_E0 e he)

/-- Packaging hook: RunsOK of `OneRunNet2.net0O` (EdgesOK via `good_edges` in solutions). -/
theorem net0O_runs :
    ∃ _q₀ : ℕ, RunsOK (m := 529) net0O :=
  ⟨0, net0O_RunsOK⟩

end IntMul.Kappa.R8.Bit.Oppbank.OneRunFormalOK2


