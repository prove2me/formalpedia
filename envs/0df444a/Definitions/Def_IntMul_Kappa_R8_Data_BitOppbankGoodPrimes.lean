-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimes
-- name    : IntMul_Kappa_R8_Data_BitOppbankGoodPrimes
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:23:18.103257+00:00
-- url     : https://prove2.me/theorems/fac3e30f-7d4f-4f5b-ad1d-a9dcd30f6476
-- title:
--   R8 good_primes/FormalOK retarget codeBound=64251 + Net0P RunsOK
-- statement:
--   Retarget of Defs52 `good_primes` / `FormalOK` packaging to densified opp-bank alphabet $\mathrm{codeBound}=64251$ on published `Net0P` ($373d80bb$).
--
--   Self-contained finite edge family $E_0$ with `EdgeQ` coverage yields
--   $$\mathrm{RunsOK}(\mathrm{net0P}).$$
--   Also records
--   $$M_0=\{P_c:c<64251\}\cup\{P_T:T<1771\},\qquad EM_0=\{E_1(e),E_2(e):e\in E_0\}$$
--   and statements `GoodPrimesStmt` / `Net0OkStmt` for EdgesOK/FormalOK once platform `good_edges`/`good_mats` and densified `Pnd` land.
-- source:
--   Net0P 373d80bb; ProjB b18c4ed9; QHNet 52d9e9e0; NetMom 84ad4683

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# R8 good_primes / FormalOK retarget at `codeBound = 64251`

Self-contained `E0` / `EdgeQ` / `runsOK0` for published `Net0P` (`373d80bb`),
Defs52 packs `M0`/`EM0`, and `GoodPrimesStmt`/`Net0OkStmt` packaging toward
`/verify` `oppbank_net`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.GoodPrimes

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.ProjB
open IntMul.Kappa.R8.Bit.Oppbank.Net0P
open IntMul.Kappa.R8.Bit.Oppbank.NB hiding codeBound net0 ch0 dfltE pickE S0 Si0
open Matrix Finset

noncomputable abbrev ch0 : ProjB.Ch := ProjB.ch0P

theorem codeBound_eq : ProjB.codeBound = 64251 := rfl

theorem pswQ_zero {m : ℕ} : pswQ (0 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  unfold pswQ
  rw [sub_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem dfltE_Q : EdgeQ ProjB.dfltE 0 := by
  refine ⟨fun ρ h => absurd h List.not_mem_nil, fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
    fun i => by rw [show ProjB.dfltE.E₁ = 1 from rfl, Matrix.one_apply_eq]; exact one_ne_zero,
    fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
    fun i => by rw [show ProjB.dfltE.E₂ = 1 from rfl, Matrix.one_apply_eq]; exact one_ne_zero, ?_⟩
  rw [pswQ_zero]
  show (1 : QMat2 529) * (([] : List (Fin (529 + 529) × Fin (529 + 529))).map
    fun p => Equiv.swap p.1 p.2).prod.permMatrix ℚ * 1 = 1
  simp

theorem pickE_spec {P : Edge 529 → Prop} (h : ∃ e, P e) : P (ProjB.pickE P) := by
  unfold ProjB.pickE; rw [dif_pos h]; exact Classical.choose_spec h

theorem pickE_Q (q : Matrix (Fin 529) (Fin 529) ℚ) (R : List (ℕ × ℕ × ℕ) → Prop) :
    ∃ q', EdgeQ (ProjB.pickE (PE q R)) q' := by
  by_cases h : ∃ e, PE q R e
  · exact ⟨q, (pickE_spec h).1⟩
  · unfold ProjB.pickE; rw [dif_neg h]; exact ⟨0, dfltE_Q⟩

/-! ## Finite edge set E0 at densified codeBound -/

attribute [local semireducible] IntMul.Kappa.R8.Bit.Oppbank.ProjB.I3
attribute [local semireducible] IntMul.Kappa.R8.Bit.Oppbank.ProjB.I2


noncomputable instance instDecEqEdge529 : DecidableEq (Edge 529) := Classical.decEq _

noncomputable def E0 : Finset (Edge 529) :=
  (I3.image fun p => ch0.e1 p.1 p.2.1 p.2.2) ∪
    (I3.image fun p => ch0.e2 p.1 p.2.1 p.2.2) ∪
    ((Finset.range v).image ch0.ex) ∪
    (I2.image fun p => ch0.en p.1 p.2) ∪
    ((Finset.range v).image ch0.ei) ∪
    (I2.image fun p => ch0.ec p.1 p.2) ∪ {ProjB.dfltE}

theorem mem_I3 (p : ℕ × ℕ × ℕ) :
    p ∈ I3 ↔ p.1 < 1771 ∧ p.2.1 < 64251 ∧ p.2.2 < 64251 := by
  unfold I3
  rw [Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range, Finset.mem_range]
  change _ ↔ p.1 < 1771 ∧ p.2.1 < ProjB.codeBound ∧ p.2.2 < ProjB.codeBound
  simp only [ProjB.codeBound]

theorem mem_I2 (p : ℕ × ℕ) : p ∈ I2 ↔ p.1 < 1771 ∧ p.2 < 1771 := by
  unfold I2
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]

attribute [local irreducible] IntMul.Kappa.R8.Bit.Oppbank.ProjB.I3
attribute [local irreducible] IntMul.Kappa.R8.Bit.Oppbank.ProjB.I2
attribute [irreducible] E0

attribute [local semireducible] E0

theorem dflt_mem : ProjB.dfltE ∈ E0 := by
  rw [E0, Finset.mem_union]; exact Or.inr (Finset.mem_singleton_self _)

theorem e1_mem (b o c : ℕ) : ch0.e1 b o c ∈ E0 := by
  by_cases h : b < v ∧ o < ProjB.codeBound ∧ c < ProjB.codeBound
  · have hv : b < 1771 := by simpa [v] using h.1
    have : (b, o, c) ∈ I3 := (mem_I3 _).2 ⟨hv, h.2.1, h.2.2⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(b, o, c), this, rfl⟩)))))
  · have heq : ch0.e1 b o c = ProjB.dfltE := by
      change (if b < v ∧ o < ProjB.codeBound ∧ c < ProjB.codeBound then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem e2_mem (a o c : ℕ) : ch0.e2 a o c ∈ E0 := by
  by_cases h : a < v ∧ o < ProjB.codeBound ∧ c < ProjB.codeBound
  · have hv : a < 1771 := by simpa [v] using h.1
    have : (a, o, c) ∈ I3 := (mem_I3 _).2 ⟨hv, h.2.1, h.2.2⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, o, c), this, rfl⟩)))))
  · have heq : ch0.e2 a o c = ProjB.dfltE := by
      change (if a < v ∧ o < ProjB.codeBound ∧ c < ProjB.codeBound then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ex_mem (b : ℕ) : ch0.ex b ∈ E0 := by
  by_cases h : b < v
  · have hv : b < 1771 := by simpa [v] using h
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨b, Finset.mem_range.2 hv, rfl⟩))))
  · have heq : ch0.ex b = ProjB.dfltE := by
      change (if b < v then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem en_mem (a t : ℕ) : ch0.en a t ∈ E0 := by
  by_cases h : a < v ∧ t < v
  · have ha : a < 1771 := by simpa [v] using h.1
    have ht : t < 1771 := by simpa [v] using h.2
    have : (a, t) ∈ I2 := (mem_I2 _).2 ⟨ha, ht⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, t), this, rfl⟩)))
  · have heq : ch0.en a t = ProjB.dfltE := by
      change (if a < v ∧ t < v then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ei_mem (a : ℕ) : ch0.ei a ∈ E0 := by
  by_cases h : a < v
  · have hv : a < 1771 := by simpa [v] using h
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inr ⟨a, Finset.mem_range.2 hv, rfl⟩))
  · have heq : ch0.ei a = ProjB.dfltE := by
      change (if a < v then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ec_mem (a s : ℕ) : ch0.ec a s ∈ E0 := by
  by_cases h : a < v ∧ s < v
  · have ha : a < 1771 := by simpa [v] using h.1
    have hs : s < 1771 := by simpa [v] using h.2
    have : (a, s) ∈ I2 := (mem_I2 _).2 ⟨ha, hs⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inr ⟨(a, s), this, rfl⟩)
  · have heq : ch0.ec a s = ProjB.dfltE := by
      change (if a < v ∧ s < v then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem E0_Q : ∀ e ∈ E0, ∃ q, EdgeQ e q := by
  have k : ∀ (P : Prop) [Decidable P] (q : Matrix (Fin 529) (Fin 529) ℚ)
      (R : List (ℕ × ℕ × ℕ) → Prop),
      ∃ q', EdgeQ (if P then ProjB.pickE (PE q R) else ProjB.dfltE) q' := by
    intro P _ q R
    split_ifs
    · exact pickE_Q q R
    · exact ⟨0, dfltE_Q⟩
  intro e he
  simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at he
  rcases he with (((((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) |
    ⟨p, -, rfl⟩) | rfl
  · -- e1
    simp only [ch0, ProjB.ch0P]
    exact k _ _ _
  · simp only [ch0, ProjB.ch0P]; exact k _ _ _
  · simp only [ch0, ProjB.ch0P]; exact k _ _ _
  · simp only [ch0, ProjB.ch0P]; exact k _ _ _
  · simp only [ch0, ProjB.ch0P]; exact k _ _ _
  · simp only [ch0, ProjB.ch0P]; exact k _ _ _
  · exact ⟨0, dfltE_Q⟩

attribute [local irreducible] E0

/-! ## Every program edge is a chosen family; RunsOK -/

def Fam (ch : IntMul.Kappa.R8.Bit.Oppbank.NB.Ch) (e : Edge 529) : Prop :=
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

theorem prog_fam (ch : IntMul.Kappa.R8.Bit.Oppbank.NB.Ch) :
    ∀ e ∈ (net ch).edges, Fam ch e := by
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

theorem edges_E0 : ∀ e ∈ net0P.edges, e ∈ E0 := by
  intro e he
  have he' : e ∈ (net (Net0P.toNB ch0)).edges := he
  rcases prog_fam (Net0P.toNB ch0) e he' with
    ⟨b, o, c, rfl⟩ | ⟨a, o, c, rfl⟩ | ⟨b, rfl⟩ | ⟨a, t, rfl⟩ | ⟨a, rfl⟩ | ⟨a, s, rfl⟩
  · simpa [Net0P.toNB] using e1_mem b o c
  · simpa [Net0P.toNB] using e2_mem a o c
  · simpa [Net0P.toNB] using ex_mem b
  · simpa [Net0P.toNB] using en_mem a t
  · simpa [Net0P.toNB] using ei_mem a
  · simpa [Net0P.toNB] using ec_mem a s

/-- **RunsOK piece of `net0_ok`**: every run on `net0P` is `RunOK`
(via `E0` + `EdgeQ`; `pickE` defaults to `dfltE` when `PE` is vacant). -/
theorem runsOK0 : net0P.RunsOK := by
  intro e he ρ hρ
  obtain ⟨q, hq⟩ := E0_Q e (edges_E0 e he)
  exact hq.1 ρ hρ

theorem net0P_RunsOK : RunsOK (m := 529) net0P := runsOK0
theorem net0_RunsOK : RunsOK (m := 529) Net0P.net0 := runsOK0

/-! ## Finite packs at densified codeBound -/

noncomputable def M0 : Finset M23 :=
  (Finset.range ProjB.codeBound).image Pc ∪ (Finset.range v).image Pl

noncomputable def EM0 : Finset (QMat2 529) :=
  E0.image Edge.E₁ ∪ E0.image Edge.E₂

theorem mem_M0_Pc {c : ℕ} (hc : c < ProjB.codeBound) : Pc c ∈ M0 := by
  unfold M0
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hc))

theorem mem_M0_Pl {b : ℕ} (hb : b < v) : Pl b ∈ M0 := by
  unfold M0
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hb))

def GoodPrimesStmt : Prop :=
  ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ,
    (∀ e ∈ E0, EdgeOK (q ^ f) e) ∧ FormalOK (m := 529) net0P (q ^ f)

def Net0OkStmt : Prop :=
  ∃ q₀ : ℕ,
    RunsOK (m := 529) net0P ∧
      (∀ q, q.Prime → q₀ < q → ∀ f,
        EdgesOK (m := 529) net0P (q ^ f) ∧ FormalOK (m := 529) net0P (q ^ f))

theorem net0Ok_runs : ∃ _q₀ : ℕ, RunsOK (m := 529) net0P ∧ True :=
  ⟨0, net0P_RunsOK, trivial⟩

theorem E0_Q_retarget : ∀ e ∈ E0, ∃ q, EdgeQ e q := E0_Q

end IntMul.Kappa.R8.Bit.Oppbank.GoodPrimes


