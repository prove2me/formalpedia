-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankFormalOK
-- name    : IntMul_Kappa_R8_Data_BitOppbankFormalOK
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:34:31.3278+00:00
-- url     : https://prove2.me/theorems/112701fa-ec00-47f0-823f-10b1a423aa90
-- title:
--   R8 FormalOK/EdgesOK/hist_mom feed on Net0Pnd (honest Pnd)
-- statement:
--   FormalOK/EdgesOK packaging for the honest-`Pnd` opp-bank carrier `Net0Pnd.net0Pnd` at $\mathrm{codeBound}=64251$ (Pnd $1351eb81$).
--
--   Proves the moment identity
--   $$\mathrm{histMoment}(C.\mathrm{hist},529,\tau)=\sum_{e\in C.\mathrm{edges}}\mathrm{EM}_\tau(e),$$
--   `EdgeOK` for the trivial edge, and Defs52 `E0`/`runsOK0` so
--   $$\mathrm{RunsOK}(\mathrm{net0Pnd}).$$
--   `EdgesOK_of_good_primes` lifts a prime-bound `EdgeOK` on $E_0$ to the program. Open: inhabit `PE` via `flagBasis` and discharge `good_mats`/`FormalOK`.
-- source:
--   Pnd 1351eb81; Net0P 373d80bb; MomPack cddcbe7a; GoodPrimes fac3e30f; NetMom 84ad4683

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0Pnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetMom
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# FormalOK / EdgesOK / hist_mom feed for `Net0Pnd`

Expands good_primes packaging onto the honest-`Pnd` carrier
`Net0Pnd.net0Pnd` (`Pnd` = `1351eb81`). Proves:

* `hist_mom` — `histMoment C.hist = (C.edges.map EM).sum` at opp-bank `W`
* `dfltE_EdgeOK` — trivial edge admissible at every `N ≠ 0`
* `E0` / `runsOK0` for `Pnd.ch0P` → `net0Pnd` (same Defs52 pickE shape as GoodPrimes)

`GoodPrimesStmt` / `EdgesOK`/`FormalOK` for large primes remain the open half of
`net0_ok` (need `good_edges`/`good_mats` + inhabited `PE` via `flagBasis`).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.FormalOKFeed

open IntMul.Kappa
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetMom
open IntMul.Kappa.R8.Bit.Oppbank.NB hiding codeBound net0 ch0 dfltE pickE S0 Si0
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open AModel AModelFac Matrix Finset

noncomputable abbrev ch0 : Pnd.Ch := Pnd.ch0P

theorem codeBound_eq : SupG.codeBound = 64251 := rfl

/-! ## hist_mom (network hist = edge-moment sum) -/

theorem hist_mom (τ : ℝ) (C : QHNet (ZMod 2) 104719230 3217907 529) :
    histMoment C.hist 529 τ = (C.edges.map (EM τ)).sum := by
  unfold histMoment QHNet.hist QHNet.widths
  generalize C.edges = l
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.flatMap_cons, List.map_append, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]
    congr 1
    rw [EM, List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun ρ _ => ?_)
    simp [fw]

theorem hist_mom_net0Pnd (τ : ℝ) :
    histMoment net0Pnd.hist 529 τ = (net0Pnd.edges.map (EM τ)).sum :=
  hist_mom τ net0Pnd

/-! ## EdgeOK for dfltE -/

theorem redQ_one (N : ℕ) : redQ N 1 = 1 := by
  have hcop : Nat.Coprime (1 : ℚ).den N := by
    simp [Rat.den_one]
  simp only [redQ, toGood, dif_pos hcop]
  have h1 : (⟨(1 : ℚ), hcop⟩ : goodSub N) = 1 := by
    apply Subtype.ext; simp [One.one]
  rw [h1]
  exact (redHom N).map_one

theorem dfltE_EdgeOK (N : ℕ) [NeZero N] : EdgeOK N (Pnd.dfltE) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [Pnd.dfltE, ne_of_lt hij]
  · intro i j hij
    simp [Pnd.dfltE, ne_of_lt hij]
  · intro i
    change IsUnit (redQ N (Pnd.dfltE.E₁ i i))
    have h1 : Pnd.dfltE.E₁ i i = 1 := by simp [Pnd.dfltE]
    rw [h1, redQ_one]; exact isUnit_one
  · intro i
    change IsUnit (redQ N (Pnd.dfltE.E₂ i i))
    have h1 : Pnd.dfltE.E₂ i i = 1 := by simp [Pnd.dfltE]
    rw [h1, redQ_one]; exact isUnit_one

/-! ## E0 / EdgeQ / runsOK0 for Pnd.ch0P → net0Pnd -/

theorem pswQ_zero {m : ℕ} : pswQ (0 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  unfold pswQ
  rw [sub_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem dfltE_Q : EdgeQ Pnd.dfltE 0 := by
  refine ⟨fun ρ h => absurd h List.not_mem_nil, fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
    fun i => by rw [show Pnd.dfltE.E₁ = 1 from rfl, Matrix.one_apply_eq]; exact one_ne_zero,
    fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
    fun i => by rw [show Pnd.dfltE.E₂ = 1 from rfl, Matrix.one_apply_eq]; exact one_ne_zero, ?_⟩
  rw [pswQ_zero]
  show (1 : QMat2 529) * (([] : List (Fin (529 + 529) × Fin (529 + 529))).map
    fun p => Equiv.swap p.1 p.2).prod.permMatrix ℚ * 1 = 1
  simp

theorem pickE_spec {P : Edge 529 → Prop} (h : ∃ e, P e) : P (Pnd.pickE P) := by
  unfold Pnd.pickE; rw [dif_pos h]; exact Classical.choose_spec h

theorem pickE_Q (q : Matrix (Fin 529) (Fin 529) ℚ) (R : List (ℕ × ℕ × ℕ) → Prop) :
    ∃ q', EdgeQ (Pnd.pickE (PE q R)) q' := by
  by_cases h : ∃ e, PE q R e
  · exact ⟨q, (pickE_spec h).1⟩
  · unfold Pnd.pickE; rw [dif_neg h]; exact ⟨0, dfltE_Q⟩

noncomputable instance instDecEqEdge529 : DecidableEq (Edge 529) := Classical.decEq _

-- Pnd may not export I3/I2 — use local finsets at codeBound
def I3P : Finset (ℕ × ℕ × ℕ) :=
  Finset.range 1771 ×ˢ (Finset.range SupG.codeBound ×ˢ Finset.range SupG.codeBound)

def I2P : Finset (ℕ × ℕ) := Finset.range 1771 ×ˢ Finset.range 1771

attribute [irreducible] I3P I2P

noncomputable def E0 : Finset (Edge 529) :=
  (I3P.image fun p => ch0.e1 p.1 p.2.1 p.2.2) ∪
    (I3P.image fun p => ch0.e2 p.1 p.2.1 p.2.2) ∪
    ((Finset.range v).image ch0.ex) ∪
    (I2P.image fun p => ch0.en p.1 p.2) ∪
    ((Finset.range v).image ch0.ei) ∪
    (I2P.image fun p => ch0.ec p.1 p.2) ∪ {Pnd.dfltE}

attribute [irreducible] E0
attribute [local semireducible] E0 I3P I2P

theorem mem_I3P (p : ℕ × ℕ × ℕ) :
    p ∈ I3P ↔ p.1 < 1771 ∧ p.2.1 < 64251 ∧ p.2.2 < 64251 := by
  unfold I3P
  rw [Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range, Finset.mem_range]
  change _ ↔ p.1 < 1771 ∧ p.2.1 < SupG.codeBound ∧ p.2.2 < SupG.codeBound
  simp only [SupG.codeBound]

theorem mem_I2P (p : ℕ × ℕ) : p ∈ I2P ↔ p.1 < 1771 ∧ p.2 < 1771 := by
  unfold I2P
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]

attribute [local irreducible] I3P I2P

theorem dflt_mem : Pnd.dfltE ∈ E0 := by
  rw [E0, Finset.mem_union]; exact Or.inr (Finset.mem_singleton_self _)

theorem e1_mem (b o c : ℕ) : ch0.e1 b o c ∈ E0 := by
  by_cases h : b < v ∧ o < SupG.codeBound ∧ c < SupG.codeBound
  · have hv : b < 1771 := by simpa [v] using h.1
    have : (b, o, c) ∈ I3P := (mem_I3P _).2 ⟨hv, by simpa [SupG.codeBound] using h.2.1,
      by simpa [SupG.codeBound] using h.2.2⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(b, o, c), this, rfl⟩)))))
  · have heq : ch0.e1 b o c = Pnd.dfltE := by
      change (if b < v ∧ o < SupG.codeBound ∧ c < SupG.codeBound then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem e2_mem (a o c : ℕ) : ch0.e2 a o c ∈ E0 := by
  by_cases h : a < v ∧ o < SupG.codeBound ∧ c < SupG.codeBound
  · have hv : a < 1771 := by simpa [v] using h.1
    have : (a, o, c) ∈ I3P := (mem_I3P _).2 ⟨hv, by simpa [SupG.codeBound] using h.2.1,
      by simpa [SupG.codeBound] using h.2.2⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, o, c), this, rfl⟩)))))
  · have heq : ch0.e2 a o c = Pnd.dfltE := by
      change (if a < v ∧ o < SupG.codeBound ∧ c < SupG.codeBound then _ else _) = _
      rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ex_mem (b : ℕ) : ch0.ex b ∈ E0 := by
  by_cases h : b < v
  · have hv : b < 1771 := by simpa [v] using h
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨b, Finset.mem_range.2 hv, rfl⟩))))
  · have heq : ch0.ex b = Pnd.dfltE := by
      change (if b < v then _ else _) = _; rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem en_mem (a t : ℕ) : ch0.en a t ∈ E0 := by
  by_cases h : a < v ∧ t < v
  · have ha : a < 1771 := by simpa [v] using h.1
    have ht : t < 1771 := by simpa [v] using h.2
    have : (a, t) ∈ I2P := (mem_I2P _).2 ⟨ha, ht⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, t), this, rfl⟩)))
  · have heq : ch0.en a t = Pnd.dfltE := by
      change (if a < v ∧ t < v then _ else _) = _; rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ei_mem (a : ℕ) : ch0.ei a ∈ E0 := by
  by_cases h : a < v
  · have hv : a < 1771 := by simpa [v] using h
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inr ⟨a, Finset.mem_range.2 hv, rfl⟩))
  · have heq : ch0.ei a = Pnd.dfltE := by
      change (if a < v then _ else _) = _; rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem ec_mem (a s : ℕ) : ch0.ec a s ∈ E0 := by
  by_cases h : a < v ∧ s < v
  · have ha : a < 1771 := by simpa [v] using h.1
    have hs : s < 1771 := by simpa [v] using h.2
    have : (a, s) ∈ I2P := (mem_I2P _).2 ⟨ha, hs⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inr ⟨(a, s), this, rfl⟩)
  · have heq : ch0.ec a s = Pnd.dfltE := by
      change (if a < v ∧ s < v then _ else _) = _; rw [if_neg h]
    rw [heq]; exact dflt_mem

theorem E0_Q : ∀ e ∈ E0, ∃ q, EdgeQ e q := by
  have k : ∀ (P : Prop) [Decidable P] (q : Matrix (Fin 529) (Fin 529) ℚ)
      (R : List (ℕ × ℕ × ℕ) → Prop),
      ∃ q', EdgeQ (if P then Pnd.pickE (PE q R) else Pnd.dfltE) q' := by
    intro P _ q R
    split_ifs
    · exact pickE_Q q R
    · exact ⟨0, dfltE_Q⟩
  intro e he
  simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at he
  rcases he with (((((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) |
    ⟨p, -, rfl⟩) | rfl
  · simp only [ch0, Pnd.ch0P]; exact k _ _ _
  · simp only [ch0, Pnd.ch0P]; exact k _ _ _
  · simp only [ch0, Pnd.ch0P]; exact k _ _ _
  · simp only [ch0, Pnd.ch0P]; exact k _ _ _
  · simp only [ch0, Pnd.ch0P]; exact k _ _ _
  · simp only [ch0, Pnd.ch0P]; exact k _ _ _
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

theorem edges_E0 : ∀ e ∈ net0Pnd.edges, e ∈ E0 := by
  intro e he
  have he' : e ∈ (net (Net0Pnd.toNB ch0)).edges := he
  rcases prog_fam (Net0Pnd.toNB ch0) e he' with
    ⟨b, o, c, rfl⟩ | ⟨a, o, c, rfl⟩ | ⟨b, rfl⟩ | ⟨a, t, rfl⟩ | ⟨a, rfl⟩ | ⟨a, s, rfl⟩
  · simpa [Net0Pnd.toNB] using e1_mem b o c
  · simpa [Net0Pnd.toNB] using e2_mem a o c
  · simpa [Net0Pnd.toNB] using ex_mem b
  · simpa [Net0Pnd.toNB] using en_mem a t
  · simpa [Net0Pnd.toNB] using ei_mem a
  · simpa [Net0Pnd.toNB] using ec_mem a s

theorem runsOK0 : net0Pnd.RunsOK := by
  intro e he ρ hρ
  obtain ⟨q, hq⟩ := E0_Q e (edges_E0 e he)
  exact hq.1 ρ hρ

theorem net0Pnd_RunsOK : RunsOK (m := 529) net0Pnd := runsOK0

/-! ## Packaging statements -/

def GoodPrimesStmt : Prop :=
  ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ,
    (∀ e ∈ E0, EdgeOK (q ^ f) e) ∧ FormalOK (m := 529) net0Pnd (q ^ f)

def Net0OkStmt : Prop :=
  ∃ q₀ : ℕ,
    RunsOK (m := 529) net0Pnd ∧
      (∀ q, q.Prime → q₀ < q → ∀ f,
        EdgesOK (m := 529) net0Pnd (q ^ f) ∧ FormalOK (m := 529) net0Pnd (q ^ f))

theorem net0Ok_runs : ∃ _q₀ : ℕ, RunsOK (m := 529) net0Pnd ∧ True :=
  ⟨0, net0Pnd_RunsOK, trivial⟩

/-- EdgesOK follows from good_primes once every program edge is in E0. -/
theorem EdgesOK_of_good_primes (q₀ : ℕ)
    (h : ∀ q, q.Prime → q₀ < q → ∀ f, ∀ e ∈ E0, EdgeOK (q ^ f) e)
    {q : ℕ} (hq : q.Prime) (hlt : q₀ < q) (f : ℕ) :
    EdgesOK (m := 529) net0Pnd (q ^ f) :=
  fun e he => h q hq hlt f e (edges_E0 e he)

end IntMul.Kappa.R8.Bit.Oppbank.FormalOKFeed


