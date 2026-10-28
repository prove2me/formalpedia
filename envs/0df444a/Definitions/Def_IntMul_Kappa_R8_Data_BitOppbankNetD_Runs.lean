-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetD_Runs
-- name    : IntMul_Kappa_R8_Data_BitOppbankNetD_Runs
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:11:22.151963+00:00
-- url     : https://prove2.me/theorems/0ff7a59b-c074-45bc-8695-3a9452103ec5
-- title:
--   R8 NetD runsOK0: ProjB+DagC wired net0D with E0/EdgeQ/RunsOK
-- statement:
--   Opp-bank densified network at $W=104719230$, $T=3217907$, $m=529$, $\mathrm{codeBound}=64251$, formed by wiring published projectors `BitOppbankProjB` ($b18c4ed9$) and DagC packs into the published QHNet program `BitOppbankQHNet` ($52d9e9e0$):
--   $$\mathrm{net0D}=\mathrm{net}(\mathrm{toNB}(\mathrm{ch0P})).$$
--
--   Every program edge lies in a finite family $E_0$ of Defs52 edge classes (`SideR`/`DataR`/`AuxR` via `pickE`/`PE`, with `dfltE` fallback). Each member of $E_0$ realises some rational `EdgeQ`, so
--   $$\mathrm{RunsOK}(\mathrm{net0D})$$
--   holds (`runsOK0`). This is the first conjunct of `net0_ok` toward open `oppbank_net`; EdgesOK/FormalOK still need `good_primes`/`flagBasis`.
-- source:
--   ProjB b18c4ed9; ChkBitArg e96b5336; ChkBitDagC 47a4be0b; QHNet 52d9e9e0; NetD_Wire 54e37bf3

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankChkBitDagC
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# R8 opp-bank NetD — wire `ProjB` + DagC into published `QHNet`

`BitOppbankProjB` (`b18c4ed9`) supplies densified `Pl`/`Dm`/`nestOK`/`pickE`/`ch0P`.
`ChkBitDagC` supplies DagC `g*` for Track-C `orthOK`. Bridge `toNB`/`net0D` feeds
published `BitOppbankQHNet` (`52d9e9e0`). Includes `RunOK` / `E0` / `runsOK0` pieces
toward `net0_ok` (Defs52 wiring; `pickE` falls back to `dfltE` so `RunsOK` holds
before `flagBasis` inhabits every `PE`).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.NetD

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.ProjB
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank.DagC
open Matrix Finset
open QHNet (RunsOK)

/-! ## Re-exports from ProjB -/

abbrev codeBound := ProjB.codeBound
abbrev Ch := ProjB.Ch
noncomputable def ch0 : Ch := ProjB.ch0P

theorem codeBound_eq : codeBound = 64251 := rfl

theorem dagC_imported : (g0 : List Nat) = g0 := rfl

/-! ## Bridge into published QHNet program -/

noncomputable def toNB (ch : Ch) : IntMul.Kappa.R8.Bit.Oppbank.NB.Ch where
  S := ch.S
  Si := ch.Si
  e1 := ch.e1
  e2 := ch.e2
  ex := ch.ex
  en := ch.en
  ei := ch.ei
  ec := ch.ec

noncomputable def net0D : QHNet (ZMod 2) W Tmp 529 := net (toNB ch0)

theorem net0D_W : W = 104719230 := rfl
theorem net0D_T : Tmp = 3217907 := rfl
theorem net0D_codeBound : codeBound = 64251 := codeBound_eq
theorem toNB_ex (ch : Ch) : (toNB ch).ex = ch.ex := rfl
theorem toNB_ei (ch : Ch) : (toNB ch).ei = ch.ei := rfl
theorem toNB_e1 (ch : Ch) : (toNB ch).e1 = ch.e1 := rfl
theorem toNB_e2 (ch : Ch) : (toNB ch).e2 = ch.e2 := rfl
theorem toNB_en (ch : Ch) : (toNB ch).en = ch.en := rfl
theorem toNB_ec (ch : Ch) : (toNB ch).ec = ch.ec := rfl

/-! ## net0_ok pieces: RunOK for Defs52 run classes -/

theorem RunOK_auxRuns19_0 : RunOK 529 (0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4) := by
  simp [RunOK]

theorem RunOK_auxRuns19_1 :
    RunOK 529 ((19 + 4), (19 + 4), (19 + 4) * (19 + 4) - 2 * (19 + 4)) := by
  simp [RunOK]

theorem RunOK_of_mem_auxRuns19 {ρ : ℕ × ℕ × ℕ} (h : ρ ∈ auxRuns 19) :
    RunOK 529 ρ := by
  simp [auxRuns] at h
  rcases h with h | h
  · simpa [h] using RunOK_auxRuns19_0
  · simpa [h] using RunOK_auxRuns19_1

theorem RunOK_dataRuns23_0 : RunOK 529 (2 * 23 - 1, 2 * 23 - 1, 529 - 2 * (2 * 23 - 1)) := by
  simp [RunOK]

theorem RunOK_dataRuns23_1 : RunOK 529 (1, 529 - 23 + 1, 23 - 2) := by
  simp [RunOK]

theorem RunOK_of_mem_dataRuns23 {ρ : ℕ × ℕ × ℕ} (h : ρ ∈ dataRuns 23 529) :
    RunOK 529 ρ := by
  simp [dataRuns] at h
  rcases h with h | h
  · simpa [h] using RunOK_dataRuns23_0
  · simpa [h] using RunOK_dataRuns23_1

theorem RunOK_of_mem_sideRuns23 {r : ℕ} {ρ : ℕ × ℕ × ℕ}
    (hr : r ≤ 23) (h : ρ ∈ sideRuns 23 529 r) : RunOK 529 ρ := by
  unfold sideRuns at h
  by_cases hcond : 23 < 2 * r
  · simp [hcond] at h
    subst h
    have hpos : 0 < 2 * r - 23 := Nat.sub_pos_of_lt hcond
    have hlt : 2 * r - 23 < 529 := by omega
    have h1 : 23 - r + (2 * r - 23) ≤ 529 := by omega
    have h2 : 529 - r + (2 * r - 23) ≤ 529 := by
      have : 529 - r + (2 * r - 23) = 506 + r := by omega
      omega
    exact ⟨hpos, hlt, h1, h2⟩
  · simp [hcond] at h

theorem dfltE_runsOK : ∀ ρ ∈ (ProjB.dfltE : Edge 529).runs, RunOK 529 ρ := by
  intro ρ h; simp [ProjB.dfltE] at h

theorem AuxR_runsOK {rs : List (ℕ × ℕ × ℕ)} (h : AuxR rs) :
    ∀ ρ ∈ rs, RunOK 529 ρ := by
  intro ρ hρ
  have hrs : rs = auxRuns 19 := h
  exact RunOK_of_mem_auxRuns19 (by simpa [hrs] using hρ)

/-! ## EdgeQ for dfltE / pickE (Defs52 NetD) -/

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
  by_cases h : b < v ∧ o < codeBound ∧ c < codeBound
  · have hv : b < 1771 := by simpa [v] using h.1
    have : (b, o, c) ∈ I3 := (mem_I3 _).2 ⟨hv, h.2.1, h.2.2⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(b, o, c), this, rfl⟩)))))
  · have heq : ch0.e1 b o c = ProjB.dfltE := by
      simp only [ch0, ProjB.ch0P, v, codeBound, ProjB.codeBound] at h ⊢
      simp [h]
    rw [heq]; exact dflt_mem

theorem e2_mem (a o c : ℕ) : ch0.e2 a o c ∈ E0 := by
  by_cases h : a < v ∧ o < codeBound ∧ c < codeBound
  · have hv : a < 1771 := by simpa [v] using h.1
    have : (a, o, c) ∈ I3 := (mem_I3 _).2 ⟨hv, h.2.1, h.2.2⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, o, c), this, rfl⟩)))))
  · have heq : ch0.e2 a o c = ProjB.dfltE := by
      simp only [ch0, ProjB.ch0P, v, codeBound, ProjB.codeBound] at h ⊢
      simp [h]
    rw [heq]; exact dflt_mem

theorem ex_mem (b : ℕ) : ch0.ex b ∈ E0 := by
  by_cases h : b < v
  · have hv : b < 1771 := by simpa [v] using h
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨b, Finset.mem_range.2 hv, rfl⟩))))
  · have heq : ch0.ex b = ProjB.dfltE := by
      simp only [ch0, ProjB.ch0P, v] at h ⊢
      simp [h]
    rw [heq]; exact dflt_mem

theorem en_mem (a t : ℕ) : ch0.en a t ∈ E0 := by
  by_cases h : a < v ∧ t < v
  · have ha : a < 1771 := by simpa [v] using h.1
    have ht : t < 1771 := by simpa [v] using h.2
    have : (a, t) ∈ I2 := (mem_I2 _).2 ⟨ha, ht⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, t), this, rfl⟩)))
  · have heq : ch0.en a t = ProjB.dfltE := by
      simp only [ch0, ProjB.ch0P, v] at h ⊢
      simp [h]
    rw [heq]; exact dflt_mem

theorem ei_mem (a : ℕ) : ch0.ei a ∈ E0 := by
  by_cases h : a < v
  · have hv : a < 1771 := by simpa [v] using h
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inl (Or.inr ⟨a, Finset.mem_range.2 hv, rfl⟩))
  · have heq : ch0.ei a = ProjB.dfltE := by
      simp only [ch0, ProjB.ch0P, v] at h ⊢
      simp [h]
    rw [heq]; exact dflt_mem

theorem ec_mem (a s : ℕ) : ch0.ec a s ∈ E0 := by
  by_cases h : a < v ∧ s < v
  · have ha : a < 1771 := by simpa [v] using h.1
    have hs : s < 1771 := by simpa [v] using h.2
    have : (a, s) ∈ I2 := (mem_I2 _).2 ⟨ha, hs⟩
    simp only [E0, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    exact Or.inl (Or.inr ⟨(a, s), this, rfl⟩)
  · have heq : ch0.ec a s = ProjB.dfltE := by
      simp only [ch0, ProjB.ch0P, v] at h ⊢
      simp [h]
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

theorem edges_E0 : ∀ e ∈ net0D.edges, e ∈ E0 := by
  intro e he
  have he' : e ∈ (net (toNB ch0)).edges := he
  rcases prog_fam (toNB ch0) e he' with
    ⟨b, o, c, rfl⟩ | ⟨a, o, c, rfl⟩ | ⟨b, rfl⟩ | ⟨a, t, rfl⟩ | ⟨a, rfl⟩ | ⟨a, s, rfl⟩
  · simpa [toNB_e1] using e1_mem b o c
  · simpa [toNB_e2] using e2_mem a o c
  · simpa [toNB_ex] using ex_mem b
  · simpa [toNB_en] using en_mem a t
  · simpa [toNB_ei] using ei_mem a
  · simpa [toNB_ec] using ec_mem a s

/-- **RunsOK piece of `net0_ok`**: every run on `net0D` is `RunOK`
(via `E0` + `EdgeQ`; `pickE` defaults to `dfltE` when `PE` is vacant). -/
theorem runsOK0 : net0D.RunsOK := by
  intro e he ρ hρ
  obtain ⟨q, hq⟩ := E0_Q e (edges_E0 e he)
  exact hq.1 ρ hρ

theorem net0D_RunsOK : RunsOK (m := 529) net0D := runsOK0

end IntMul.Kappa.R8.Bit.Oppbank.NetD


