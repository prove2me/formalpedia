-- Prove2me | Definitions.Def_DetDLP_D4SoloForest
-- name    : DetDLP_D4SoloForest
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T22:39:44.381898+00:00
-- url     : https://prove2.me/theorems/1909d3f4-d342-4359-9590-c1bb51236809
-- title:
--   Tree Map, Step Loss Bounds, and V2 Prefix Peeling
-- statement:
--   Defines rank-tree leaf mapping with correctness and Fits preservation, bounds local step loss and total precision guard, and proves prefix peeling invariance for unrollAuxV2 and callsV2.
-- source:
--   prove2me_m14_solo/Definitions/Def_DetDLP_D4SoloForest.lean

import Definitions.Def_DetDLP_D4SoloTree
import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DetDLP.D4SoloForest

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4GuardTree.Expansion DetDLP.D4SoloRaw DetDLP.D4SoloNode
open DetDLP.D4SoloRoot DetDLP.D4SoloStep DetDLP.D4SoloStepEq DetDLP.D4SoloTree
open DetDLP.MachineComposition
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section

section OutputLengthBound

private theorem tape_outside_init (A : PrimitiveMachine) (inp : List Bool)
    (i : Fin A.tapeCount) (z : ℤ)
    (hz : z < (locatedInit A inp).lower i ∨ (locatedInit A inp).upper i < z) :
    ((locatedInit A inp).config.tapes i).nth (z - (locatedInit A inp).position i) = none := by
  simp only [locatedInit, sub_zero] at hz ⊢
  change (if i = A.inputTape then Turing.Tape.mk₁ (inp.map some) else Turing.Tape.mk₁ []).nth z = none
  by_cases hi : i = A.inputTape
  · simp only [hi, ↓reduceIte] at hz ⊢
    cases z with
    | negSucc m => rfl
    | ofNat m =>
      simp only [Int.ofNat_eq_natCast] at hz ⊢
      have hm : inp.length ≤ m := by
        rcases hz with hlt | hgt <;> omega
      simp only [Turing.Tape.mk₁, Turing.Tape.mk₂]
      rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD]
      have hnone : (inp.map some)[m]? = none := List.getElem?_eq_none (by simpa using hm)
      rw [hnone]; rfl
  · simp only [hi, ↓reduceIte] at hz ⊢
    cases z with
    | negSucc m => rfl
    | ofNat m =>
      simp only [Int.ofNat_eq_natCast] at hz ⊢
      have hm : 1 ≤ m := by rcases hz with hlt | hgt <;> omega
      simp only [Turing.Tape.mk₁, Turing.Tape.mk₂]
      rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD]
      have hnone : ([] : List (Option Bool))[m]? = none := List.getElem?_eq_none (by simp)
      rw [hnone]; rfl

private theorem tape_outside_step {A : PrimitiveMachine} {c d : LocatedCfg A}
    (hwf : LocatedWellFormed c)
    (hinv : ∀ i z, (z < c.lower i ∨ c.upper i < z) →
      (c.config.tapes i).nth (z - c.position i) = none)
    (hstep : locatedStep A c = some d) :
    ∀ i z, (z < d.lower i ∨ d.upper i < z) →
      (d.config.tapes i).nth (z - d.position i) = none := by
  unfold locatedStep at hstep
  obtain ⟨cfg', hcs, rfl⟩ := Option.map_eq_some_iff.mp hstep
  intro i z hz
  unfold PrimitiveMachine.step at hcs
  cases hs : c.config.state with
  | inl b => rw [hs] at hcs; cases hcs
  | inr q =>
    rw [hs] at hcs
    dsimp only at hcs
    cases htr : A.transition q (c.config.tapes (A.scan q)).head with
    | inl ans =>
      rw [htr] at hcs
      injection hcs with hcfg
      subst hcfg
      have hmon : c.monitor ⟨.inl ans, c.config.tapes⟩ = ⟨⟨.inl ans, c.config.tapes⟩, c.position, c.lower, c.upper⟩ := by
        simp [LocatedCfg.monitor, hs, htr]
      rw [hmon] at hz ⊢
      exact hinv i z hz
    | inr qa =>
      rw [htr] at hcs
      rcases qa with ⟨q', action⟩
      injection hcs with hcfg
      subst hcfg
      let nextTape := match action with
        | .move dir => (c.config.tapes (A.scan q)).move dir
        | .write sym => (c.config.tapes (A.scan q)).write sym
      let nextCfg : A.Cfg := ⟨.inr q', Function.update c.config.tapes (A.scan q) nextTape⟩
      by_cases hi : i = A.scan q
      · subst hi
        let j := A.scan q
        have hpos : (c.monitor nextCfg).position j = c.position j + headDisplacement action := by
          simp [LocatedCfg.monitor, hs, htr, j]
        have hlo : (c.monitor nextCfg).lower j = min (c.lower j) (c.position j + headDisplacement action) := by
          simp [LocatedCfg.monitor, hs, htr, j]
        have hhi : (c.monitor nextCfg).upper j = max (c.upper j) (c.position j + headDisplacement action) := by
          simp [LocatedCfg.monitor, hs, htr, j]
        have htape : (c.monitor nextCfg).config.tapes j = nextTape := by
          simp [LocatedCfg.monitor, hs, htr, j, nextCfg]
        change z < (c.monitor nextCfg).lower j ∨ (c.monitor nextCfg).upper j < z at hz
        change ((c.monitor nextCfg).config.tapes j).nth (z - (c.monitor nextCfg).position j) = none
        rw [hlo, hhi] at hz
        rw [htape, hpos]
        dsimp only [nextTape]
        have hz_old : z < c.lower j ∨ c.upper j < z := by
          rcases hz with h1 | h2
          · exact Or.inl (lt_of_lt_of_le h1 (min_le_left _ _))
          · exact Or.inr (lt_of_le_of_lt (le_max_left _ _) h2)
        cases action with
        | write sym =>
          simp only [headDisplacement, add_zero]
          have hwf_j := hwf j
          have hne0 : z - c.position j ≠ 0 := by
            rcases hz_old with h1 | h2 <;> omega
          rw [Turing.Tape.write_nth]
          simp only [hne0, ↓reduceIte]
          exact hinv j z hz_old
        | move dir =>
          cases dir with
          | left =>
            simp only [headDisplacement, Turing.Tape.move_left_nth]
            have heq : z - (c.position j + -1) - 1 = z - c.position j := by omega
            rw [heq]
            exact hinv j z hz_old
          | right =>
            simp only [headDisplacement, Turing.Tape.move_right_nth]
            have heq : z - (c.position j + 1) + 1 = z - c.position j := by omega
            rw [heq]
            exact hinv j z hz_old
      · have hpos : (c.monitor nextCfg).position i = c.position i := by
          simp [LocatedCfg.monitor, hs, htr, Function.update_of_ne hi]
        have hlo : (c.monitor nextCfg).lower i = c.lower i := by
          simp [LocatedCfg.monitor, hs, htr, Function.update_of_ne hi]
        have hhi : (c.monitor nextCfg).upper i = c.upper i := by
          simp [LocatedCfg.monitor, hs, htr, Function.update_of_ne hi]
        have htape : (c.monitor nextCfg).config.tapes i = c.config.tapes i := by
          simp [LocatedCfg.monitor, hs, htr, nextCfg, Function.update_of_ne hi]
        change z < (c.monitor nextCfg).lower i ∨ (c.monitor nextCfg).upper i < z at hz
        change ((c.monitor nextCfg).config.tapes i).nth (z - (c.monitor nextCfg).position i) = none
        rw [hlo, hhi] at hz
        rw [htape, hpos]
        exact hinv i z hz

private theorem tape_outside_trace {A : PrimitiveMachine} {inp : List Bool}
    {n : ℕ} {f : LocatedCfg A}
    (htr : Computation.Trace (locatedStep A) n (locatedInit A inp) f) :
    ∀ i z, (z < f.lower i ∨ f.upper i < z) →
      (f.config.tapes i).nth (z - f.position i) = none := by
  have hgen : ∀ {a b : LocatedCfg A} {m : ℕ},
      Computation.Trace (locatedStep A) m a b →
      LocatedWellFormed a →
      (∀ i z, (z < a.lower i ∨ a.upper i < z) → (a.config.tapes i).nth (z - a.position i) = none) →
      ∀ i z, (z < b.lower i ∨ b.upper i < z) → (b.config.tapes i).nth (z - b.position i) = none := by
    intro a b m tr
    induction tr with
    | refl => intro _ hinv; exact hinv
    | cons hs _ ih =>
      intro hw hinv
      exact ih (locatedWellFormed_step hw hs) (tape_outside_step hw hinv hs)
  exact hgen htr (locatedWellFormed_init A inp) (tape_outside_init A inp)

/-- Universal output-length bound: any word written by `RunsWithin` has length `≤ σ`. -/
theorem runsWithin_output_len_le {A : PrimitiveMachine} {o : Fin A.tapeCount}
    {inp out : List Bool} {τ σ : ℝ}
    (h : RunsWithin A o inp out τ σ) : (out.length : ℝ) ≤ σ := by
  obtain ⟨n, f, htr, _, hout, _, hs⟩ := h
  have hf_sp : (visitedSpace f : ℝ) ≤ σ := hs n f le_rfl htr
  by_cases hempty : out.length = 0
  · rw [hempty, Nat.cast_zero]
    exact (Nat.cast_nonneg (visitedSpace f)).trans hf_sp
  · have hpos : 0 < out.length := Nat.pos_of_ne_zero hempty
    have hout_inv := tape_outside_trace htr o
    have h0_in : f.lower o ≤ f.position o := by
      by_contra! hlt
      have hnone := hout_inv (f.position o) (Or.inl hlt)
      rw [sub_self, hout] at hnone
      change (Turing.Tape.mk₁ (out.map some)).nth ((0 : ℕ) : ℤ) = none at hnone
      simp only [Turing.Tape.mk₁, Turing.Tape.mk₂] at hnone
      rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD] at hnone
      have h0lt : 0 < (out.map some).length := by simp [hpos]
      rw [List.getElem?_eq_getElem h0lt, List.getElem_map, Option.getD_some] at hnone
      cases hnone
    have hlast_in : f.position o + ((out.length - 1 : ℕ) : ℤ) ≤ f.upper o := by
      by_contra! hgt
      have hnone := hout_inv (f.position o + ((out.length - 1 : ℕ) : ℤ)) (Or.inr hgt)
      have hsub : f.position o + ((out.length - 1 : ℕ) : ℤ) - f.position o = ((out.length - 1 : ℕ) : ℤ) := by omega
      rw [hsub, hout] at hnone
      simp only [Turing.Tape.mk₁, Turing.Tape.mk₂] at hnone
      rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD] at hnone
      have hllt : out.length - 1 < (out.map some).length := by simp; omega
      rw [List.getElem?_eq_getElem hllt, List.getElem_map, Option.getD_some] at hnone
      cases hnone
    have hlen_le : out.length ≤ (f.upper o - f.lower o + 1).toNat := by omega
    have hsingle : (f.upper o - f.lower o + 1).toNat ≤ visitedSpace f :=
      Finset.single_le_sum (f := fun i : Fin A.tapeCount => (f.upper i - f.lower i + 1).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)
    exact (by exact_mod_cast hlen_le.trans hsingle : (out.length : ℝ) ≤ visitedSpace f).trans hf_sp

end OutputLengthBound

section TreeMap

def treeMap {α β : Type} (fn : α → β) : D4RankCode.Tree α → D4RankCode.Tree β
  | .leaf a => .leaf (fn a)
  | .choice n next => .choice n (fun d => treeMap fn (next d))

theorem treeMap_read {α β : Type} (fn : α → β) (t : D4RankCode.Tree α) (b j : ℕ) :
    (treeMap fn t).read b j = (t.read b j).map fn := by
  induction t generalizing b j with
  | leaf a =>
    unfold treeMap D4RankCode.Tree.read
    split_ifs <;> rfl
  | choice n next ih =>
    unfold treeMap D4RankCode.Tree.read
    dsimp only
    split_ifs with hwb hmod
    · exact ih ⟨j % 2 ^ Nat.clog 2 n, hmod⟩ (b - Nat.clog 2 n) (j / 2 ^ Nat.clog 2 n)
    · rfl
    · rfl

theorem treeMap_fits {α β : Type} (fn : α → β) (t : D4RankCode.Tree α) (b : ℕ)
    (h : t.Fits b) : (treeMap fn t).Fits b := by
  induction t generalizing b with
  | leaf _ => trivial
  | choice n next ih =>
    exact ⟨h.1, fun i => ih i (b - Nat.clog 2 n) (h.2 i)⟩

theorem treeMap_total {α β R : Type} [AddCommMonoid R] (fn : α → β) (v : β → R)
    (t : D4RankCode.Tree α) :
    D4RankCode.Tree.total v (treeMap fn t) = D4RankCode.Tree.total (v ∘ fn) t := by
  induction t with
  | leaf a => rfl
  | choice n next ih =>
    simp only [treeMap, D4RankCode.Tree.total, ih]

end TreeMap

section LeafAndForest

theorem slots_bound_64 (k : ℕ) : D4GuardTree.slots k ≤ 64 ^ k := by
  have heq : 63 * D4GuardTree.slots k + 1 = 64 ^ k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [D4GuardTree.slots, pow_succ, ← ih]; ring
  omega

theorem loss_le_localAllowance (S D d M : ℕ) (hd : d ≤ D) (hM : M ≤ S) (hw : 1 ≤ D3Stopped.width S d) :
    AppendixD4.loss M (D3Stopped.shift S d) (D3Stopped.width S d) 0 ≤ localAllowance S D := by
  let a := D3Stopped.shift S d
  let u := D3Stopped.width S d
  have ha : a ≤ D3Stopped.shift S D := shift_mono_solo S hd
  have hpow : 2 ^ a ≤ 2 ^ D3Stopped.shift S D := Nat.pow_le_pow_right (by decide) ha
  have hmult : AppendixD4.mult M u ≤ 3 * S := by
    unfold AppendixD4.mult
    have hdiv : (3 * M + u - 1) / u ≤ 3 * M := by
      have : 3 * M + u - 1 < (3 * M + 1) * u := by
        rw [Nat.add_mul, Nat.one_mul]
        have : 1 ≤ 3 * M * u + u := by omega
        have : 3 * M * 1 ≤ 3 * M * u := Nat.mul_le_mul_left _ hw
        omega
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hw).mpr this)
    exact hdiv.trans (Nat.mul_le_mul_left 3 hM)
  unfold AppendixD4.loss tileScale localAllowance
  simp only [Nat.sub_zero]
  have h1 : 6 * AppendixD4.mult M u * 2 ^ a ≤ 18 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D := by
    have hp1 : 1 ≤ D3Stopped.shift S D + 1 := Nat.succ_pos _
    have hs1 : S ≤ S + 1 := Nat.le_succ S
    calc 6 * AppendixD4.mult M u * 2 ^ a
        ≤ 6 * (3 * S) * 2 ^ D3Stopped.shift S D := Nat.mul_le_mul (Nat.mul_le_mul_left 6 hmult) hpow
      _ = 18 * S * 1 * 2 ^ D3Stopped.shift S D := by ring
      _ ≤ 18 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D := by gcongr
  have h2 : 4 * M * (a + 1) ≤ 4 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D := by
    have hp2 : 1 ≤ 2 ^ D3Stopped.shift S D := Nat.one_le_pow _ _ (by decide)
    calc 4 * M * (a + 1)
        ≤ 4 * (S + 1) * (D3Stopped.shift S D + 1) * 1 := by
          rw [mul_one]; exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 (hM.trans (Nat.le_succ S))) (Nat.add_le_add_right ha 1)
      _ ≤ 4 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D := by gcongr
  dsimp only [a, u] at h1 h2
  calc 6 * AppendixD4.mult M (D3Stopped.width S d) * 2 ^ D3Stopped.shift S d + 4 * M * (D3Stopped.shift S d + 1)
      ≤ 18 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D +
          4 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D := Nat.add_le_add h1 h2
    _ = 22 * ((S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) := by ring
    _ ≤ 40 * ((S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) := Nat.mul_le_mul_right _ (by decide)
    _ = 40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D := by ring

theorem step_prec_le_guard (S D p d pCurr M : ℕ) (hd : d < D) (hM : M ≤ S)
    (hw : 1 ≤ D3Stopped.width S d)
    (hpCurr : pCurr ≤ p + 80 * S * 2 ^ D3Stopped.shift S d) :
    pCurr + AppendixD4.loss M (D3Stopped.shift S d) (D3Stopped.width S d) 0 ≤
      totalGuard S D + p := by
  have hD1 : 1 ≤ D := by omega
  have h64 : 64 ≤ 64 ^ D := by
    calc 64 = 64 ^ 1 := by ring
      _ ≤ 64 ^ D := Nat.pow_le_pow_right (by decide) hD1
  have hloss := loss_le_localAllowance S D d M hd.le hM hw
  have ha : D3Stopped.shift S d ≤ D3Stopped.shift S D := shift_mono_solo S hd.le
  have hpow : 2 ^ D3Stopped.shift S d ≤ 2 ^ D3Stopped.shift S D := Nat.pow_le_pow_right (by decide) ha
  have h80 : 80 * S * 2 ^ D3Stopped.shift S d ≤ 2 * localAllowance S D := by
    unfold localAllowance
    have hsh1 : 1 ≤ D3Stopped.shift S D + 1 := Nat.succ_pos _
    calc 80 * S * 2 ^ D3Stopped.shift S d
        ≤ 80 * (S + 1) * 1 * 2 ^ D3Stopped.shift S D := by
          rw [mul_one]; exact Nat.mul_le_mul (Nat.mul_le_mul_left 80 (Nat.le_succ S)) hpow
      _ ≤ 80 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D := by gcongr
      _ = 2 * (40 * (S + 1) * (D3Stopped.shift S D + 1) * 2 ^ D3Stopped.shift S D) := by ring
  unfold totalGuard
  have h3 : 3 * localAllowance S D ≤ localAllowance S D * 64 ^ D := by
    calc 3 * localAllowance S D ≤ 64 * localAllowance S D := Nat.mul_le_mul_right _ (by decide)
      _ ≤ 64 ^ D * localAllowance S D := Nat.mul_le_mul_right _ h64
      _ = localAllowance S D * 64 ^ D := Nat.mul_comm _ _
  omega

theorem small_ctx_eq {C c : ℕ} {x : Input C c} {f : ℤ[X]} {PktOK : PktPred f x.l}
    (guard : ℕ) (nd : SoloNode x f PktOK) :
    small (contextV2 x.S x.m x.p guard x.l (polynomialBits f)) nd.toWorkItem.bits =
      (decide (Nat.clog 32 (4 * x.m) ≤ nd.d) || decide (nd.G.nE ≤ D3Stopped.threshold x.S)) := by
  unfold small contextV2 SoloNode.toWorkItem WorkItem.bits BipartiteMultigraph.encode
  simp [num, fld_pack]

theorem stepLoss_ctx_eq {C c : ℕ} {x : Input C c} {f : ℤ[X]} {PktOK : PktPred f x.l}
    (guard : ℕ) (nd : SoloNode x f PktOK) (hd : nd.d < Nat.clog 32 (4 * x.m)) :
    stepLoss (contextV2 x.S x.m x.p guard x.l (polynomialBits f)) nd.toWorkItem.bits =
      AppendixD4.loss nd.G.nE (D3Stopped.shift x.S nd.d) (D3Stopped.width x.S nd.d) 0 := by
  let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
  have hnum0 : num nd.toWorkItem.bits 0 = nd.d := by
    simp [SoloNode.toWorkItem, WorkItem.bits, num, fld_pack]
  have hM : num (fld nd.toWorkItem.bits 1) 1 = nd.G.nE := by
    simp [SoloNode.toWorkItem, WorkItem.bits, BipartiteMultigraph.encode, num, fld_pack]
  have hrow : rowAt ctx nd.toWorkItem.bits = row x.S nd.d := by
    unfold rowAt
    rw [hnum0]
    have h5 : fld ctx 5 = pack ((List.range (Nat.clog 32 (4 * x.m))).map (row x.S)) := by
      simp [ctx, contextV2, fld_pack]
    rw [h5, fld_pack]
    have hlen : nd.d < ((List.range (Nat.clog 32 (4 * x.m))).map (row x.S)).length := by simp [hd]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_map,
        List.getElem_range, Option.getD_some]
  unfold stepLoss AppendixD4.loss tileScale
  rw [hrow, hM]
  dsimp only [row]
  simp only [num, fld_pack, List.getD_cons_zero, List.getD_cons_succ, num_countWord, Nat.sub_zero]
  have ha_le : D3Stopped.shift x.S nd.d ≤ 64 ^ D3Stopped.shift x.S nd.d :=
    (Nat.lt_pow_self (by decide : 1 < 64)).le
  rw [pow2_replicate_eq _ _ ha_le]

theorem unrollAuxV2_peel_stop (ctx : Wd) (F : Wd → WalkerStep) (fuel : ℕ)
    (i : Wd) (rest done_ : List Wd) (acc : Wd) (lossSum : ℕ)
    (hsmall : small ctx i = true) :
    unrollAuxV2 ctx F fuel (i :: rest) done_ acc lossSum =
      unrollAuxV2 ctx F fuel rest (done_ ++ [i]) acc lossSum := by
  have hidx : ((i :: rest).map (small ctx)).idxOf false = 1 + (rest.map (small ctx)).idxOf false := by
    simp [List.map_cons, hsmall, List.idxOf, List.findIdx_cons, Nat.add_comm]
  conv_lhs => rw [unrollAuxV2.eq_1]
  conv_rhs => rw [unrollAuxV2.eq_1]
  rw [hidx]
  have hdrop : (i :: rest).drop (1 + (rest.map (small ctx)).idxOf false) =
      rest.drop ((rest.map (small ctx)).idxOf false) := by
    rw [Nat.add_comm]; rfl
  have htake : done_ ++ (i :: rest).take (1 + (rest.map (small ctx)).idxOf false) =
      (done_ ++ [i]) ++ rest.take ((rest.map (small ctx)).idxOf false) := by
    rw [Nat.add_comm 1, List.take_succ_cons, List.append_assoc]; rfl
  rw [hdrop, htake]

theorem callsV2_peel_stop (ctx : Wd) (F : Wd → WalkerStep) (fuel : ℕ)
    (i : Wd) (rest done_ : List Wd) (b u : ℕ) (acc : Wd) (lossSum : ℕ)
    (hsmall : small ctx i = true) :
    callsV2 ctx F fuel (i :: rest) done_ b u acc lossSum =
      callsV2 ctx F fuel rest (done_ ++ [i]) b u acc lossSum := by
  have hidx : ((i :: rest).map (small ctx)).idxOf false = 1 + (rest.map (small ctx)).idxOf false := by
    simp [List.map_cons, hsmall, List.idxOf, List.findIdx_cons, Nat.add_comm]
  conv_lhs => rw [callsV2.eq_def]; dsimp only
  conv_rhs => rw [callsV2.eq_def]; dsimp only
  rw [hidx]
  have hdrop : (i :: rest).drop (1 + (rest.map (small ctx)).idxOf false) =
      rest.drop ((rest.map (small ctx)).idxOf false) := by
    rw [Nat.add_comm]; rfl
  have htake : done_ ++ (i :: rest).take (1 + (rest.map (small ctx)).idxOf false) =
      (done_ ++ [i]) ++ rest.take ((rest.map (small ctx)).idxOf false) := by
    rw [Nat.add_comm 1, List.take_succ_cons, List.append_assoc]; rfl
  rw [hdrop, htake]

end LeafAndForest

end

end DetDLP.D4SoloForest


