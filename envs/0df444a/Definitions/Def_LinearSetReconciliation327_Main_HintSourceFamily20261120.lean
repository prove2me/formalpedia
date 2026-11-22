-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintSourceFamily20261120
-- name    : LinearSetReconciliation327_Main_HintSourceFamily20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:04:28.564019+00:00
-- url     : https://prove2.me/theorems/c0bac5ba-011b-40bd-b9b7-5c6fda06d6b1
-- title:
--   LinearSetReconciliation327 — HintSourceFamily (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintSourceFamily20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdatePrepared20261120
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
import Theorems.Thm_LinearSetReconciliation327_Main_proposition_2_3
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_9
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_10
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_4
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_5_6
import Theorems.Thm_LinearSetReconciliation327_Main_theorem_4_9
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crStep_halted (P : Program) (E : RAMEnv) (s : RAMState) (h : Halted P s) : step P E s = s := by
  cases hp : P[s.pc]? with
  | none => simp only [Halted, hp] at h
  | some ins => cases ins <;> simp_all only [Halted, step, not_false_eq_true]
theorem crClock_result_of_halts (P : Program) (E : RAMEnv) (s out : RAMState) (T : ℝ) (B : ℕ)
    (hRun : HaltsWithin P E T s out) (hBudget : T ≤ (B : ℝ)) : (step P E)^[B] s = out := by
  obtain ⟨k, hk, hExec, hHalt⟩ := hRun
  have hkB : k ≤ B := by exact_mod_cast hk.trans hBudget
  have hStay : ∀ j, (step P E)^[j] out = out := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [show j + 1 = 1 + j from by omega, Function.iterate_add_apply, Function.iterate_one,
          ih, crStep_halted P E out hHalt]
  calc
    (step P E)^[B] s = (step P E)^[B - k] ((step P E)^[k] s) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    _ = (step P E)^[B - k] out := by rw [hExec]
    _ = out := hStay _
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
structure CRSourcePacket (N t : ℕ) where
  W : ℕ
  R : ℕ
  det : ℕ → ℕ
  H : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin R → ZMod 2)
def crSourceEmpty (N t : ℕ) : CRSourcePacket N t := ⟨1, 0, fun _ => 0, 0⟩
def CRSourcePacketSpec (progUp progDec : Program) (K cW : ℝ) (N t : ℕ)
    (d : CRSourcePacket N t) : Prop :=
  WidthOK d.W N cW (lg ((N : ℝ) + 2)) ∧ wordsOf d.W d.R ≤ 2 ^ d.W ∧
  (d.R : ℝ) ≤ K * ((t : ℝ) * lg ((N : ℝ) + 2) ^ 2) ∧
  ColumnWeightLE d.H (K * lg ((N : ℝ) + 2) ^ 2) ∧
  TogglesWithin progUp (detEnv d.W d.det) d.H (K * lg ((N : ℝ) + 2) ^ 2) ∧
  ∀ x : Fin N → ZMod 2, (Finset.univ.filter fun i => x i = 1).card ≤ t →
    ∃ out : RAMState,
      HaltsWithin progDec (detEnv d.W d.det)
        (K * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)))
        (decoderStart d.W (d.H x) []) out ∧ OutputsSupport out x
structure CRSourceBundle where
  progUp : Program
  progDec : Program
  K : ℝ
  cW : ℝ
  K_pos : 0 < K
  cW_pos : 0 < cW
  data : ∀ N t, CRSourcePacket N t
  spec : ∀ N t, 1 ≤ N → t ≤ N → CRSourcePacketSpec progUp progDec K cW N t (data N t)
  invalid : ∀ N t, ¬ (1 ≤ N ∧ t ≤ N) → data N t = crSourceEmpty N t
theorem crSourceBundle_exists : Nonempty CRSourceBundle := by
  classical
  obtain ⟨progUp, progDec, K, cW, hK, hcW, hAll⟩ := proposition_2_3
  have hPackets : ∀ N t, ∃ d : CRSourcePacket N t,
      ((1 ≤ N ∧ t ≤ N) → CRSourcePacketSpec progUp progDec K cW N t d) ∧
        (¬ (1 ≤ N ∧ t ≤ N) → d = crSourceEmpty N t) := by
    intro N t
    by_cases hValid : 1 ≤ N ∧ t ≤ N
    · obtain ⟨W, R, det, H, hSpec⟩ := hAll N t hValid.1 hValid.2
      refine ⟨⟨W, R, det, H⟩, ?_, ?_⟩
      · intro h
        exact hSpec
      · intro h
        exact (h hValid).elim
    · refine ⟨crSourceEmpty N t, ?_, ?_⟩
      · intro h
        exact (hValid h).elim
      · intro h
        rfl
  choose data hSpec hInvalid using hPackets
  exact ⟨⟨progUp, progDec, K, cW, hK, hcW, data,
    fun N t hN ht => hSpec N t ⟨hN, ht⟩, hInvalid⟩⟩
noncomputable def crSourceBundle : CRSourceBundle := Classical.choice crSourceBundle_exists
def crSourceSteps (S : CRSourceBundle) (N t : ℕ) : ℕ :=
  ⌈S.K * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2))⌉₊
theorem crSourceSteps_ge (S : CRSourceBundle) (N t : ℕ) :
    S.K * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)) ≤ (crSourceSteps S N t : ℝ) :=
  Nat.le_ceil _
theorem crSource_clock_recovers (S : CRSourceBundle) (N t : ℕ) (hN : 1 ≤ N) (ht : t ≤ N)
    (x : Fin N → ZMod 2) (hSupp : (Finset.univ.filter fun i => x i = 1).card ≤ t) :
    OutputsSupport
      ((step S.progDec (detEnv (S.data N t).W (S.data N t).det))^[crSourceSteps S N t]
        (decoderStart (S.data N t).W ((S.data N t).H x) [])) x := by
  obtain ⟨out, hRun, hOut⟩ := (S.spec N t hN ht).2.2.2.2.2 x hSupp
  rw [crClock_result_of_halts S.progDec (detEnv (S.data N t).W (S.data N t).det)
    (decoderStart (S.data N t).W ((S.data N t).H x) []) out _ (crSourceSteps S N t)
    hRun (crSourceSteps_ge S N t)]
  exact hOut
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
open Classical
def crInput (N : ℕ) (x : Finset ℕ) : Fin N → ZMod 2 :=
  fun i => if i.val ∈ x then 1 else 0
theorem crSupport_mem {N : ℕ} (y : Fin N → ZMod 2) (v : ℕ) :
    v ∈ support y ↔ ∃ i : Fin N, i.val = v ∧ y i = 1 := by
  simp only [support, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hv⟩; exact ⟨i, hv, hi⟩
  · rintro ⟨i, hv, hi⟩; exact ⟨i, hi, hv⟩
theorem crSupport_at {N : ℕ} (y : Fin N → ZMod 2) (i : Fin N) :
    i.val ∈ support y ↔ y i = 1 := by
  rw [crSupport_mem]
  constructor
  · rintro ⟨j, hj, hy⟩
    exact (congrArg y (Fin.ext hj)).symm.trans hy
  · intro h; exact ⟨i, rfl, h⟩
theorem crSupport_lt {N : ℕ} (y : Fin N → ZMod 2) {v : ℕ}
    (h : v ∈ support y) : v < N := by
  obtain ⟨i, rfl, _⟩ := (crSupport_mem y v).mp h
  exact i.isLt
theorem crSupport_card {N : ℕ} (y : Fin N → ZMod 2) : (support y).card ≤ N := by
  calc
    (support y).card ≤ (Finset.univ.filter fun i : Fin N => y i = 1).card :=
      Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by simp
theorem crInput_support (N : ℕ) (x : Finset ℕ) (hx : x ⊆ Finset.range N) :
    support (crInput N x) = x := by
  ext v
  rw [crSupport_mem]
  constructor
  · rintro ⟨i, rfl, hi⟩
    by_contra hn
    simp [crInput, hn] at hi
  · intro hv
    exact ⟨⟨v, Finset.mem_range.mp (hx hv)⟩, rfl, by simp [crInput, hv]⟩
theorem crInput_support_vec {N : ℕ} (y : Fin N → ZMod 2) :
    crInput N (support y) = y := by
  funext i
  rcases zmod2_eq_zero_or_one (y i) with hi | hi
  · simp [crInput, crSupport_at, hi]
  · simp [crInput, crSupport_at, hi]
theorem crInput_insert {N a : ℕ} (x : Finset ℕ) (ha : a < N) (hx : a ∉ x) :
    crInput N (insert a x) = Pi.single (⟨a, ha⟩ : Fin N) 1 + crInput N x := by
  funext i
  by_cases hi : i.val = a
  · have he : i = (⟨a, ha⟩ : Fin N) := Fin.ext hi
    subst i
    simp [crInput, hx]
  · have he : i ≠ (⟨a, ha⟩ : Fin N) := fun h => hi (congrArg Fin.val h)
    simp [crInput, hi, Pi.single_eq_of_ne he]
def crNatCol (S : CRSourceBundle) (N t c : ℕ) : Finset ℕ :=
  if hc : c < N then support ((S.data N t).H (Pi.single (⟨c, hc⟩ : Fin N) 1)) else ∅
def crSourceRun (S : CRSourceBundle) (N t : ℕ) (a : Finset ℕ) : RAMState :=
  (step S.progDec (detEnv (S.data N t).W (S.data N t).det))^[crSourceSteps S N t]
    (decoderStart (S.data N t).W (crInput (S.data N t).R a) [])
def crReadResult (N : ℕ) (s : RAMState) : Option (Finset ℕ) :=
  if s.regs 1 ≤ N then some ((outList s).toFinset.filter fun v => v < N) else none
def crFamily (S : CRSourceBundle) : CRFamily where
  rows := fun N t => (S.data N t).R
  col := crNatCol S
  dec := fun N t a =>
    if 1 ≤ N ∧ t ≤ N then crReadResult N (crSourceRun S N t a) else some ∅
theorem crNatCol_range (S : CRSourceBundle) (N t c : ℕ) :
    crNatCol S N t c ⊆ Finset.range (S.data N t).R := by
  intro v hv
  unfold crNatCol at hv
  split_ifs at hv with hc
  · exact Finset.mem_range.mpr (crSupport_lt _ hv)
  · simp at hv
theorem crFamily_single (S : CRSourceBundle) (N t a : ℕ) (ha : a < N) :
    (crFamily S).sketch N t {a} =
      support ((S.data N t).H (Pi.single (⟨a, ha⟩ : Fin N) 1)) := by
  rw [cr_sketch_singleton]
  ext v
  change v ∈ (Finset.range (S.data N t).R).filter
    (fun r => r ∈ crNatCol S N t a) ↔ _
  rw [Finset.mem_filter]
  simp only [crNatCol, dif_pos ha]
  exact and_iff_right_of_imp (fun h => Finset.mem_range.mpr (crSupport_lt _ h))
theorem crFamily_sketch (S : CRSourceBundle) (N t : ℕ) (x : Finset ℕ)
    (hx : x ⊆ Finset.range N) :
    (crFamily S).sketch N t x = support ((S.data N t).H (crInput N x)) := by
  revert hx
  induction x using Finset.induction_on with
  | empty =>
    intro hx
    have hz : crInput N ∅ = 0 := by ext i; simp [crInput]
    simp [CRFamily.sketch, hz, support_zero]
  | @insert a x ha ih =>
    intro hx
    have haN : a < N := Finset.mem_range.mp (hx (Finset.mem_insert_self a x))
    have hxN : x ⊆ Finset.range N := fun i hi => hx (Finset.mem_insert_of_mem hi)
    have hs : insert a x = symmDiff ({a} : Finset ℕ) x := by
      ext i
      by_cases hi : i = a <;> simp [Finset.mem_symmDiff, hi, ha]
    calc
      (crFamily S).sketch N t (insert a x) =
          symmDiff ((crFamily S).sketch N t {a}) ((crFamily S).sketch N t x) := by
        rw [hs, sketch_symmDiff]
      _ = symmDiff (support ((S.data N t).H (Pi.single (⟨a, haN⟩ : Fin N) 1)))
          (support ((S.data N t).H (crInput N x))) := by
        rw [crFamily_single S N t a haN, ih hxN]
      _ = support ((S.data N t).H (Pi.single (⟨a, haN⟩ : Fin N) 1 + crInput N x)) := by
        rw [map_add, support_add]
      _ = support ((S.data N t).H (crInput N (insert a x))) := by
        rw [crInput_insert x haN ha]
theorem crInput_card (N : ℕ) (x : Finset ℕ) (hx : x ⊆ Finset.range N) :
    (Finset.univ.filter fun i : Fin N => crInput N x i = 1).card = x.card := by
  calc
    (Finset.univ.filter fun i : Fin N => crInput N x i = 1).card =
        (support (crInput N x)).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = x.card := congrArg Finset.card (crInput_support N x hx)
theorem crReadResult_support {N : ℕ} (s : RAMState) (x : Fin N → ZMod 2)
    (h : OutputsSupport s x) : crReadResult N s = some (support x) := by
  have hSet : (outList s).toFinset = support x := by
    ext v
    rw [List.mem_toFinset, crSupport_mem]
    exact h.2 v
  have hLen : s.regs 1 = (support x).card := by
    rw [← hSet, List.toFinset_card_of_nodup h.1]
    simp [outList]
  have hBound : s.regs 1 ≤ N := hLen.trans_le (crSupport_card x)
  rw [crReadResult, if_pos hBound, hSet]
  congr 1
  exact Finset.filter_eq_self.mpr (fun v hv => crSupport_lt x hv)
theorem crFamily_recovers (S : CRSourceBundle) : (crFamily S).Recovers := by
  intro N t ht x hx hxt
  by_cases hN : 1 ≤ N
  · have hCard := crInput_card N x hx
    have hOut := crSource_clock_recovers S N t hN ht (crInput N x) (hCard.trans_le hxt)
    have hSyn := crFamily_sketch S N t x hx
    change (if 1 ≤ N ∧ t ≤ N then _ else some ∅) = some x
    rw [if_pos ⟨hN, ht⟩, crSourceRun, hSyn, crInput_support_vec]
    rw [crReadResult_support _ _ hOut, crInput_support N x hx]
  · have hZero : N = 0 := by omega
    have hEmpty : x = ∅ := by simpa [hZero] using hx
    change (if 1 ≤ N ∧ t ≤ N then _ else some ∅) = some x
    rw [if_neg (fun h => hN h.1), hEmpty]
theorem crFamily_rows (S : CRSourceBundle) (N t : ℕ) (ht : t ≤ N) :
    ((crFamily S).rows N t : ℝ) ≤ S.K * ((t : ℝ) * lg ((N : ℝ) + 2) ^ 2) := by
  by_cases hN : 1 ≤ N
  · exact (S.spec N t hN ht).2.2.1
  · have hInvalid : ¬ (1 ≤ N ∧ t ≤ N) := fun h => hN h.1
    change ((S.data N t).R : ℝ) ≤ _
    rw [S.invalid N t hInvalid]
    simpa only [crSourceEmpty, Nat.cast_zero] using
      mul_nonneg S.K_pos.le (mul_nonneg (Nat.cast_nonneg t) (sq_nonneg (lg ((N : ℝ) + 2))))
theorem crFamily_columns (S : CRSourceBundle) (N t : ℕ) (ht : t ≤ N) (c : ℕ) :
    (((crFamily S).col N t c).card : ℝ) ≤ S.K * lg ((N : ℝ) + 2) ^ 2 := by
  change ((crNatCol S N t c).card : ℝ) ≤ _
  unfold crNatCol
  split_ifs with hc
  · have hN : 1 ≤ N := by omega
    have hImage : (support ((S.data N t).H (Pi.single (⟨c, hc⟩ : Fin N) 1))).card ≤
        (Finset.univ.filter fun i : Fin (S.data N t).R =>
          (S.data N t).H (Pi.single (⟨c, hc⟩ : Fin N) 1) i = 1).card := Finset.card_image_le
    exact (Nat.cast_le.mpr hImage).trans ((S.spec N t hN ht).2.2.2.1 ⟨c, hc⟩)
  · simpa using mul_nonneg S.K_pos.le (sq_nonneg (lg ((N : ℝ) + 2)))
theorem crFamily_range (S : CRSourceBundle) (N t c : ℕ) :
    (crFamily S).col N t c ⊆ Finset.range ((crFamily S).rows N t) :=
  crNatCol_range S N t c
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
@[simp] lemma hN_zero (N : ℕ) : hN N 0 = 0 := by
  unfold hN
  simp
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
open Finset
namespace LinearSetReconciliation327.Main
universe u v
end LinearSetReconciliation327.Main
end
set_option autoImplicit false



#print axioms LinearSetReconciliation327.Main.crFamily_recovers


