-- Prove2me | Definitions.Def_DetDLP_S8H0_SevenChecks
-- name    : DetDLP_S8H0_SevenChecks
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:41:32.60351+00:00
-- url     : https://prove2.me/theorems/94fd37a8-c41d-451c-a86a-effcb7b03f6b
-- title:
--   Witness-independent arithmetic checks for the seven elliptic-curve blocks
-- statement:
--   For each hash block, separate the intrinsic multiplier and adder tests from the two external bus equalities. Compose the same witness-independent tests on seven disjoint copies. On encoded coordinate transcripts with the prescribed buses and final curve predicate, the accepting transcripts are in bijection with the affine curve points, including infinity.
-- source:
--   Companion to DetDLP.s8h_ec_order_query (f0e81f0e-6143-4672-a126-0c2b5aa2d552); S8H point addresses and point slots.

import Definitions.Def_DetDLP_S8H_PointAddresses
import Definitions.Def_DetDLP_S8H_ECPointSlots

set_option autoImplicit false
namespace DetDLP.S8H0.SevenChecks
open S8J S8J.HashGateLayout S8H.PointAddresses S8H.ECPointArithmetic S8H.ECPointSlots

def body {d : ℕ} (hd : 1 ≤ d) : w3_factorTest (layout d hd) :=
  joinTest (joinTest (w3_fpMulTests d hd) (w3_fpMulTests d hd))
    (joinTest (S8C.AddLayout.test false) (joinTest (S8C.AddLayout.test false) (S8C.AddLayout.test false)))

def buses {d p : ℕ} (hd : 1 ≤ d) (a x : ℕ) (r : w3_fpHashCert d p hd) :=
  (∀ i, r.1.2.2.1.2 (w4_M5PortTensor.ext hd i) = w3_mulBus d a x r.1.2.2.1.1.val i) ∧
  (∀ i, r.1.2.2.2.2 (w4_M5PortTensor.ext hd i) = w3_mulBus d r.1.2.1.val p r.1.2.2.2.1.val i)

set_option maxHeartbeats 2000000 in
theorem body_iff {d p : ℕ} (hd : 1 ≤ d) (a b x z : ℕ) (r : w3_fpHashCert d p hd)
    (w : w3_slotHashAux d) :
    Accept _ (body hd) (encode hd b z r w) ∧ buses hd a x r ↔ w3_slotHashBits hd a b x z r w := by
  unfold body encode layout
  erw [joined,joined,joined,joined]
  let m := r.1.2
  have H₃ := addBits_iff (by omega : 0 < 2*d) m.2.2.1.val r.1.1.val m.2.1.1.val false w.1
  have H₄ := addBits_iff (by omega : 0 < d+1) r.1.1.val b w.2.1.val false w.2.2.1
  have H₅ := addBits_iff (by omega : 0 < d+1) z (if r.2 then p else 0) w.2.1.val false w.2.2.2
  constructor
  · rintro ⟨⟨⟨u,v⟩,t,l,k⟩,h,j⟩
    exact ⟨⟨⟨h,u⟩,⟨j,v⟩,H₃.mp t⟩,H₄.mp l,H₅.mp k⟩
  · rintro ⟨⟨⟨h,u⟩,⟨j,v⟩,t⟩,l,k⟩
    exact ⟨⟨⟨u,v⟩,H₃.mpr t,H₄.mpr l,H₅.mpr k⟩,h,j⟩

variable {A : w3_FactorLayout}

def copyTest (t : w3_factorTest A) : (n : ℕ) → w3_factorTest (copies A n)
  | 0 => t
  | n+1 => joinTest t (copyTest t n)

def copyBits : (n : ℕ) → (Fin (n+1) → Fin A.nb → Bool) → Fin (copies A n).nb → Bool
  | 0, f => f 0
  | n+1, f => Fin.append (f 0) (copyBits n (fun i => f i.succ))

theorem copy_iff (t : w3_factorTest A) (n : ℕ) (f : Fin (n+1) → Fin A.nb → Bool) :
    Accept _ (copyTest t n) (copyBits (A := A) n f) ↔ ∀ i, Accept A t (f i) := by
  induction n with
  | zero =>
    refine ⟨?_,fun h => h 0⟩
    intro h i
    have hi : i = 0 := Fin.ext (by omega); subst i; exact h
  | succ n ih =>
    erw [copyTest, copyBits, joined, ih]
    exact ⟨fun h i => Fin.cases h.1 h.2 i,fun h => ⟨h 0,fun i => h i.succ⟩⟩

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

def gateArgs (c : C p) (t : Transcript p) := args E c.2.1 c.2.2 0 0 (fun i => (t.1 i).1)

def sevenBits (c : C p) (t : Transcript p) : Fin (seven (Nat.succ_pos (bitLen p))).nb → Bool :=
  copyBits 6 (A := layout (width p) (Nat.succ_pos _)) fun i =>
    encode (Nat.succ_pos _) (gateArgs E c t i).2.2.val (t.1 i).1.val (t.1 i).2 (t.2 i)

def sevenBuses (c : C p) (t : Transcript p) := ∀ i,
  buses (Nat.succ_pos _) (gateArgs E c t i).1.val (gateArgs E c t i).2.1.val (t.1 i).2

theorem seven_iff (c : C p) (t : Transcript p) :
    Accept _ (copyTest (body (Nat.succ_pos (bitLen p))) 6) (sevenBits E c t) ∧ sevenBuses E c t
      ↔ slots E c.2.1 c.2.2 0 0 t := by
  unfold sevenBits
  rw [copy_iff]
  let h (i : Fin 7) := body_iff (Nat.succ_pos (bitLen p)) (gateArgs E c t i).1.val
    (gateArgs E c t i).2.2.val (gateArgs E c t i).2.1.val (t.1 i).1.val (t.1 i).2 (t.2 i)
  exact ⟨fun ⟨u,v⟩ i => (h i).mp ⟨u i,v i⟩,
    fun s => ⟨fun i => ((h i).mpr (s i)).1,fun i => ((h i).mpr (s i)).2⟩⟩

def physical (c : C p) (t : Transcript p) :=
  (Accept _ (copyTest (body (Nat.succ_pos (bitLen p))) 6) (sevenBits E c t) ∧ sevenBuses E c t) ∧
    checkCurve c t

theorem physical_iff (c : C p) (t : Transcript p) : physical E c t ↔ orderOK E (c,t) :=
  and_congr_left' (seven_iff E c t)

noncomputable def pointEquiv (mul : w3_modMulInterface) [E.IsElliptic] :
    {w : C p × Transcript p // physical E w.1 w.2} ≃ E.toAffine.Point :=
  (Equiv.subtypeEquivRight (p := fun w : C p × Transcript p => physical E w.1 w.2)
    (q := fun w : C p × Transcript p => orderOK E w)
    (fun w => physical_iff E w.1 w.2)).trans (orderEquiv mul E)

end DetDLP.S8H0.SevenChecks


