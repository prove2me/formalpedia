-- Prove2me | Definitions.Def_DetDLP_S8H4_ElemTiles
-- name    : DetDLP_S8H4_ElemTiles
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:47:55.651588+00:00
-- url     : https://prove2.me/theorems/87a4d177-cede-4330-b9d5-ba4291947b10
-- title:
--   Seven multiply-add tiles and the threshold tile for elliptic factor-block counting
-- statement:
--   For a fixed elliptic-curve element query, a typed arithmetic transcript supplies the assignments of seven multiply-add tiles and a strict-comparison tile. With the affine, curve-equation, and prefix conditions imposed, accepted typed transcripts are in bijection with the points counted by the query. The numeric layout has fewer than $35010(d+2)$ incidences at width $d$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8H_ECPointSlots
import Definitions.Def_DetDLP_S8H_PointAddresses
import Definitions.Def_DetDLP_S8J_CircuitRealizes

set_option autoImplicit false
namespace DetDLP.S8H4.ElemTiles
open S8H S8J ECPointArithmetic ECPointSlots PointAddresses CircuitRealizes M89S1

def testCopies {A : w3_FactorLayout} : (n : ℕ) → (Fin (n+1) → w3_factorTest A) → w3_factorTest (copies A n)
  | 0, t => t 0
  | n+1, t => joinTest (t 0) (testCopies n (fun j => t j.succ))

def bitsCopies {A : w3_FactorLayout} : (n : ℕ) → (Fin (n+1) → Fin A.nb → Bool) → Fin (copies A n).nb → Bool
  | 0, u => u 0
  | n+1, u => Fin.append (u 0) (bitsCopies n (fun j => u j.succ))

theorem copies_iff {A : w3_FactorLayout} (n : ℕ) (t : Fin (n+1) → w3_factorTest A)
    (u : Fin (n+1) → Fin A.nb → Bool) :
    Accept _ (testCopies n t) (bitsCopies n u) ↔ ∀ j, Accept _ (t j) (u j) := by
  induction n with
  | zero => exact ⟨fun h j => by obtain rfl : j = 0 := Fin.ext (by omega); exact h,fun h => h 0⟩
  | succ n ih =>
    erw [testCopies,bitsCopies,HashGateLayout.joined,ih]
    exact ⟨fun h => Fin.cases h.1 h.2,fun h => ⟨h 0,fun j => h j.succ⟩⟩

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (i : Fin m)

abbrev Witness (p : ℕ) := C p × (Transcript p × w3_slotDiff (width p))

def arg (w : Witness p) := args E w.1.2.1 w.1.2.2 (alpha S i w.1.2.2)
  (beta S i w.1.2.2) (fun j => (w.2.1.1 j).1)

noncomputable def hashTests (w : Witness p) := testCopies 6 fun j =>
  HashGateLayout.tests (Nat.succ_pos (bitLen p)) (arg E S i w j).1.val (arg E S i w j).2.1.val (w.2.1.1 j).2

def hashBits (w : Witness p) := bitsCopies (A := HashGateLayout.layout (width p) (Nat.succ_pos _)) 6 fun j =>
  HashGateLayout.encode (Nat.succ_pos _) (arg E S i w j).2.2.val (w.2.1.1 j).1.val (w.2.1.1 j).2 (w.2.1.2 j)

theorem hashes_iff (w : Witness p) : Accept _ (hashTests E S i w) (hashBits E S i w) ↔
    slots E w.1.2.1 w.1.2.2 (alpha S i w.1.2.2) (beta S i w.1.2.2) w.2.1 := by
  unfold hashTests hashBits
  rw [copies_iff]
  exact forall_congr' fun j => HashGateLayout.encode_iff ..

abbrev layout (p : ℕ) := join (seven (Nat.succ_pos (bitLen p))) (lessBlock (width p)).A

def code (d : ℕ) := sum (sevenCode d) (add (d+1))
theorem models (p : ℕ) : Models (code (width p)) (layout p) := sum_spec (seven_spec _) (add_spec _)
theorem uniform : Uniform code := sum_poly seven_poly (add_poly _ (by intros; exact Groundwork.PolyT.add ‹_› (Groundwork.PolyT.const 1)))
theorem edges (p : ℕ) : (layout p).ne < 35010 * (width p + 2) := by
  have h := seven_edges (Nat.succ_pos (bitLen p))
  change (seven _).ne + (width p+1)*5 < _
  unfold width; omega

noncomputable def tests (w : Witness p) : w3_factorTest (layout p) :=
  joinTest (hashTests E S i w) (lessBlock (width p)).t

def bits (T : ℕ) (w : Witness p) : Fin (layout p).nb → Bool :=
  Fin.append (hashBits E S i w) (HashGateLayout.addBits (w.2.1.1 6).1.val w.2.2.1.val T w.2.2.2)

def pins (b : ℕ) (η : List Bool) (w : Witness p) : Prop :=
  checkCurve w.1 w.2.1 ∧ w.1.1 = false ∧ (word b w.1).take η.length = η

theorem encode_iff (T b : ℕ) (η : List Bool) (w : Witness p) :
    Accept _ (tests E S i w) (bits E S i T w) ∧ pins b η w ↔ elemOK E S i T b η w := by
  unfold tests bits pins elemOK
  erw [HashGateLayout.joined,hashes_iff,lessBlock_iff]; tauto

def accepted (T b : ℕ) (η : List Bool) := {w : Witness p //
  Accept _ (tests E S i w) (bits E S i T w) ∧ pins b η w}

noncomputable def pointEquiv [E.IsElliptic] (mul : w3_modMulInterface) (T b : ℕ)
    (hT : T ≤ p) (η : List Bool) : accepted E S i T b η ≃
    {P : E.toAffine.Point // ECPointGadget.elemPin b T S i η P = true} :=
  (Equiv.subtypeEquivRight fun w => encode_iff E S i T b η w).trans (elemEquiv mul S i T b hT η)

theorem card [E.IsElliptic] (mul : w3_modMulInterface) (T : ℕ) (hT : T ≤ p) (η : List Bool) :
    Nat.card (accepted E S i T (bitLen p) η) = elemCount (ecFactorBlock E T S i) (ecWord (bitLen p)) η := by
  classical
  letI := ecPointFintype E
  rw [Nat.card_congr (pointEquiv E S i mul T (bitLen p) hT η),Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp [elemCount, ecFactorBlock, ECPointGadget.elemPin, Finset.filter_filter]

end DetDLP.S8H4.ElemTiles


