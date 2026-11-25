-- Prove2me | Definitions.Def_DetDLP_M3B_ECAddrGadget
-- name    : DetDLP_M3B_ECAddrGadget
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:22:20.037887+00:00
-- url     : https://prove2.me/theorems/0b255320-31a2-43ae-b012-44006770d951
-- title:
--   EC native lookup address selector and adder
-- statement:
--   Checks a parity-selected threshold and a ripple-carry sum using witness-independent named rows; proves unique completions, high-bit vanishing, and exact low-bit native lookup addresses.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECAddress
import Definitions.Def_DetDLP_S8H0_NamedBlocks

set_option autoImplicit false
namespace DetDLP.M3B.ECAddrGadget
open S8H0 S8H0.NamedBlocks S8H0.RegisterMap
open OAI.Algorithms.SubexponentialSAT w4_ConvolutionArithmetic

abbrev Bits (d : ℕ) := Fin d → Bool
abbrev Aux (d : ℕ) := Bits d × Bits d × Bits d
def width (p k : ℕ) := max (bitLen p + 1) k
def digits (d n : ℕ) : Bits d := fun i => n.testBit i.val
def offset (s : Bool) (T : ℕ) := if s then T else 0

def good {d : ℕ} (T : ℕ) (s : Bool) (h : Bits d) (u : Aux d) :=
  (∀ i, u.1 i = (s && T.testBit i.val)) ∧
    S8C.AddLayout.Columns false h u.1 u.2.1 u.2.2

/-- The threshold is public; the selector and the hash are named input wires. -/
def block {r : Shape} {d : ℕ} (T : ℕ) (s : Ref r) (h t z c : Fin d → Ref r) :=
  joinB (rows d 2 (fun i => ![s,t i]) (fun i a => decide (a 1 = (a 0 && T.testBit i.val))))
    (add false h t z c)

theorem block_iff {r : Shape} {d : ℕ} (T : ℕ) (s : Ref r) (h t z c : Fin d → Ref r)
    (x : Fin (r.size+1) → Bool) :
    (block T s h t z c).OK x ↔ good T (s.eval x) (fun i => (h i).eval x)
      (fun i => (t i).eval x, fun i => (z i).eval x, fun i => (c i).eval x) := by
  rw [block,joinB_iff,rows_iff,add_iff]; simp [good]

theorem edges {r : Shape} {d : ℕ} (T : ℕ) (s : Ref r) (h t z c : Fin d → Ref r) :
    (block T s h t z c).core.A.ne = 7*d := by change d*2+d*5 = _; omega

private theorem select_digit {d : ℕ} (s : Bool) (T : ℕ) (i : Fin d) :
    digits d (offset s T) i = (s && T.testBit i.val) := by cases s <;> simp [digits,offset]

private theorem selected {d : ℕ} {s : Bool} {T : ℕ} {h : Bits d} {u : Aux d}
    (H : good T s h u) : u.1 = digits d (offset s T) :=
  funext fun i => (H.1 i).trans (select_digit s T i).symm

private theorem decode_digit {d : ℕ} (z : Bits d) :
    digits d (ResidueWires.value z).val = z := funext (ResidueWires.value_bit z)

private theorem replay {d a T : ℕ} {s : Bool} {u : Aux d} (hd : 0 < d)
    (H : good T s (digits d a) u) : w3_addColumns d a (offset s T) (ResidueWires.value u.2.1).val false u.2.2 := by
  apply (S8C.AddLayout.columns_iff hd ..).mp
  change S8C.AddLayout.Columns false (digits d a) (digits d (offset s T))
    (digits d (ResidueWires.value u.2.1).val) u.2.2
  rw [decode_digit,← selected H]; exact H.2

theorem output {d a T : ℕ} {s : Bool} {u : Aux d} (hd : 0 < d)
    (ha : a + offset s T < 2^d) (H : good T s (digits d a) u) :
    u.2.1 = digits d (a + offset s T) := by
  have hh := w3_addColumns_sound (by omega) (by omega) (ResidueWires.value u.2.1).isLt (replay hd H)
  simp only [Bool.toNat_false,Nat.add_zero] at hh
  rw [hh,decode_digit]

theorem unique {d a T : ℕ} {s : Bool} (hd : 0 < d) (ha : a + offset s T < 2^d) :
    ∃! u : Aux d, good T s (digits d a) u := by
  obtain ⟨c,hc,uc⟩ := w3_addColumns_unique (cin := false) (a := a) (b := offset s T)
    (by omega) (by omega) ha (by simp)
  refine ⟨(digits d (offset s T), digits d (a + offset s T),c),
    ⟨select_digit s T, (S8C.AddLayout.columns_iff hd ..).mpr hc⟩,?_⟩
  intro u hu
  have hz := output hd ha hu
  refine Prod.ext (selected hu) (Prod.ext hz (uc _ ?_))
  apply (S8C.AddLayout.columns_iff hd ..).mp
  change S8C.AddLayout.Columns false (digits d a) (digits d (offset s T)) (digits d (a+offset s T)) u.2.2
  rw [← selected hu,← hz]; exact hu.2

variable {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} [E.IsElliptic]
variable {S : ECSeed p m} {T : ℕ} {i : Fin m} (w : ECCert.Slot E S T i) (k : ℕ)

abbrev hash := (w.1.2.1.1 6).1.val
abbrev odd := ECAddress.parity w.1.1.2.2
def slotOK := good T (odd w) (digits (width p k) (hash w))

private theorem fits (hT : T ≤ p) (hk : 2*T ≤ 2^k) :
    hash w + offset (odd w) T < 2^(width p k) :=
  ((ECAddress.read_bound E S T i hT w).trans_le hk).trans_le
    (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

theorem slot_unique (hT : T ≤ p) (hk : 2*T ≤ 2^k) : ∃! u, slotOK w k u :=
  unique (by unfold width; omega) (fits w k hT hk)

theorem slot_digits (hT : T ≤ p) (hk : 2*T ≤ 2^k) {u : Aux (width p k)} (H : slotOK w k u) :
    u.2.1 = digits (width p k) (ECAddress.read E S T i w) :=
  output (by unfold width; omega) (fits w k hT hk) H

theorem high_zero (hT : T ≤ p) (hk : 2*T ≤ 2^k) {u : Aux (width p k)} (H : slotOK w k u)
    (j : Fin (width p k)) (hj : k ≤ j.val) : u.2.1 j = false := by
  rw [slot_digits w k hT hk H]
  exact Nat.testBit_eq_false_of_lt (((ECAddress.read_bound E S T i hT w).trans_le hk).trans_le
    (Nat.pow_le_pow_right (by decide) hj))

def low {p k : ℕ} (u : Aux (width p k)) : Bits k := fun j => u.2.1 (Fin.castLE (le_max_right _ _) j)

theorem low_value (hT : T ≤ p) (hk : 2*T ≤ 2^k) {u : Aux (width p k)} (H : slotOK w k u) :
    bitsToNat (low u) = ECAddress.read E S T i w := by
  have hu : low u = canonicalBits k (ECAddress.read E S T i w) := by
    funext j; unfold low; rw [slot_digits w k hT hk H]; exact Nat.testBit_eq_decide_div_mod_eq ..
  rw [hu,bitsToNat_canonicalBits ((ECAddress.read_bound E S T i hT w).trans_le hk)]

theorem low_address (F : Fin m → List (ECCert.Point E)) (mul : w3_modMulInterface) (hT : T ≤ p)
    (hF : ECCert.ListsOK E F S T) (hk : 2*T ≤ 2^k) {u : Aux (width p k)} (H : slotOK w k u) :
    bitsToNat (low u) = ECAddress.address E S T i ((F i).get (ECCert.indexEquiv E F S T mul hT hF i w)) :=
  (low_value w k hT hk H).trans (ECAddress.read_eq E S T i F mul hT hF w)

end DetDLP.M3B.ECAddrGadget


