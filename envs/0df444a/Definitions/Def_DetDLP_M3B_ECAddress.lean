-- Prove2me | Definitions.Def_DetDLP_M3B_ECAddress
-- name    : DetDLP_M3B_ECAddress
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:10:05.080017+00:00
-- url     : https://prove2.me/theorems/845a6844-12d8-4234-8b23-6cf0098b035d
-- title:
--   Stage II EC native slot address correctness
-- statement:
--   Identifies the checked slot's residue and parity offset with the native address of its decoded indexed block point and proves its strict range bound.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECCert

set_option autoImplicit false
namespace DetDLP.M3B.ECAddress
open ECCert S8H4 S8H.ECPointArithmetic S8H.ECPointSlots

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (S : ECSeed p m) (T : ℕ) (i : Fin m)

def parity (y : ZMod p) := decide (y.val % 2 = 1)

def address : Point E → ℕ
  | .zero => 2*T
  | .some x y _ =>
    let s := parity y
    let ab := S i s
    ((ab.1.val+1)*x.val+ab.2.val)%p + (if s then T else 0)

/-- The numeric wire address is the hash plus the selected bank offset, not
    a concatenation at a power-of-two boundary. -/
def read (w : Slot E S T i) :=
  (w.1.2.1.1 6).1.val + (if parity w.1.1.2.2 then T else 0)

theorem slot_semantics (w : Slot E S T i) : elemOK E S i T (bitLen p) [] w.1 :=
  (ElemTiles.encode_iff E S i T (bitLen p) [] w.1).mp w.2

theorem read_bound (hT : T ≤ p) (w : Slot E S T i) : read E S T i w < 2*T := by
  have h := slot_semantics E S T i w
  have hfit := (w.1.2.1.1 6).1.val_lt.trans (fits p)
  have ht : (w.1.2.1.1 6).1.val < T := by
    exact (w3_slotLt_spec hfit (hT.trans (fits p).le)).1 _ h.2.2.2.1
  unfold read
  split <;> omega

variable (F : Fin m → List (Point E)) (mul : w3_modMulInterface) (hT : T ≤ p)
variable (hF : ListsOK E F S T)

theorem coords_get (w : Slot E S T i) :
    coords ((F i).get (indexEquiv E F S T mul hT hF i w)) = w.1.1 := by
  classical
  let u := ElemTiles.pointEquiv E S i mul T (bitLen p) hT [] w
  let e := (hF i).1.getEquiv (F i)
  have hm : u.val ∈ F i := by
    rw [← List.mem_toFinset, (hF i).2]
    simpa [S8H.ECPointGadget.elemPin,ecFactorBlock] using u.prop
  have hg := congrArg Subtype.val (e.apply_symm_apply ⟨u.val,hm⟩)
  change coords ((F i).get (e.symm ⟨u.val,hm⟩)) = w.val.1
  change (F i).get (e.symm ⟨u.val,hm⟩) = u.val at hg
  rw [hg]
  exact coords_decode _

theorem read_eq (w : Slot E S T i) : read E S T i w =
    address E S T i ((F i).get (indexEquiv E F S T mul hT hF i w)) := by
  have hc := coords_get E S T i F mul hT hF w
  have ho := slot_semantics E S T i w
  have hv := congrArg ZMod.val (values mul ho.1 6)
  have hn := ho.2.2.1
  generalize he : (F i).get (indexEquiv E F S T mul hT hF i w) = A at hc ⊢
  cases A with
  | zero =>
    have := congrArg Prod.fst hc
    simp [coords, hn] at this
  | some x y h =>
    have hx := congrArg (fun c : C p => c.2.1) hc
    have hy := congrArg (fun c : C p => c.2.2) hc
    change x = w.1.1.2.1 at hx
    change y = w.1.1.2.2 at hy
    subst x; subst y
    let yy := w.1.1.2.2
    have ha : (S i (parity yy)).1.val+1 < p := by have := (S i (parity yy)).1.isLt; omega
    have ea : (alpha S i yy).val = (S i (parity yy)).1.val+1 := ZMod.val_natCast_of_lt ha
    have eb : (beta S i yy).val = (S i (parity yy)).2.val := ZMod.val_natCast_of_lt (S i (parity yy)).2.isLt
    unfold read address
    rw [hv,hash_value,ea,eb]

end DetDLP.M3B.ECAddress


