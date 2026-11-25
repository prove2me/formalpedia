-- Prove2me | Definitions.Def_DetDLP_W3_ModMul
-- name    : DetDLP_W3_ModMul
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T21:35:38.678834+00:00
-- url     : https://prove2.me/theorems/04cded04-5958-42eb-a269-ab623c618705
-- title:
--   R2 modular multiplication on the concrete M5 edge assignment
-- statement:
--   Defines the external bus of the numbered $d$-bit multiplication BTN. At a power-of-two modulus, the unique full product is constrained only on its low $d$ bits. At a strictly smaller modulus, two product runs and a quotient word enforce Euclidean division. The predicates quantify the internal M5 edge assignments and require satisfaction at every ordered-port tensor.
-- source:
--   Deterministic Discrete Logarithms, Section 2.3 Lemmas 2.3–2.4 and Section 4.2(1). Referee revision R2.

import Definitions.Def_DetDLP_W4_M5PortTensor

set_option autoImplicit false
namespace DetDLP
open w4_M5GraphBounds w4_M5PortTensor

/-- Physical external word for the M5 multiplier in input-input-output order. -/
def w3_mulBus (d x y u : ℕ) (i : Fin (4*d)) : Bool :=
  if i.val < d then x.testBit i.val else if i.val < 2*d then y.testBit (i.val-d) else u.testBit (i.val-2*d)

abbrev w3_mulRun (d : ℕ) (hd : 1 ≤ d) := Fin (2^(2*d)) × (Fin (graph d hd).nE → Bool)

def w3_mulPins {d : ℕ} (hd : 1 ≤ d) (x y : ℕ) (r : w3_mulRun d hd) : Prop :=
  (∀ i, r.2 (ext hd i) = w3_mulBus d x y r.1.val i) ∧
  ∀ v, tensor hd v (fun j => r.2 (((graph d hd).ports v).get j)) = true

/-- Power-of-two branch. The $d$ low output bits of the unique full product are pinned to $z$. -/
def w3_modOne {d : ℕ} (hd : 1 ≤ d) (x y z : ℕ) (r : w3_mulRun d hd) : Prop :=
  w3_mulPins hd x y r ∧ ∀ i : Fin d, r.1.val.testBit i.val = z.testBit i.val

/-- Strict-modulus branch. The public modulus fits in $d$ bits and the quotient is a $d$-bit word. -/
def w3_modTwo {d : ℕ} (hd : 1 ≤ d) (q x y z : ℕ)
    (r : Fin (2^d) × w3_mulRun d hd × w3_mulRun d hd) : Prop :=
  w3_mulPins hd x y r.2.1 ∧ w3_mulPins hd r.1.val q r.2.2 ∧ r.2.2.1.val + z = r.2.1.1.val

def w3_modMulInterface : Prop := ∀ (d : ℕ) (hd : 1 ≤ d) (q x y z : ℕ),
  2 ≤ q → q ≤ 2^d → x < q → y < q → z < q →
  (q = 2^d → (z = (x*y)%q → ∃! r, w3_modOne hd x y z r) ∧
    (∀ r, w3_modOne hd x y z r → z = (x*y)%q)) ∧
  (q < 2^d → (z = (x*y)%q → ∃! r, w3_modTwo hd q x y z r) ∧
    (∀ r, w3_modTwo hd q x y z r → z = (x*y)%q))

end DetDLP


