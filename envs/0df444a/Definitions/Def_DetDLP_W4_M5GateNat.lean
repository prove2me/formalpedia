-- Prove2me | Definitions.Def_DetDLP_W4_M5GateNat
-- name    : DetDLP_W4_M5GateNat
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:27:15.42781+00:00
-- url     : https://prove2.me/theorems/b2ceaeca-517d-41f0-ac17-8e132479534d
-- title:
--   Polynomial-time natural arithmetic for evaluator gate checks
-- statement:
--   The eight local checks can be evaluated using unary-bounded loops over natural-number bit indices, polynomial-time edge reads, and polynomially bounded Fermat arithmetic.

import Definitions.Def_DetDLP_W4_M5GateOps
set_option autoImplicit false
namespace DetDLP.w4_M5GateNat
open Groundwork Groundwork.PolyT w4_MulParams w4_M5GraphBounds w4_M5EdgeNat w4_M5Evaluator w4_M5GateOps
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.div Groundwork.PolyT.mod Groundwork.PolyT.mul Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.length P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 J_poly n0_poly L1_poly L2_poly mu_poly pow2_poly sumN_poly allN_poly word_poly Q_poly rootPow_poly invPow_poly invScale_poly wire_poly
attribute [local irreducible] wire word pow2 cap sumN allN Q rootPow invPow invScale J n0 L1 L2
set_option maxHeartbeats 180000
abbrev Ctx := Pad × ℕ × List Bool
abbrev pad (c : Ctx) := c.1
abbrev dim (c : Ctx) := c.1.length

def b0 (c : Ctx) (x0 x1 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 0 (x1 + ((dim c))*(x0)))
@[local fun_prop] theorem b0_poly {α} [Enc α] {c : α → Ctx} {x0 x1 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) : PolyT (fun x => b0 (c x) (x0 x) (x1 x)) := by simp only [b0,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b0

def b1 (c : Ctx) (x0 x1 x2 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 1 ((x2 + (W (dim c))*(x1)) + ((n0 (dim c))*(W (dim c)))*(x0)))
@[local fun_prop] theorem b1_poly {α} [Enc α] {c : α → Ctx} {x0 x1 x2 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) (hx2 : PolyT x2) : PolyT (fun x => b1 (c x) (x0 x) (x1 x) (x2 x)) := by simp only [b1,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b1

def w1 (c : Ctx) (x0 x1 : ℕ) : ℕ := word (pad c) (W (dim c)) (fun i => b1 c x0 x1 i)
@[local fun_prop] theorem w1_poly {α} [Enc α] {c : α → Ctx} {x0 x1 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) : PolyT (fun x => w1 (c x) (x0 x) (x1 x)) := by unfold w1; fun_prop
attribute [local irreducible] w1

def b2 (c : Ctx) (x0 x1 x2 x3 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 2 (((x3 + (W (dim c))*(x2)) + ((L1 (dim c))*(W (dim c)))*(x1)) + ((L2 (dim c))*((L1 (dim c))*(W (dim c))))*(x0)))
@[local fun_prop] theorem b2_poly {α} [Enc α] {c : α → Ctx} {x0 x1 x2 x3 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) (hx2 : PolyT x2) (hx3 : PolyT x3) : PolyT (fun x => b2 (c x) (x0 x) (x1 x) (x2 x) (x3 x)) := by simp only [b2,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b2

def w2 (c : Ctx) (x0 x1 x2 : ℕ) : ℕ := word (pad c) (W (dim c)) (fun i => b2 c x0 x1 x2 i)
@[local fun_prop] theorem w2_poly {α} [Enc α] {c : α → Ctx} {x0 x1 x2 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) (hx2 : PolyT x2) : PolyT (fun x => w2 (c x) (x0 x) (x1 x) (x2 x)) := by unfold w2; fun_prop
attribute [local irreducible] w2

def b3 (c : Ctx) (x0 x1 x2 x3 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 3 (((x3 + (W (dim c))*(x2)) + ((L1 (dim c))*(W (dim c)))*(x1)) + ((L2 (dim c))*((L1 (dim c))*(W (dim c))))*(x0)))
@[local fun_prop] theorem b3_poly {α} [Enc α] {c : α → Ctx} {x0 x1 x2 x3 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) (hx2 : PolyT x2) (hx3 : PolyT x3) : PolyT (fun x => b3 (c x) (x0 x) (x1 x) (x2 x) (x3 x)) := by simp only [b3,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b3

def w3 (c : Ctx) (x0 x1 x2 : ℕ) : ℕ := word (pad c) (W (dim c)) (fun i => b3 c x0 x1 x2 i)
@[local fun_prop] theorem w3_poly {α} [Enc α] {c : α → Ctx} {x0 x1 x2 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) (hx2 : PolyT x2) : PolyT (fun x => w3 (c x) (x0 x) (x1 x) (x2 x)) := by unfold w3; fun_prop
attribute [local irreducible] w3

def b4 (c : Ctx) (x0 x1 x2 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 4 ((x2 + (W (dim c))*(x1)) + ((L1 (dim c))*(W (dim c)))*(x0)))
@[local fun_prop] theorem b4_poly {α} [Enc α] {c : α → Ctx} {x0 x1 x2 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) (hx2 : PolyT x2) : PolyT (fun x => b4 (c x) (x0 x) (x1 x) (x2 x)) := by simp only [b4,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b4

def w4 (c : Ctx) (x0 x1 : ℕ) : ℕ := word (pad c) (W (dim c)) (fun i => b4 c x0 x1 i)
@[local fun_prop] theorem w4_poly {α} [Enc α] {c : α → Ctx} {x0 x1 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) : PolyT (fun x => w4 (c x) (x0 x) (x1 x)) := by unfold w4; fun_prop
attribute [local irreducible] w4

def b5 (c : Ctx) (x0 x1 x2 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 5 ((x2 + (W (dim c))*(x1)) + ((L1 (dim c))*(W (dim c)))*(x0)))
@[local fun_prop] theorem b5_poly {α} [Enc α] {c : α → Ctx} {x0 x1 x2 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) (hx2 : PolyT x2) : PolyT (fun x => b5 (c x) (x0 x) (x1 x) (x2 x)) := by simp only [b5,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b5

def w5 (c : Ctx) (x0 x1 : ℕ) : ℕ := word (pad c) (W (dim c)) (fun i => b5 c x0 x1 i)
@[local fun_prop] theorem w5_poly {α} [Enc α] {c : α → Ctx} {x0 x1 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) : PolyT (fun x => w5 (c x) (x0 x) (x1 x)) := by unfold w5; fun_prop
attribute [local irreducible] w5

def b6 (c : Ctx) (x0 x1 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 6 (x1 + (W (dim c))*(x0)))
@[local fun_prop] theorem b6_poly {α} [Enc α] {c : α → Ctx} {x0 x1 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) : PolyT (fun x => b6 (c x) (x0 x) (x1 x)) := by simp only [b6,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b6

def w6 (c : Ctx) (x0 : ℕ) : ℕ := word (pad c) (W (dim c)) (fun i => b6 c x0 i)
@[local fun_prop] theorem w6_poly {α} [Enc α] {c : α → Ctx} {x0 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) : PolyT (fun x => w6 (c x) (x0 x)) := by unfold w6; fun_prop
attribute [local irreducible] w6

def b7 (c : Ctx) (x0 x1 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 7 (x1 + (W (dim c))*(x0)))
@[local fun_prop] theorem b7_poly {α} [Enc α] {c : α → Ctx} {x0 x1 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) : PolyT (fun x => b7 (c x) (x0 x) (x1 x)) := by simp only [b7,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b7

def w7 (c : Ctx) (x0 : ℕ) : ℕ := word (pad c) (W (dim c)) (fun i => b7 c x0 i)
@[local fun_prop] theorem w7_poly {α} [Enc α] {c : α → Ctx} {x0 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) : PolyT (fun x => w7 (c x) (x0 x)) := by unfold w7; fun_prop
attribute [local irreducible] w7

def b8 (c : Ctx) (x0 x1 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 8 (x1 + (W (dim c))*(x0)))
@[local fun_prop] theorem b8_poly {α} [Enc α] {c : α → Ctx} {x0 x1 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) (hx1 : PolyT x1) : PolyT (fun x => b8 (c x) (x0 x) (x1 x)) := by simp only [b8,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b8

def w8 (c : Ctx) (x0 : ℕ) : ℕ := word (pad c) (W (dim c)) (fun i => b8 c x0 i)
@[local fun_prop] theorem w8_poly {α} [Enc α] {c : α → Ctx} {x0 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) : PolyT (fun x => w8 (c x) (x0 x)) := by unfold w8; fun_prop
attribute [local irreducible] w8

def b9 (c : Ctx) (x0 : ℕ) : Bool := wire (pad c) c.2.1 c.2.2 (edgeBase (dim c) 9 x0)
@[local fun_prop] theorem b9_poly {α} [Enc α] {c : α → Ctx} {x0 : α → ℕ} (hc : PolyT c) (hx0 : PolyT x0) : PolyT (fun x => b9 (c x) (x0 x)) := by simp only [b9,edgeBase,W,pad,dim]; fun_prop
attribute [local irreducible] b9

def inDigit (c : Ctx) (t u : ℕ) : ℕ := word (pad c) (k (dim c)) fun i => if k (dim c)*u+i < dim c then b0 c t (k (dim c)*u+i) else false
@[local fun_prop] theorem inDigit_poly {α} [Enc α] {c : α → Ctx} {t u : α → ℕ} (hc : PolyT c) (ht : PolyT t) (hu : PolyT u) : PolyT (fun x => inDigit (c x) (t x) (u x)) := by simp only [inDigit,k]; fun_prop
attribute [local irreducible] inDigit

def outDigit (c : Ctx) (u : ℕ) : ℕ := word (pad c) (k (dim c)) fun i => if k (dim c)*u+i < 2*dim c then b9 c (k (dim c)*u+i) else false
@[local fun_prop] theorem outDigit_poly {α} [Enc α] {c : α → Ctx} {u : α → ℕ} (hc : PolyT c) (hu : PolyT u) : PolyT (fun x => outDigit (c x) (u x)) := by simp only [outDigit,k]; fun_prop
attribute [local irreducible] outDigit

def packed (c : Ctx) (t i : ℕ) : ℕ := if i < n0 (dim c) then w1 c t i else 0
@[local fun_prop] theorem packed_poly {α} [Enc α] {c : α → Ctx} {t i : α → ℕ} (hc : PolyT c) (ht : PolyT t) (hi : PolyT i) : PolyT (fun x => packed (c x) (t x) (i x)) := by unfold packed; fun_prop
attribute [local irreducible] packed

def first (c : Ctx) (t i b : ℕ) : ℕ := rootPow (pad c) (b*i) * sumN (pad c) (L1 (dim c)) (fun j => rootPow (pad c) (L2 (dim c)*j*i) * packed c t (L2 (dim c)*j+b))
@[local fun_prop] theorem first_poly {α} [Enc α] {c : α → Ctx} {t i b : α → ℕ} (hc : PolyT c) (ht : PolyT t) (hi : PolyT i) (hb : PolyT b) : PolyT (fun x => first (c x) (t x) (i x) (b x)) := by unfold first; fun_prop
attribute [local irreducible] first

def second (c : Ctx) (t i b : ℕ) : ℕ := sumN (pad c) (L2 (dim c)) (fun j => rootPow (pad c) (L1 (dim c)*j*b) * w2 c t j i)
@[local fun_prop] theorem second_poly {α} [Enc α] {c : α → Ctx} {t i b : α → ℕ} (hc : PolyT c) (ht : PolyT t) (hi : PolyT i) (hb : PolyT b) : PolyT (fun x => second (c x) (t x) (i x) (b x)) := by unfold second; fun_prop
attribute [local irreducible] second

def third (c : Ctx) (i b : ℕ) : ℕ := sumN (pad c) (L2 (dim c)) (fun j => invPow (pad c) (L1 (dim c)*b*j) * w4 c j i)
@[local fun_prop] theorem third_poly {α} [Enc α] {c : α → Ctx} {i b : α → ℕ} (hc : PolyT c) (hi : PolyT i) (hb : PolyT b) : PolyT (fun x => third (c x) (i x) (b x)) := by unfold third; fun_prop
attribute [local irreducible] third

def fourth (c : Ctx) (u : ℕ) : ℕ := invScale (pad c) * sumN (pad c) (L1 (dim c)) (fun i => invPow (pad c) ((L2 (dim c)*(u / L2 (dim c))+u % L2 (dim c))*i) * w5 c (u % L2 (dim c)) i)
@[local fun_prop] theorem fourth_poly {α} [Enc α] {c : α → Ctx} {u : α → ℕ} (hc : PolyT c) (hu : PolyT u) : PolyT (fun x => fourth (c x) (u x)) := by unfold fourth; fun_prop
attribute [local irreducible] fourth

def linkL (c : Ctx) (j : ℕ) : ℕ := if 0 < j then if j < 2*n0 (dim c) then w7 c (j-1) else 0 else 0
@[local fun_prop] theorem linkL_poly {α} [Enc α] {c : α → Ctx} {j : α → ℕ} (hc : PolyT c) (hj : PolyT j) : PolyT (fun x => linkL (c x) (j x)) := by unfold linkL; fun_prop
attribute [local irreducible] linkL

def linkR (c : Ctx) (j : ℕ) : ℕ := if 0 < j then if j < 2*n0 (dim c) then w8 c (j-1) else 0 else 0
@[local fun_prop] theorem linkR_poly {α} [Enc α] {c : α → Ctx} {j : α → ℕ} (hc : PolyT c) (hj : PolyT j) : PolyT (fun x => linkR (c x) (j x)) := by unfold linkR; fun_prop
attribute [local irreducible] linkR

def pack (c : Ctx) (t u : ℕ) : Bool := decide (w1 c t u = inDigit c t u % Q (pad c))
@[local fun_prop] theorem pack_poly {α} [Enc α] {c : α → Ctx} {t u : α → ℕ} (hc : PolyT c) (ht : PolyT t) (hu : PolyT u) : PolyT (fun x => pack (c x) (t x) (u x)) := by unfold pack; fun_prop
attribute [local irreducible] pack

def forward1 (c : Ctx) (t b : ℕ) : Bool := allN (pad c) (L1 (dim c)) (fun i => decide (w2 c t b i = first c t i b % Q (pad c)))
@[local fun_prop] theorem forward1_poly {α} [Enc α] {c : α → Ctx} {t b : α → ℕ} (hc : PolyT c) (ht : PolyT t) (hb : PolyT b) : PolyT (fun x => forward1 (c x) (t x) (b x)) := by unfold forward1; fun_prop
attribute [local irreducible] forward1

def forward2 (c : Ctx) (t i : ℕ) : Bool := allN (pad c) (L2 (dim c)) (fun b => decide (w3 c t b i = second c t i b % Q (pad c)))
@[local fun_prop] theorem forward2_poly {α} [Enc α] {c : α → Ctx} {t i : α → ℕ} (hc : PolyT c) (ht : PolyT t) (hi : PolyT i) : PolyT (fun x => forward2 (c x) (t x) (i x)) := by unfold forward2; fun_prop
attribute [local irreducible] forward2

def pointwise (c : Ctx) (b i : ℕ) : Bool := decide (w4 c b i = (w3 c 0 b i * w3 c 1 b i) % Q (pad c))
@[local fun_prop] theorem pointwise_poly {α} [Enc α] {c : α → Ctx} {b i : α → ℕ} (hc : PolyT c) (hb : PolyT b) (hi : PolyT i) : PolyT (fun x => pointwise (c x) (b x) (i x)) := by unfold pointwise; fun_prop
attribute [local irreducible] pointwise

def inverse1 (c : Ctx) (i : ℕ) : Bool := allN (pad c) (L2 (dim c)) (fun b => decide (w5 c b i = third c i b % Q (pad c)))
@[local fun_prop] theorem inverse1_poly {α} [Enc α] {c : α → Ctx} {i : α → ℕ} (hc : PolyT c) (hi : PolyT i) : PolyT (fun x => inverse1 (c x) (i x)) := by unfold inverse1; fun_prop
attribute [local irreducible] inverse1

def inverse2 (c : Ctx) (b : ℕ) : Bool := allN (pad c) (2*n0 (dim c)) (fun u => if u % L2 (dim c) = b then decide (w6 c u = fourth c u % Q (pad c)) else true)
@[local fun_prop] theorem inverse2_poly {α} [Enc α] {c : α → Ctx} {b : α → ℕ} (hc : PolyT c) (hb : PolyT b) : PolyT (fun x => inverse2 (c x) (b x)) := by unfold inverse2; fun_prop
attribute [local irreducible] inverse2

def carry (c : Ctx) (u : ℕ) : Bool := decide (w6 c u + linkR c u = outDigit c u + pow2 (pad c) (k (dim c)) * linkL c (u+1))
@[local fun_prop] theorem carry_poly {α} [Enc α] {c : α → Ctx} {u : α → ℕ} (hc : PolyT c) (hu : PolyT u) : PolyT (fun x => carry (c x) (u x)) := by simp only [carry,k]; fun_prop
attribute [local irreducible] carry

def carrySpacer (c : Ctx) (i : ℕ) : Bool := decide (w7 c i = w8 c i)
@[local fun_prop] theorem carrySpacer_poly {α} [Enc α] {c : α → Ctx} {i : α → ℕ} (hc : PolyT c) (hi : PolyT i) : PolyT (fun x => carrySpacer (c x) (i x)) := by unfold carrySpacer; fun_prop
attribute [local irreducible] carrySpacer

end DetDLP.w4_M5GateNat


