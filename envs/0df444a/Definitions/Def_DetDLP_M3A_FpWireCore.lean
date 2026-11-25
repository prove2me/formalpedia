-- Prove2me | Definitions.Def_DetDLP_M3A_FpWireCore
-- name    : DetDLP_M3A_FpWireCore
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T21:08:11.599527+00:00
-- url     : https://prove2.me/theorems/5dd34857-ddbb-4364-9751-e8c1c98773de
-- title:
--   Concrete native finite-field wire-core specification
-- statement:
--   Specifies the actual incidence graph, lookup set, size budget, descriptor and local tensor of the native finite-field core with absolute constant one million.
-- source:
--   DetDLP Stage II, native Fp wire core and lookup separation, Section 4.

import Definitions.Def_DetDLP_M3A_FpChainBijection

set_option autoImplicit false
namespace DetDLP.M3A.FpWireCore
open S8J S8L.FpPair.Stage FpArithNet FpChainBijection
open M3B.ECLayout (vertex port read_accepted gateSlots)
attribute [-simp] Fin.natAdd_eq_addNat
set_option backward.isDefEq.respectTransparency false

variable {p m d k T : ℕ} [Fact p.Prime]

def numbering (m : ℕ) : Fin (4*m) ≃ Fin m × Fin 2 × Bool where
  toFun s := (blockIndex s,coord s,whichSide s)
  invFun t := row t.2.2 t.1 t.2.1
  left_inv s := by obtain ⟨b,i,j,rfl⟩ := row_surj s; simp
  right_inv := by rintro ⟨i,j,b⟩; simp

/-- Non-lookup vertices return zero. On lookup vertices, reconstruct the word in bit
    significance order, not in the enumeration order of incident edges. -/
noncomputable def address (A : w3_FactorLayout) {n k : ℕ} (f : Fin n → Fin k → Fin A.nb)
    (v : Fin (w3_factorGraph (M3B.ECLayout.layout A f)).nV) (x : Fin ((w3_factorGraph _).deg v) → Bool) :=
  if h : ∃ i, v=vertex A f i then bitsToNat (fun j => x (h.choose_spec.symm ▸ port A f h.choose j)) else 0

def budget (m d k prec : ℕ) := 2*(70000*m*(d+3)+16*m*k+1)+prec
variable (F : Fin m → List (ZMod p)ˣ) (seed : FpSeed p m) (P : (ZMod p)ˣ) (pre : List Bool)
noncomputable def native {M : ℕ} (nz : NeZero M) (y : w3_Label M (w3_fpFB F).totalCoords) (input : List Bool) (d k : ℕ) : w3_Query :=
  { V := Additive (ZMod p)ˣ, M := M, nz := nz, b := d, m := m, k := k, FB := w3_fpFB F, P := Additive.ofMul P, y := y,
    code := fun x y => word (d:=d) F (x,y), pre := pre, input := input, addr := fun i j => w3_fpHashWord seed i (w3_fpResidue (((w3_fpFB F).blocks i).get j).toMul).val }
variable {M : ℕ} (nz : NeZero M) (y : w3_Label M (w3_fpFB F).totalCoords) (input : List Bool)
local notation "Q" => native F seed P pre nz y input d k
variable (hd : 1 ≤ d) (hp : 2 ≤ p) (hf : p < 2^d) (ht : T ≤ 2^k) (hm : 1 ≤ m)
variable (hF : ∀ i, (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) (mul : w3_modMulInterface)
local notation "A" => arith hd m k pre
local notation "f" => bus (m:=m) (k:=k) hd pre
local notation "G" => w3_factorGraph (layout hd m k pre)
local notation "sl" => gateSlots (q:=Q) A f (numbering m)

abbrev Shape (q : w3_Query) (C S : ℕ) := 2 ≤ q.b ∧ 1 ≤ q.m ∧ 1 ≤ q.k ∧ blockCount q.b ≤ C*q.m ∧ q.m ≤ C*blockCount q.b ∧
    S ≤ C*q.m*q.b ∧ 4*q.m*q.k ≤ C*q.b ∧ q.b ≤ C*(4*q.m*q.k) ∧ 1 ≤ w3_precision q ∧ w3_precision q ≤ S ∧ 1 ≤ w3_len q ∧ w3_len q ≤ C*q.m

/-- The concrete graph, tensor, lookup set and packet budget, independently of the proof of parsimony. -/
def NativeCore (W : w3_WireCore Q 1000000) :=
  W.desc = (Q).input ∧ W.S = budget m d k (w3_precision Q) ∧ W.G = G ∧
  HEq W.L (w3_incLookups (layout hd m k pre) sl) ∧
  HEq W.T (w3_gateWeight (w3_incSlot (layout hd m k pre) sl) (address A f)
    (w3_factorChecks _ (test hd p T (P : ZMod p).val seed pre)))

/-- Existence specialized to the transported query plus the concrete fields required by the evaluators. -/
def CoreFamily : Prop :=
  (∀ (q : w3_Query), w3_fpQueries q → w3_modMulInterface → Nonempty {W : w3_WireCore q 1000000 // W.desc=q.input}) ∧
  ∀ {p m d k T M : ℕ} [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ) (seed : FpSeed p m) (P : (ZMod p)ˣ) (pre : List Bool)
    (nz : NeZero M) (y : w3_Label M (w3_fpFB F).totalCoords) (input : List Bool) (hd : 1 ≤ d),
    2 ≤ d → m = blockCount d → 2 ≤ p → p < 2^d → T ≤ 2^k → 1 ≤ m →
    (∀ i, (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) → w3_modMulInterface →
    w3_fpQueries (native F seed P pre nz y input d k) → ∃ W, NativeCore (T:=T) (k:=k) F seed P pre nz y input hd W

attribute [simp] Fin.natAdd_eq_addNat
end DetDLP.M3A.FpWireCore
abbrev DetDLP_M3A_FpWireCore := DetDLP.M3A.FpWireCore.CoreFamily


