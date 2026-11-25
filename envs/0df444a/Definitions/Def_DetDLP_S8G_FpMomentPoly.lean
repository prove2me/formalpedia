-- Prove2me | Definitions.Def_DetDLP_S8G_FpMomentPoly
-- name    : DetDLP_S8G_FpMomentPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:35:15.474177+00:00
-- url     : https://prove2.me/theorems/a9148b0c-561a-4e23-b588-1e70ce0e8ec6
-- title:
--   Polynomial decoding of prime-field moment parameters and uniform packet encoding
-- statement:
--   The five-field query is decoded by framed list cursors. Counting the integers whose fourth power is below the ceiling binary logarithm computes the block count exactly. An address description with polynomial endpoint and tensor checks and unary enumeration bounds yields polynomial graph-building and port-evaluation functions with exact packet specifications.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Definitions.Def_DetDLP_S8G_FpMomentLayout
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_DetDLP_S8H_WirePacket
import Theorems.Thm_Groundwork_Unary_of_length

set_option autoImplicit false
namespace DetDLP.S8G.FpMoment.Code
open Groundwork DetDLP_W1_Queries M89S1
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  first_poly more_poly PolyT.length PolyT.mul P2M_Groundwork_PolyT_id__1c5d0f44cc8f

abbrev W := List Bool

def prime (w : W) := PolyT.bval (second w)
def idx (w : W) := PolyT.bval (third w)
def threshold (w : W) := PolyT.bval (third (more w))
def pfx (w : W) := third (more (more w))

@[simp] theorem fields (p : ℕ) (j : Fin 4) (T : ℕ) (η : W) :
    let w := word p j T η
    prime w = p ∧ idx w = j.val ∧ threshold w = T ∧ pfx w = η := by
  simp [prime,idx,threshold,pfx,word,queryWord,second,third]

@[local fun_prop] theorem prime_poly : PolyT prime := by unfold prime second; fun_prop
@[local fun_prop] theorem idx_poly : PolyT idx := by unfold idx third second; fun_prop
@[local fun_prop] theorem threshold_poly : PolyT threshold := by unfold threshold third second; fun_prop
@[local fun_prop] theorem prefix_poly : PolyT pfx := by unfold pfx third second; fun_prop

/-- Ceiling binary logarithm, including the inputs zero and one. -/
def width (x : ℕ) := (Nat.bits (x-1)).length

theorem width_eq (x : ℕ) : width x = bitLen x := by
  unfold width bitLen
  rw [Nat.size_eq_bits_len]
  apply le_antisymm
  · apply Nat.size_le.mpr
    rcases x with _|x
    · decide
    · simpa using (Nat.le_pow_clog (by decide : 1 < 2) (x+1))
  · apply Nat.clog_le_of_le_pow
    have h := Nat.lt_size_self (x-1)
    omega

@[local fun_prop] theorem width_poly {α : Type} [Enc α] {f : α → ℕ} (hf : PolyT f) :
    PolyT fun x => width (f x) := by unfold width; fun_prop

private theorem count_lt (k n : ℕ) : (List.range n).countP (fun a => decide (a < k)) = min n k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ,List.countP_append,ih]; by_cases h : n < k <;> simp [h] <;> omega

/-- Counts integers strictly smaller than the required fourth root, using only a unary range of logarithmic length. -/
def slots (b : ℕ) :=
  let c := width (b+2)
  max 2 ((List.range c).countP (fun k => decide (k*k*k*k < c)))

theorem slots_eq (b : ℕ) : slots b = blockCount b := by
  let c := Nat.clog 2 (b+2)
  let r := Nat.ceil ((c:ℝ)^((1:ℝ)/4))
  have iff' (k : ℕ) : r ≤ k ↔ c ≤ k*k*k*k := by
    change ⌈(c:ℝ)^((1:ℝ)/4)⌉₊ ≤ k ↔ _
    rw [Nat.ceil_le,one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by norm_num)]
    norm_cast
    ring_nf
  have hr : r ≤ c := (iff' c).mpr (by simpa [pow_succ] using Nat.le_self_pow (by decide : 4 ≠ 0) c)
  have eq : (fun k : ℕ => decide (k*k*k*k < c)) = fun k => decide (k < r) := by
    funext k; simp only [← not_le, ← iff']
  change max 2 ((List.range (width (b+2))).countP _) = max 2 r
  simp only [width_eq,bitLen]
  change max 2 ((List.range c).countP (fun k => decide (k*k*k*k < c))) = max 2 r
  rw [eq,count_lt,min_eq_right hr]

@[local fun_prop] theorem slots_poly {α : Type} [Enc α] {f : α → ℕ} (hf : PolyT f) :
    PolyT fun x => slots (f x) := by
  let g (x : α) := width (f x+2)
  have hg : PolyT g := by unfold g; fun_prop
  have u : Unary g := by unfold g width; apply Unary.of_length; fun_prop
  have hc := PolyT.countP (f := fun (x : α) k => decide (k*k*k*k < g x))
    (by have h := PolyT.comp hg (PolyT.fst (PolyT.id' (α := α × ℕ))); fun_prop) (PolyT.range u)
  change PolyT fun x => max 2 ((List.range (g x)).countP (fun k => decide (k*k*k*k < g x)))
  simp only [max_def]; apply PolyT.ite' <;> fun_prop (disch := assumption)

def sizeField (w : W) := scale (slots (width (prime w))) (width (prime w))

theorem sizeField_word (p : ℕ) (j : Fin 4) (T : ℕ) (η : W) :
    sizeField (word p j T η) = scale (blockCount (bitLen p)) (bitLen p) := by
  simp only [sizeField,(fields p j T η).1, width_eq,slots_eq]

theorem sizeField_poly : PolyT sizeField := by unfold sizeField scale; fun_prop

open S8C S8H w4_M5Network OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Numeric interface for a layout compiler, total even on malformed input packets. -/
structure Addresses where
  nv : W → ℕ
  ne : W → ℕ
  src : W → ℕ → ℕ
  dst : W → ℕ → ℕ
  check : W × ℕ × W → Bool

structure Addresses.Uniform (a : Addresses) : Prop where
  nv : PolyT a.nv
  ne : PolyT a.ne
  vert : Unary fun w => a.nv w + a.ne w
  edge : Unary fun w => a.ne w + a.ne w
  src : PolyT fun z : W × ℕ => a.src z.1 z.2
  dst : PolyT fun z : W × ℕ => a.dst z.1 z.2
  check : PolyT a.check

def make (a : Addresses) (w : W) := outerPacket w
  (WirePacket.packet (a.nv w) (a.ne w) (a.src w) (a.dst w)) (sizeField w)

def port (a : Addresses) := portPacket a.check

theorem make_poly (a : Addresses) (h : a.Uniform) : PolyT (make a) :=
  outerPacket_poly PolyT.id' (WirePacket.packet_poly h.nv h.ne h.vert h.edge h.src h.dst) sizeField_poly

theorem port_poly (a : Addresses) (h : a.Uniform) : PolyT (port a) := portPacket_poly h.check

theorem make_word (a : Addresses) (p : ℕ) (j : Fin 4) (T : ℕ) (η : W) (G : WireGraph)
    (hv : a.nv (word p j T η) = G.nV) (he : a.ne (word p j T η) = G.nE)
    (hs : ∀ i : Fin G.nE, a.src (word p j T η) i.val = (G.endpoints i).1.val)
    (hd : ∀ i : Fin G.nE, a.dst (word p j T η) i.val = (G.endpoints i).2.val) :
    let w := word p j T η; let s := scale (blockCount (bitLen p)) (bitLen p)
    make a w = encodeBTNInstance w G.subdivision s s 1 := by
  dsimp only
  rw [make,hv,he,WirePacket.packet_eq G _ _ hs hd,sizeField_word,outerPacket_eq]

theorem port_word (a : Addresses) (w : W) (v : ℕ) (xs : W) :
    port a (encodePortQuery w v xs) = encodeNatListBin [if a.check (w,v,xs) then 1 else 0] :=
  portPacket_eq ..

end DetDLP.S8G.FpMoment.Code


