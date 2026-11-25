-- Prove2me | Definitions.Def_DetDLP_D4BSliceArgs
-- name    : DetDLP_D4BSliceArgs
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:25:21.201414+00:00
-- url     : https://prove2.me/theorems/17f6946c-ba63-4cbb-a8a0-b799e0dd82e5
-- title:
--   Building the residual slice input from the port query and source reply
-- statement:
--   A polynomial-time adapter builds the six canonical input fields required by the residual digit slice postprocessor. Bounded unary fuel limits materialization of powers of two even on malformed inputs.

import Definitions.Def_DetDLP_D4BEntryCodec
import Theorems.Thm_Groundwork_PolyT_pow_unary
set_option autoImplicit false
namespace DetDLP.D4BEntry
open Groundwork Groundwork.PolyT D4Plan D4Slice AppendixD4 ResidualScalarOracle DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.map PolyT.flatMap PolyT.length PolyT.div PolyT.mod PolyT.mul PolyT.zip
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_ite__226169acf219
  D4Slice.field_poly w5_M6Sort.decode_poly w5_M6Sort.encode_poly listWord_poly
private theorem clog2_size (n : ℕ) : Nat.clog 2 n = Nat.size (n-1) := by
  apply le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide)).2; have := Nat.lt_size_self (n-1); omega
  · apply Nat.size_le.mpr
    have H := Nat.le_pow_clog (by decide : 1 < 2) n
    have h : 0 < 2 ^ Nat.clog 2 n := by positivity
    omega
@[local fun_prop] theorem clog2_poly {α : Type} [Enc α] {f : α → ℕ} (hf : PolyT f) : PolyT (fun a => Nat.clog 2 (f a)) := by simp only [clog2_size, ← Nat.size_eq_bits_len]; fun_prop

def clipped (n : ℕ) (fuel : W) : W := (fuel.take n).map fun _ => true
@[local fun_prop] theorem clipped_poly {α : Type} [Enc α] {n : α → ℕ} {fuel : α → W} (hn : PolyT n) (hw : PolyT fuel) : PolyT fun x => clipped (n x) (fuel x) := by unfold clipped; fun_prop
@[simp] theorem clipped_eq {n : ℕ} {w : W} (h : n ≤ w.length) : clipped n w = List.replicate n true := by simp [clipped,min_eq_left h]
def modBits (n : ℕ) (fuel : W) := (2 ^ (fuel.take n).length : ℕ).bits
@[local fun_prop] theorem modBits_poly {α : Type} [Enc α] {n : α → ℕ} {fuel : α → W} (hn : PolyT n) (hw : PolyT fuel) : PolyT fun x => modBits (n x) (fuel x) := by
  unfold modBits; apply bits; apply pow_unary (const 2)
  have h : PolyT fun a => ((fuel a).take (n a)).map (fun _ => ()) := by fun_prop
  exact h.congr (by simp)
@[simp] theorem modBits_eq {n : ℕ} {w : W} (h : n ≤ w.length) : modBits n w = (2^n : ℕ).bits := by simp [modBits,min_eq_left h]

def addresses (d K : ℕ) (src : W) := encodeNatListBin ((List.range (w5_M6Sort.decode src).length).map fun z => z % d + K * (z / d))
@[local fun_prop] theorem addresses_poly {α : Type} [Enc α] {d K : α → ℕ} {src : α → W} (hd : PolyT d) (hK : PolyT K) (hs : PolyT src) : PolyT fun a => addresses (d a) (K a) (src a) := by
  unfold addresses; apply w5_M6Sort.encode_poly; apply PolyT.map (f := fun a z => z % d a + K a * (z / d a)) (by fun_prop); apply PolyT.range
  have h : PolyT fun a => (w5_M6Sort.decode (src a)).map fun _ => () := by fun_prop
  exact h.congr (by simp)
private theorem addr_spec {l d K : ℕ} (f : Fin (l*d) → ℕ) : addresses d K (encodeNatListBin (List.ofFn f)) = encodeNatListBin (List.ofFn fun z : Fin (l*d) => (finProdFinEquiv (m:=l) (n:=d) |>.symm z).2.val + K * (finProdFinEquiv (m:=l) (n:=d) |>.symm z).1.val) := by
  unfold addresses; simp only [w5_M6Sort.decode_encode,List.length_ofFn]; congr 1; apply List.ext_getElem; simp; intro i hi hi'; simp [finProdFinEquiv,Fin.modNat,Fin.divNat]

def nval (n : ℕ) (w : W) := bval (field n w)
@[local fun_prop] theorem nval_poly {α : Type} [Enc α] (n : ℕ) {f : α → W} (hf : PolyT f) : PolyT fun x => nval n (f x) := by unfold nval; fun_prop

def sliceArgs (w src pad : W) :=
  let desc := field 0 w; let g := field 0 (field 2 desc)
  let d := (field 2 (field 1 desc)).length; let n := nval 0 g; let β := nval 1 g
  let l := nval 7 (field 0 desc); let K := n*(d-1)+1; let h := max 1 (β/(n+1))
  let av := (w5_M6Sort.decode (field 3 desc)).getD (nval 1 w) 0
  listWord [clipped (K*l) pad, addresses d K src, modBits (β+n*h+n*Nat.clog 2 (d*l)+2) pad, modBits (h*av) pad, modBits h pad, src]

@[local fun_prop] theorem sliceArgs_poly {α : Type} [Enc α] {w src pad : α → W} (hw : PolyT w) (hs : PolyT src) (hp : PolyT pad) : PolyT fun a => sliceArgs (w a) (src a) (pad a) := by
  unfold sliceArgs; fun_prop

theorem sliceArgs_spec {C c : ℕ} {x : Input C c} (P : Plan x) (u : Fin P.N)
    (a : Fin (P.R u).nV → Fin (J P u)) (v : Fin (P.R u).nV) (t : Fin ((P.R u).deg v) → Bool) (pad : W)
    (hl : spacing P.f (P.R u)*x.l ≤ pad.length)
    (hp : precision P.f x.l (P.R u) (h P u) (4*x.m*x.k) ≤ pad.length)
    (ha : h P u * (a v).val ≤ pad.length) (hh : h P u ≤ pad.length) :
    let d := P.f.natDegree; let K := spacing P.f (P.R u); let coord := (finProdFinEquiv (m:=x.l) (n:=d)).symm
    let src := residue P.f x.l (P.guard+x.p) P.hf (P.V u v t)
    sliceArgs (encodePortQuery (digitDesc P u a) v.val (List.ofFn t)) src pad =
      Encoding.encodeList id [List.replicate (K*x.l) true,
        encodeNatListBin (List.ofFn fun z => (coord z).2.val+K*(coord z).1.val),
        (2^(precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) : ℕ).bits,(2^(h P u*(a v).val) : ℕ).bits,(2^(h P u) : ℕ).bits,src] := by
  dsimp only
  simp [sliceArgs,nval,encodePortQuery,digitDesc,input,encodeTerminalBTNInstance,header,branch,BipartiteMultigraph.encode,polynomialBits,P.edges,List.getD_eq_getElem?_getD,v.isLt]
  change Encoding.encodeList id [clipped _ pad, addresses _ _ _, modBits _ pad,modBits _ pad, modBits _ pad,_] = _
  unfold spacing at hl ⊢; unfold precision h digitWidth at hp; unfold h digitWidth at hh ha
  rw [clipped_eq hl, modBits_eq hp, modBits_eq ha, modBits_eq hh]
  unfold residue; rw [addr_spec]; rfl
end DetDLP.D4BEntry


