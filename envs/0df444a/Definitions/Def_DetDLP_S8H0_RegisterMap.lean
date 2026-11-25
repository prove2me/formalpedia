-- Prove2me | Definitions.Def_DetDLP_S8H0_RegisterMap
-- name    : DetDLP_S8H0_RegisterMap
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:03:39.930921+00:00
-- url     : https://prove2.me/theorems/71289ed5-8703-4e6d-bdf9-776fd724d06a
-- title:
--   Flat addresses and a linear budget for the point-check registers
-- statement:
--   Flatten words, products and fixed-length vectors into one Boolean register file. Typed addresses retrieve exactly the corresponding flattened bit. The Tag 0 bank has 118d + 14m + 45 bits for word width d and multiplier wire count m, giving a linear bound and a polynomial-time size computation.
-- source:
--   Companion to DetDLP.s8h_ec_order_query, f0e81f0e-6143-4672-a126-0c2b5aa2d552.

import Definitions.Def_DetDLP_S8H0_SignalBank
import Definitions.Def_DetDLP_S8H_PointAddresses

set_option autoImplicit false
namespace DetDLP.S8H0.RegisterMap
open S8H.PointAddresses S8H.ECPointArithmetic SignalBank ResidueWires
open Groundwork (PolyT Enc)

inductive Shape where
  | bit
  | word (n : ℕ)
  | pair (u v : Shape)
  | vec (n : ℕ) (s : Shape)

def Shape.size : Shape → ℕ
  | .bit => 1
  | .word n => n
  | .pair u v => u.size+v.size
  | .vec n s => n*s.size

def Shape.Data : Shape → Type
  | .bit => Bool
  | .word n => Bits n
  | .pair u v => u.Data × v.Data
  | .vec n s => Fin n → s.Data

def Shape.decode : (s : Shape) → Bits s.size ≃ s.Data
  | .bit => ⟨(· (0 : Fin 1)),fun b _ => b,fun f => funext fun i => congrArg f (Fin.eq_zero i).symm,fun _ => rfl⟩
  | .word _ => Equiv.refl _
  | .pair u v => Equiv.trans
      ⟨fun f => (f ∘ Fin.castAdd v.size,f ∘ Fin.natAdd u.size),fun f => Fin.append f.1 f.2,
        fun f => funext fun i => Fin.addCases (fun j => Fin.append_left _ _ j) (fun j => Fin.append_right _ _ j) i,
        fun f => Prod.ext (funext fun i => Fin.append_left _ _ i) (funext fun i => Fin.append_right _ _ i)⟩
      (u.decode.prodCongr v.decode)
  | .vec n s => Equiv.trans
      ⟨fun f i j => f (finProdFinEquiv (i,j)),fun f t => f (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2,
        fun f => funext fun i => congrArg f (finProdFinEquiv.apply_symm_apply i),
        fun f => funext fun i => funext fun j => by simp⟩
      (Equiv.piCongrRight (fun _ : Fin n => s.decode))

inductive Addr : Shape → Type where
  | bit : Addr .bit
  | word {n : ℕ} (j : Fin n) : Addr (.word n)
  | fst {u v} (a : Addr u) : Addr (.pair u v)
  | snd {u v} (a : Addr v) : Addr (.pair u v)
  | vec {n s} (i : Fin n) (a : Addr s) : Addr (.vec n s)

def Addr.index {s} : Addr s → Fin s.size
  | .bit => (0 : Fin 1)
  | .word j => j
  | .fst a => Fin.castAdd _ a.index
  | .snd a => Fin.natAdd _ a.index
  | .vec i a => finProdFinEquiv (i,a.index)

def Addr.get {s} : Addr s → s.Data → Bool
  | .bit,v => v
  | .word j,v => v j
  | .fst a,v => a.get v.1
  | .snd a,v => a.get v.2
  | .vec i a,v => a.get (v i)

theorem Addr.correct {s} (a : Addr s) (xs : Bits s.size) : a.get (s.decode xs) = xs a.index := by
  induction a with
  | bit => rfl
  | word => rfl
  | fst a ih => exact ih _
  | snd a ih => exact ih _
  | vec i a ih => exact ih _

open Shape in
def triple (d : ℕ) := pair (word d) (pair (word d) (word (d+1)))

open Shape in
def mul (d e : ℕ) := pair (word (2*d)) (word e)

open Shape in
def run (d e : ℕ) := pair (triple d) (pair (pair (triple d) (pair (word d) (pair (mul d e) (mul d e)))) bit)

open Shape in
def bank (d e : ℕ) := pair (pair bit (pair (triple d) (triple d)))
  (pair (vec 7 (run d e)) (vec 7 (pair (word (2*d)) (pair (word (d+1)) (pair (word (d+1)) (word (d+1)))))))

def regs (d : ℕ) := (bank d (wires d)).size

theorem regs_eq (d : ℕ) : regs d = 118*d + 14*wires d + 45 := by
  simp only [regs,bank,run,mul,triple,Shape.size]; omega

theorem regs_linear {d : ℕ} (hd : 1 ≤ d) : regs d < 16000*(d+2) := by
  have h := w3_fpMulIncidenceBounds hd
  have he : (w3_fpMulLayout d hd).ne = wires d + wires d := by rw [wires_eq hd]; rfl
  rw [regs_eq]; omega

theorem regs_poly {α : Type} [Enc α] {d : α → ℕ} (hd : PolyT d) : PolyT fun x => regs (d x) := by
  have h : PolyT fun x => wires (d x) := mul_poly.nb hd
  simp only [regs_eq]; apply PolyT.add _ (PolyT.const _)
  exact PolyT.add (PolyT.mul (PolyT.const _) hd) (PolyT.mul (PolyT.const _) h)

def flat {d : ℕ} (hd : 1 ≤ d) : Bits (regs d) ≃ Bank d hd := by
  unfold regs; rw [wires_eq hd]; exact (bank d (w4_M5GraphBounds.graph d hd).nE).decode

end DetDLP.S8H0.RegisterMap


