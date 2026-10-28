-- Prove2me | Definitions.Def_RuntimeTransferArithmetic
-- name    : RuntimeTransferArithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:14:00.963245+00:00
-- url     : https://prove2.me/theorems/243f953b-0cea-4177-ae81-46045987990f
-- title:
--   Explicit complex arithmetic and full-product programs
-- statement:
--   Defines the full polynomial product and middle-coefficient selection, an instruction interpreter charging one for each explicit complex multiplication or inversion and the oracle charge for a full-product call, chirp generation, pointwise multiplication, structural chirp reflection, and a concrete Fourier program. Structural array and control operations are uncharged. The instruction type permits arbitrary mathematical continuations and returned values; it is not a compiler guaranteeing costs for arbitrary functions. In the concrete Fourier program, scalar preparation and decoding operations are explicit instructions. Parameters and roots are supplied as inputs.
-- source:
--   Strengthened transfer results, companion note to this mission, 24 October 2026. Concrete instruction-count and bit-length formulation of classical Bluestein and Kronecker reductions; not a claim of a new complexity exponent.

import Definitions.Def_RuntimeTransferFourier
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RuntimeTransfer

/-- All coefficients of the ordinary product, with one harmless trailing zero. -/
def fullProduct {n : ℕ} (q : FourierQuery n) : Fin (3 * n + 1) → ℂ :=
  fun k => ∑ j : Fin n,
    if h : j.val ≤ k.val ∧ k.val - j.val < 2 * n + 1 then
      q.1 j * q.2 ⟨k.val - j.val, h.2⟩ else 0

def productMiddle {n : ℕ} (y : Fin (3 * n + 1) → ℂ) : Fin n → ℂ :=
  fun k => y ⟨k.val + n, by have := k.isLt; omega⟩

/-- Straight-line complex arithmetic with typed multiplication, inversion and
full polynomial-product calls. Structural array operations are free in this
arithmetic-operation model; no bit or RAM runtime is asserted. -/
inductive Arithmetic (n : ℕ) (R : Type) where
  | done : R → Arithmetic n R
  | mul : ℂ → ℂ → (ℂ → Arithmetic n R) → Arithmetic n R
  | inv : ℂ → (ℂ → Arithmetic n R) → Arithmetic n R
  | product : FourierQuery n → ((Fin (3 * n + 1) → ℂ) → Arithmetic n R) → Arithmetic n R

def Arithmetic.run {n : ℕ} {R : Type}
    (oracle : FourierQuery n → (Fin (3 * n + 1) → ℂ) × ℕ) : Arithmetic n R → R × ℕ
  | .done r => (r, 0)
  | .mul a b next => let z := (next (a * b)).run oracle; (z.1, 1 + z.2)
  | .inv a next => let z := (next a⁻¹).run oracle; (z.1, 1 + z.2)
  | .product q next => let ans := oracle q; let z := (next ans.1).run oracle;
      (z.1, ans.2 + z.2)

def Arithmetic.bind {n : ℕ} {R S : Type} (p : Arithmetic n R)
    (f : R → Arithmetic n S) : Arithmetic n S :=
  match p with
  | .done r => f r
  | .mul a b next => .mul a b (fun z => (next z).bind f)
  | .inv a next => .inv a (fun z => (next z).bind f)
  | .product q next => .product q (fun z => (next z).bind f)

/-- Two multiplication instructions per generated entry, including the last. -/
def chirpLoop {n : ℕ} (stride c d : ℂ) : (m : ℕ) → Arithmetic n (Fin m → ℂ)
  | 0 => .done Fin.elim0
  | m + 1 => .mul c d (fun c' => .mul d stride (fun d' =>
      (chirpLoop stride c' d' m).bind (fun tail => .done (Fin.cons c tail))))

/-- One multiplication instruction per coordinate. -/
def multiplyVector {n : ℕ} : (m : ℕ) → (Fin m → ℂ) → (Fin m → ℂ) →
    Arithmetic n (Fin m → ℂ)
  | 0, _, _ => .done Fin.elim0
  | m + 1, a, b => .mul (a 0) (b 0) (fun z =>
      (multiplyVector m (fun i => a i.succ) (fun i => b i.succ)).bind
        (fun tail => .done (Fin.cons z tail)))

def restrictChirp {n : ℕ} (a : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun j => a ⟨j.val, Nat.lt.step j.isLt⟩

def reflectedIndex {n : ℕ} (t : Fin (2 * n + 1)) : Fin (n + 1) :=
  if h : t.val ≤ n then ⟨n - t.val, by omega⟩
  else ⟨t.val - n, by have := t.isLt; omega⟩

def reflectChirp {n : ℕ} (a : Fin (n + 1) → ℂ) : Fin (2 * n + 1) → ℂ :=
  fun t => a (reflectedIndex t)

/-- Root supplied as input. Every complex multiplication and inversion used
for preparation and decoding is an explicit instruction. -/
def fourierArithmetic {n : ℕ} (ρ : ℂ) (x : Fin n → ℂ) : Arithmetic n (Fin n → ℂ) :=
  .mul ρ ρ (fun step => .inv ρ (fun r => .mul r r (fun invStep =>
    (chirpLoop step 1 ρ (n + 1)).bind (fun pos =>
    (chirpLoop invStep 1 r (n + 1)).bind (fun neg =>
    (multiplyVector n x (restrictChirp pos)).bind (fun a =>
    .product (a, reflectChirp neg) (fun y =>
      multiplyVector n (restrictChirp pos) (productMiddle y))))))))

end RuntimeTransfer


