-- Prove2me | Definitions.Def_RuntimeTransferFourier
-- name    : RuntimeTransferFourier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:13:29.056114+00:00
-- url     : https://prove2.me/theorems/e2f4b46c-5b4b-47d9-bf14-5f96738ec2bc
-- title:
--   Chirp queries and the middle-product interface
-- statement:
--   For natural $n$, queries consist of complex arrays of lengths $n$ and $2n+1$. The answer array has entries $\sum_j a_j b_{k+n-j}$. Defines the transform $\sum_j x_j(\rho^2)^{jk}$, chirp arrays $a_j=x_j\rho^{j^2}$ and $b_t=\rho^{-(t-n)^2}$, output scaling by $\rho^{k^2}$, and a one-query program with explicitly supplied preparation and decoding charges $E,D$. Definitions allow zero length and any complex $\rho$; the subsequent identity requires $\rho\ne0$. No root-of-unity or machine-cost fact is included in these definitions.
-- source:
--   General runtime transfer and its Fourier/packing applications, companion proof note for this mission, 24 October 2026. Original cost-semantics formulation of standard substitution principles; not a claimed new complexity bound.

import Definitions.Def_RuntimeTransfer
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RuntimeTransfer

def middleIndex {n : ℕ} (k j : Fin n) : Fin (2 * n + 1) :=
  ⟨k.val + n - j.val, by have := k.isLt; have := j.isLt; omega⟩

abbrev FourierQuery (n : ℕ) := (Fin n → ℂ) × (Fin (2 * n + 1) → ℂ)

/-- Coefficients n through 2n-1 of the ordinary product of the input arrays. -/
def middleProduct {n : ℕ} (q : FourierQuery n) : Fin n → ℂ :=
  fun k => ∑ j : Fin n, q.1 j * q.2 (middleIndex k j)

def fourierValue {n : ℕ} (ρ : ℂ) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun k => ∑ j : Fin n, x j * (ρ ^ 2) ^ (j.val * k.val)

def chirpQuery {n : ℕ} (ρ : ℂ) (x : Fin n → ℂ) : FourierQuery n :=
  (fun j => x j * ρ ^ ((j.val : ℤ) ^ 2),
   fun t => ρ ^ (-((t.val : ℤ) - (n : ℤ)) ^ 2))

def chirpDecode {n : ℕ} (ρ : ℂ) (y : Fin n → ℂ) : Fin n → ℂ :=
  fun k => ρ ^ ((k.val : ℤ) ^ 2) * y k

/-- E and D are explicit preparation/output charges supplied by the caller.
Their realization in a machine model is a separate obligation. -/
def fourierProgram {n : ℕ} (ρ : ℂ) (x : Fin n → ℂ) (E D : ℕ) :
    Program (FourierQuery n) (Fin n → ℂ) (Fin n → ℂ) :=
  .work E (.query (chirpQuery ρ x) (fun y => .work D (.done (chirpDecode ρ y))))

end RuntimeTransfer


