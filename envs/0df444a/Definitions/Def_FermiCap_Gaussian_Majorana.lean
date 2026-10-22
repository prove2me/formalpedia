-- Prove2me | Definitions.Def_FermiCap_Gaussian_Majorana
-- name    : FermiCap_Gaussian_Majorana
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:36.632109+00:00
-- url     : https://prove2.me/theorems/389c29c5-e715-489b-adc5-c63af9c186dd
-- title:
--   Jordan–Wigner Majorana operators and the fermionic product channel
-- statement:
--   On $n$ qubits, the ordered computational basis is indexed by bit strings. The Pauli matrices $X,Y,Z$ give Jordan–Wigner operators $c_{2j-1}=Z_1\otimes\cdots\otimes Z_{j-1}\otimes X_j\otimes I\cdots I$ and $c_{2j}$ with $Y_j$ in place of $X_j$. For each binary string $x$ of length $2n$, $c(x)$ is the product of the selected Majorana operators in increasing index order.
--
--   For real attenuation coefficients $b_p$, the channel is the linear map on all matrices characterized by
--   $$\Phi_b(c(x))=\left(\prod_{p:x_p=1}b_p\right)c(x).$$
--   Its Lean definition uses the trace-orthogonal expansion in these monomials. The parity operator is $Z^{\otimes n}$. This model is the shared basis for every capacity and Gaussian-state statement in the mission.
--
--   **Formalization Note** Coordinates of `Fin n → Fin 2` are tensor factors, and Lean's Majorana indices run from zero to $2n-1$.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 1, eqs. (3)–(4); p. 3, eq. (9)

import Mathlib

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace FermiCap.Gaussian

/-- The computational basis of n ordered qubits. -/
abbrev Qubits (n : ℕ) := Fin n → Fin 2

/-- Operators on the n-qubit Hilbert space. -/
abbrev Op (n : ℕ) := Matrix (Qubits n) (Qubits n) ℂ

def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => if a = b then 0 else 1

def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => if a = b then 0 else if a = 0 then -Complex.I else Complex.I

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => if a ≠ b then 0 else if a = 0 then 1 else -1

/-- Entrywise Kronecker product, with tensor factor k at coordinate k. -/
def pauliString {n : ℕ} (σ : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Op n :=
  fun x y => ∏ k, σ k (x k) (y k)

/-- Jordan-Wigner generator c_p, p=0,...,2n-1. -/
def majorana (n : ℕ) (p : Fin (2 * n)) : Op n :=
  pauliString (fun k =>
    if k.val < p.val / 2 then pauliZ
    else if k.val = p.val / 2 then (if p.val % 2 = 0 then pauliX else pauliY)
    else 1)

/-- Ordered Clifford monomial c_0^x_0 ... c_(2n-1)^x_(2n-1). -/
def monomial (n : ℕ) (x : Fin (2 * n) → Bool) : Op n :=
  ((List.finRange (2 * n)).map (fun p => if x p then majorana n p else 1)).prod

/-- The map specified on every Clifford monomial by Eq. (4), extended to all operators
using the trace-orthogonal monomial expansion. -/
def channel (n : ℕ) (b : Fin (2 * n) → ℝ) (A : Op n) : Op n :=
  ∑ x : Fin (2 * n) → Bool,
    (((2 : ℂ) ^ n)⁻¹ * ((monomial n x)ᴴ * A).trace) •
      ((∏ p : Fin (2 * n), if x p then (b p : ℂ) else 1) • monomial n x)

/-- The parity operator is the tensor product of Pauli Z matrices, Eq. (9). -/
def parity (n : ℕ) : Op n := pauliString (fun _ => pauliZ)

end FermiCap.Gaussian


