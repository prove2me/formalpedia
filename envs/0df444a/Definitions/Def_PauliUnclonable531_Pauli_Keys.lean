-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Keys
-- name    : PauliUnclonable531_Pauli_Keys
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:08.504585+00:00
-- url     : https://prove2.me/theorems/7fd12eb9-6eb9-4211-929c-6fba8bf3f168
-- title:
--   Pauli labels, supported keys, and exact uniform law
-- statement:
--   For n qubits let a bit string be an element of {0,1}ⁿ, and let a label k=(x,z) be a pair of bit strings. Translate each local pair as 00→I, 10→X, 11→Y, 01→Z, then use the published unrestricted tensor Pauli string. The supported keys exclude only the whole zero label:
--
--   $$K_n=(\{0,1\}^n\times\{0,1\}^n)\setminus\{(0^n,0^n)\},\qquad \Pr[k]=|K_n|^{-1}.$$
--
--   A key is encoded by concatenating x and z in 2n bit positions. The active mask marks nonidentity factors. The functions γ(n)=2ⁿ/(4ⁿ−1) and securityBound(n)=1/2+√γ(n)/2 abbreviate the exact source constants. The construction uses n≥1; the Pauli label layer also permits n=0. Individual identity factors remain allowed.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), §2.1, p.11; §3, p.15; Definition 4.2, p.19

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Operators
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

abbrev Bits (n : ℕ) := Fin n → Fin 2
abbrev Label (n : ℕ) := Bits n × Bits n
/-- Only the whole identity string is excluded (§3, p.15). -/
abbrev Key (n : ℕ) := {k : Label n // k ≠ (0, 0)}

def localLabel (x z : Fin 2) : Fin 4 :=
  if x = 0 then (if z = 0 then 0 else 3) else (if z = 0 then 1 else 2)

def pauli {n : ℕ} (k : Label n) : Op (Bits n) :=
  QMaxCutSDP.Rounding.pauliString (fun j => localLabel (k.1 j) (k.2 j))

def keyEncode {n : ℕ} (k : Key n) : Fin (n + n) → Fin 2 :=
  Fin.append k.val.1 k.val.2

def active {n : ℕ} (k : Label n) (j : Fin n) : Bool :=
  decide (k.1 j ≠ 0 ∨ k.2 j ≠ 0)

noncomputable def keyMass (n : ℕ) (_ : Key n) : ℝ := (Fintype.card (Key n) : ℝ)⁻¹

def sign (b : Fin 2) : ℂ := (-1 : ℂ) ^ b.val

noncomputable def gamma (n : ℕ) : ℝ := (2 : ℝ)^n / ((4 : ℝ)^n - 1)
noncomputable def securityBound (n : ℕ) : ℝ := 1/2 + (1/2) * Real.sqrt (gamma n)

end PauliUnclonable531.Pauli


