-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_copyInput
-- name    : RandPurIso_Completion_Supplement_copyInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:53:30.133574+00:00
-- url     : https://prove2.me/theorems/6266bc38-265e-47a8-84cf-3a105c3c7ab0
-- title:
--   The input $|0^n\rangle\otimes\rho^{\otimes t}\otimes|0^a\rangle$ of a copy circuit and its output register
-- statement:
--   A density matrix $\rho$ on $\mathcal H([N])$ is written on $\lceil\log_2 N\rceil$ qubits, basis label $x$ in binary (zero on strings that encode no $x<N$), and $\rho^{\otimes t}$ on $t$ such blocks. A copy circuit $\mathcal B$ on $n+(t\lceil\log_2 N\rceil+a)$ qubits starts in
--
--   $$
--   |0^n\rangle\langle 0^n|\otimes\rho^{\otimes t}\otimes|0^a\rangle\langle 0^a| ,
--   $$
--
--   and its output $\mathcal B(\rho^{\otimes t})$ is the reduced state of its first $n$ qubits. This is the interface of the circuit $\mathcal B$ "taking exactly $t$ copies of $\rho$" in Theorem 6.9.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 6.9, p. 43

import Mathlib
import Definitions.Def_RandPurIso_Completion_QInstr
open Matrix

namespace RandPurIso.Completion.Supplement

open ShiShallow RandPurIso.Completion

/-- The first `n` bits of a string on `n + k` qubits. -/
def headBits {n k : ℕ} (z : Bits (n + k)) : Bits n := fun i => z (Fin.castAdd k i)

/-- The last `k` bits of a string on `n + k` qubits. -/
def tailBits {n k : ℕ} (z : Bits (n + k)) : Bits k := fun i => z (Fin.natAdd n i)

/-- Block `j` (`clog₂ N` qubits) of a string on `t · clog₂ N` qubits (`finProdFinEquiv`). -/
def copyBlock {t c : ℕ} (z : Bits (t * c)) (j : Fin t) : Bits c := fun i => z (finProdFinEquiv (j, i))

/-- A density matrix `ρ` on `H([N])` on `⌈log₂ N⌉` qubits, basis label `x` written as `finBin x` (zero
on strings that encode no `x < N`). -/
def encState {N : ℕ} (ρ : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Bits (Nat.clog 2 N)) (Bits (Nat.clog 2 N)) ℂ :=
  fun u v => ∑ x, ∑ y, if u = finBin x ∧ v = finBin y then ρ x y else 0

/-- `ρ^{⊗t}` on `t` blocks of `⌈log₂ N⌉` qubits. -/
def copiesState {N : ℕ} (ρ : Matrix (Fin N) (Fin N) ℂ) (t : ℕ) :
    Matrix (Bits (t * Nat.clog 2 N)) (Bits (t * Nat.clog 2 N)) ℂ :=
  fun z z' => ∏ j : Fin t, encState ρ (copyBlock z j) (copyBlock z' j)

/-- **The input of the copy circuit `B`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Theorem 6.9, p. 43: "taking exactly `t` copies of
`ρ`"): `|0^n⟩⟨0^n| ⊗ ρ^{⊗t} ⊗ |0^a⟩⟨0^a|` on `n + (t·⌈log₂ N⌉ + a)` qubits; the first `n` qubits are
`B`'s output register. -/
def copyInput {N : ℕ} (n a t : ℕ) (ρ : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Bits (n + (t * Nat.clog 2 N + a))) (Bits (n + (t * Nat.clog 2 N + a))) ℂ :=
  fun z z' =>
    if headBits z = zeroBits n ∧ headBits z' = zeroBits n ∧
        tailBits (tailBits z) = zeroBits a ∧ tailBits (tailBits z') = zeroBits a then
      copiesState ρ t (headBits (tailBits z)) (headBits (tailBits z'))
    else 0

/-- The reduced state of the first `n` qubits: trace out the last `k`. -/
def outputPart {n k : ℕ} (σ : Matrix (Bits (n + k)) (Bits (n + k)) ℂ) : Matrix (Bits n) (Bits n) ℂ :=
  fun u v => ∑ r : Bits k, σ (Fin.append u r) (Fin.append v r)

end RandPurIso.Completion.Supplement


