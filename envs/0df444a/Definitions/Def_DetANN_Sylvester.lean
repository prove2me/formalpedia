-- Prove2me | Definitions.Def_DetANN_Sylvester
-- name    : DetANN_Sylvester
-- status  : Definition
-- author  : @milia
-- created : 2026-11-15T17:39:22.711166+00:00
-- url     : https://prove2.me/theorems/7bb392bc-2390-41e1-b7cf-fec2ff697329
-- title:
--   The Sylvester–Hadamard matrix (§6.1)
-- statement:
--   For $j,r\in\{0,\dots,2^k-1\}$, let $\langle j,r\rangle$ be the number of bit positions $b<k$ at which both $j$ and $r$ have a $1$. The **Sylvester–Hadamard matrix** on $\mathrm{Fin}(2^k)$ is
--
--   $$(H_k)_{jr}=(-1)^{\langle j,r\rangle}.$$
--
--   Index $i\in\mathrm{Fin}(2^k)$ of the lower half of $\mathrm{Fin}(2^{k+1})$ is $i$, and of the upper half is $2^k+i$.
--
--   This is the unnormalized Walsh–Hadamard matrix used to build the signed blocks of §6.1, in the dimension $d=2^k$.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §6.1, p.14

import Mathlib

namespace DetANN

/-!
# The Sylvester–Hadamard matrix (§6.1)

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §6.1, p.14: the (unnormalized) Walsh–Hadamard matrix on
`d = 2^k` coordinates, used to build the signed blocks.
-/

/-- The bitwise inner product `⟨j, r⟩ = #{b < k : bit b of j and bit b of r are both 1}`. -/
def bitDot (k j r : ℕ) : ℕ := ((Finset.range k).filter fun b => j.testBit b && r.testBit b).card

/-- The Sylvester–Hadamard matrix on `Fin (2^k)`: `(H_k)_{jr} = (−1)^{⟨j, r⟩}`. -/
def sylvester (k : ℕ) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ := fun j r => (-1) ^ bitDot k j r

/-- Index `i` of the lower half of `Fin (2^(k+1))`. -/
def loIdx (k : ℕ) (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) := ⟨i, by rw [pow_succ]; omega⟩

/-- Index `2^k + i` of the upper half of `Fin (2^(k+1))`. -/
def hiIdx (k : ℕ) (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) := ⟨2 ^ k + i, by rw [pow_succ]; omega⟩

end DetANN


