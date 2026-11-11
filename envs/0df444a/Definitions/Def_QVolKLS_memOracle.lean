-- Prove2me | Definitions.Def_QVolKLS_memOracle
-- name    : QVolKLS_memOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:36.402419+00:00
-- url     : https://prove2.me/theorems/627869d0-4964-461e-b894-01bd8349c4bd
-- title:
--   Strong coherent membership oracle $O_K:|x\rangle|b\rangle\mapsto|x\rangle|b\oplus 1_K(x)\rangle$ on dyadic points
-- statement:
--   Let $K\subseteq\mathbb R^d$. The **strong coherent membership oracle** of $K$ acts on a point register and one answer qubit as
--   $$
--   O_K:\ |x\rangle_S|b\rangle_Q\ \longmapsto\ |x\rangle_S|b\oplus 1_K(x)\rangle_Q
--   $$
--   for exactly represented dyadic points $x$. Membership is answered exactly, boundary points included, at any finite precision chosen by the algorithm.
--
--   A precision is a **coordinate format** $(b,p)$: the point register consists of $d$ blocks of $b$ qubits; block $j$ holds a $b$-bit two's-complement integer $z_j$ (most significant bit first), and the register state $|z\rangle$ stands for the dyadic point $x=(z_1 2^{-p},\dots,z_d 2^{-p})$. The oracle for format $(b,p)$ acts on $db+1$ qubits (the answer qubit last) as the permutation matrix of $|z,c\rangle\mapsto|z,c\oplus 1_K(x)\rangle$.
--
--   A format $(b,p)$ **covers** a set $S$ when every point of the lattice $2^{-p}\mathbb Z^d$ lying in $S$ has its integer coordinates in the two's-complement range $[-2^{b-1},2^{b-1})$, so that it is written by exactly one register string.
--
--   This is the only access to $K$ that the mission's algorithms have.
--
--   **Formalization Note** `twosComp`, `decodePoint`, `memBit`, `memFlip`, `memOracle`, `RegCovers`. Membership is decided classically (`Classical.dec`), which models exact answers on the boundary. Block $j$ of the register is the wires $jb,\dots,jb+b-1$.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §2.4, p.23 (strong coherent membership)

import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QVolKLS_IsConvexBody

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms

/-!
# The strong coherent membership oracle

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §2.4, p.23: "For exactly represented dyadic
coordinates x, the oracle acts as `O_K : |x⟩_S|b⟩_Q ↦ |x⟩_S|b ⊕ 1_K(x)⟩_Q`. Membership is answered
exactly, including on the boundary, at any finite coordinate precision chosen by the algorithm.
Each call counts as one query, independently of precision."

**Formalization Note.**
* A coordinate format is a pair `(b, p)`: each of the `d` coordinates is a `b`-bit two's-complement
  integer `z` (most significant bit first; the published `bitsToNat` convention), and stands for the
  dyadic number `z · 2^{-p}`. The point register holds `d` consecutive blocks of `b` qubits, block
  `j` being coordinate `j` (`finProdFinEquiv`). The precision `(b, p)` is "chosen by the algorithm":
  an algorithm may use several formats, one oracle per format.
* `memOracle K b p` acts on `d·b + 1` qubits, the point register followed by the answer qubit
  (the last wire), as the permutation `|z, c⟩ ↦ |z, c ⊕ 1_K(z · 2^{-p})⟩`. Membership is decided
  classically (`Classical.dec`), so it is exact, boundary points included.
-/

/-- The integer written by a `b`-bit string in two's complement, most significant bit first:
`bitsToNat z − 2^b` if the leading bit is `1`, and `bitsToNat z` otherwise (`0` for `b = 0`). -/
def twosComp {b : ℕ} (z : Qubits b) : ℤ :=
  (bitsToNat z : ℤ) - (if h : 0 < b then (if z ⟨0, h⟩ then (2 : ℤ) ^ b else 0) else 0)

/-- The dyadic point of `ℝ^d` written in the point register of format `(b, p)`: coordinate `j` is
`twosComp(block j) · 2^{-p}`, block `j` being the wires `j·b, …, j·b + b − 1`. -/
noncomputable def decodePoint (d b p : ℕ) (z : Qubits (d * b)) : Euc d :=
  WithLp.toLp 2 (fun j : Fin d =>
    (twosComp (fun i : Fin b => z (finProdFinEquiv (j, i))) : ℝ) / 2 ^ p)

/-- The membership bit `1_K(decodePoint z)` of a point-register string `z` (decided classically, so
exactly, boundary points included). -/
noncomputable def memBit {d : ℕ} (K : Set (Euc d)) (b p : ℕ) (z : Qubits (d * b)) : Bool :=
  haveI := Classical.dec (decodePoint d b p z ∈ K)
  decide (decodePoint d b p z ∈ K)

/-- The answer qubit flipped by the membership bit: `|z, c⟩ ↦ |z, c ⊕ 1_K(decodePoint z)⟩`, the
answer qubit being the last wire `Fin.last (d·b)`. -/
noncomputable def memFlip {d : ℕ} (K : Set (Euc d)) (b p : ℕ) (x : Qubits (d * b + 1)) :
    Qubits (d * b + 1) :=
  Function.update x (Fin.last (d * b))
    (xor (x (Fin.last (d * b))) (memBit K b p (fun i => x (Fin.castSucc i))))

/-- Zhang, §2.4, p.23: the **strong coherent membership oracle** `O_K` for the coordinate format
`(b, p)`, the permutation matrix of `memFlip` (column `x` has its `1` in row `memFlip x`). -/
noncomputable def memOracle {d : ℕ} (K : Set (Euc d)) (b p : ℕ) :
    Matrix (Qubits (d * b + 1)) (Qubits (d * b + 1)) ℂ :=
  Matrix.of fun y x => if y = memFlip K b p x then 1 else 0

/-- The point register of format `(b, p)` on `d` coordinates represents every point of the lattice
`2^{-p} ℤ^d` lying in `S`: each integer coordinate `k_i` of such a point is in the `b`-bit
two's-complement range `[−2^{b−1}, 2^{b−1})` (so `b ≥ 1` as soon as `S` meets the lattice). -/
def RegCovers (d b p : ℕ) (S : Set (Euc d)) : Prop :=
  ∀ k : Fin d → ℤ, latticePt ((2 : ℝ)⁻¹ ^ p) k ∈ S →
    ∀ i, -((2 : ℤ) ^ (b - 1)) ≤ k i ∧ k i < (2 : ℤ) ^ (b - 1) ∧ 1 ≤ b

end QVolKLS


