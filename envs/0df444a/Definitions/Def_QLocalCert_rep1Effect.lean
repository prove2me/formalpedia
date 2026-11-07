-- Prove2me | Definitions.Def_QLocalCert_rep1Effect
-- name    : QLocalCert_rep1Effect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:58.417106+00:00
-- url     : https://prove2.me/theorems/685b8b9a-9588-41ec-96d5-52bfb9503fbf
-- title:
--   Protocol 1: the accepting effect of one repetition and of $m$ repetitions
-- statement:
--   Protocol 1 runs on a path $v_0,\dots,v_r$ ($r\ge1$) with fingerprints $|h_x\rangle,|h_y\rangle$ of $\ell$ qubits. In each repetition, $v_j$ ($0\le j\le r-1$) holds a pair of blocks $(A_j,B_j)$ and $v_r$ a single block $A_r$; on a yes-instance the honest certificate puts $|h_x\rangle$ in every block. Each $v_j$, $j<r$, flips a fair coin $s_j$ and swaps its two blocks if $s_j=1$, keeps $\tilde A_j$ and sends $\tilde B_j$ to $v_{j+1}$. The tests are:
--   1. $T_0$: $v_0$ measures $\{|h_x\rangle\langle h_x|,I-|h_x\rangle\langle h_x|\}$ on $\tilde A_0$;
--   2. $T_j$, $1\le j\le r-1$: $v_j$ performs the SWAP test on $(\tilde B_{j-1},\tilde A_j)$;
--   3. $v_r$ flips a fair coin $t$ and performs the SWAP test on $(\tilde B_{r-1},A_r)$ if $t=0$ ($T_r$), or measures $\{|h_y\rangle\langle h_y|,I-|h_y\rangle\langle h_y|\}$ on $A_r$ if $t=1$ ($T_{r+1}$).
--
--   The accepting effect of one repetition, averaged over its coins, is
--   $$
--   M=2^{-r}\sum_{s\in\{0,1\}^r}\tfrac12\sum_{t\in\{0,1\}}U_s^\dagger\,T(t)\,U_s,
--   $$
--   where $U_s$ is the symmetrization permutation and $T(t)$ the tensor product of the performed tests. The effect of $m$ repetitions on disjoint blocks with independent coins is $\bigotimes_{k=1}^mM_k$; the honest certificate is $|h_x\rangle^{\otimes(2r+1)m}$.
--
--   **Formalization Note** The blocks of one repetition are indexed by $(\{0,1\}^\ell\times\{0,1\}^\ell)^r\times\{0,1\}^\ell$ (`Blk r ℓ`). In `testOp`, the factor $j$ is the test on $(B_j,A_{j+1})$, $A_r$ being the single block; the SWAP test is $\Pi_+$ of `swapOp`. $U_s^\dagger TU_s$ is the reindexing `submatrix` along the involution `swapPerm s`. Fingerprints are vectors `Qb ℓ → ℂ`.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Protocol 1, p.17; proof of Lemma 10, p.21

import Mathlib
import Definitions.Def_QLocalCert_piKron
import Definitions.Def_QLocalCert_swapOp

set_option autoImplicit false

namespace QLocalCert

open Matrix

/-- The blocks of one repetition of Protocol 1 on the path `v₀, …, v_r` with `ℓ`-qubit
fingerprints: the pairs `(A_j, B_j)` held by `v_j`, `0 ≤ j ≤ r − 1`, and the single block `A_r`
held by `v_r`.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Protocol 1, p.17 ("each node v_j with
0 ≤ j ≤ r−1 receives an ordered pair of blocks (A_j^{(k)}, B_j^{(k)}), and v_r receives a single
block A_r^{(k)}"). -/
abbrev Blk (r ℓ : ℕ) := (Fin r → Qb ℓ × Qb ℓ) × Qb ℓ

/-- The block `A₀` (for `r ≥ 1`). -/
def firstA {r ℓ : ℕ} (x : Blk r ℓ) : Qb ℓ := if h : 0 < r then (x.1 ⟨0, h⟩).1 else x.2

/-- The block `A_{j+1}` paired with `B_j` in test `T_{j+1}` (`A_r` for `j = r − 1`). -/
def nextA {r ℓ : ℕ} (x : Blk r ℓ) (j : Fin r) : Qb ℓ :=
  if h : j.val + 1 < r then (x.1 ⟨j.val + 1, h⟩).1 else x.2

/-- Matrix entries of the rank-one projector `|h⟩⟨h|`. -/
def projEntry {ℓ : ℕ} (h : Qb ℓ → ℂ) (a a' : Qb ℓ) : ℂ := h a * star (h a')

/-- The joint test of one repetition of Protocol 1 after symmetrization, for the endpoint coin
`t` of `v_r` (Protocol 1, p.17): `T₀ = |h_x⟩⟨h_x|` on `Ã₀`; `T_j = Π+` (SWAP test) on
`(B̃_{j−1}, Ã_j)` for `1 ≤ j ≤ r − 1`; and on `(B̃_{r−1}, A_r)` either `T_r = Π+` (`t = false`,
i.e. `t^{(k)} = 0`) or `T_{r+1} = I ⊗ |h_y⟩⟨h_y|` (`t = true`). The tests act on disjoint
registers, so the operator is their tensor product. Indexing: the factor `j : Fin r` is the test
`T_{j+1}` on `(B_j, A_{j+1})`. -/
noncomputable def testOp {ℓ : ℕ} (hx hy : Qb ℓ → ℂ) (r : ℕ) (t : Bool) :
    Matrix (Blk r ℓ) (Blk r ℓ) ℂ :=
  fun x y => projEntry hx (firstA x) (firstA y) * ∏ j : Fin r,
    if j.val + 1 = r ∧ t = true then
      (if (x.1 j).2 = (y.1 j).2 then 1 else 0) * projEntry hy (nextA x j) (nextA y j)
    else symProj (Qb ℓ) ((x.1 j).2, nextA x j) ((y.1 j).2, nextA y j)

/-- The symmetrization of Protocol 1 for coins `s = (s₀, …, s_{r−1})`: node `v_j` swaps the two
blocks of its pair when `s_j = 1`. After it, `Ã_j` is the first and `B̃_j` the second component. -/
def swapPerm {r ℓ : ℕ} (s : Fin r → Bool) (x : Blk r ℓ) : Blk r ℓ :=
  (fun j => if s j then ((x.1 j).2, (x.1 j).1) else x.1 j, x.2)

/-- The accepting effect `M` of one repetition of Protocol 1 (p.17; proof of Lemma 10, p.21:
"the effective accepting POVM element of repetition k, averaged over its private coins"):
`M = 2^{−r} ∑_{s ∈ {0,1}^r} ½ ∑_{t ∈ {0,1}} U_s† T(t) U_s`, where `U_s` is the symmetrization
permutation and `T(t)` the joint test `testOp`.

**Formalization Note.** `U_s† T U_s` has entries `T(σ_s x, σ_s y)` for the involution
`σ_s = swapPerm s`, i.e. `T.submatrix σ_s σ_s`. The fingerprints `h_x, h_y` are vectors
`Qb ℓ → ℂ`. -/
noncomputable def rep1Effect {ℓ : ℕ} (hx hy : Qb ℓ → ℂ) (r : ℕ) : Matrix (Blk r ℓ) (Blk r ℓ) ℂ :=
  ((2 : ℂ) ^ r)⁻¹ • ∑ s : Fin r → Bool,
    (1 / 2 : ℂ) • ∑ t : Bool, (testOp hx hy r t).submatrix (swapPerm s) (swapPerm s)

/-- The accepting effect `⊗_{k=1}^m M_k` of `m` repetitions of Protocol 1 on disjoint registers
with independent coins (proof of Lemma 10, p.21). -/
noncomputable def mEffect {ℓ : ℕ} (hx hy : Qb ℓ → ℂ) (r m : ℕ) :
    Matrix (Fin m → Blk r ℓ) (Fin m → Blk r ℓ) ℂ :=
  piKron fun _ => rep1Effect hx hy r

/-- The honest certificate of Protocol 1 (p.17): "On a yes-instance the honest certificate places
every individual block in the state |h_x⟩". This is the vector `|h_x⟩^{⊗(2r+1)m}`. -/
def honestVec {ℓ : ℕ} (h : Qb ℓ → ℂ) (r m : ℕ) : (Fin m → Blk r ℓ) → ℂ :=
  fun x => ∏ k, ((∏ j, h ((x k).1 j).1 * h ((x k).1 j).2) * h (x k).2)

end QLocalCert


