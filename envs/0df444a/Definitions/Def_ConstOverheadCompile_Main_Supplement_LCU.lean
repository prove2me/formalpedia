-- Prove2me | Definitions.Def_ConstOverheadCompile_Main_Supplement_LCU
-- name    : ConstOverheadCompile_Main_Supplement_LCU
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:29:29.050601+00:00
-- url     : https://prove2.me/theorems/c143d6e0-3d2d-4374-8dee-2d82aad27db2
-- title:
--   The Taylor parameters $K,\Lambda_K,\alpha_k,\gamma$, the tuple encoding, the states $|\phi_{k,M}\rangle$, and the SELECT input form
-- statement:
--   Objects of the proof of Theorem 10 (§5), for a real constant $c$ and integers $n\ge1$, $M$, $K$.
--
--   1. **Taylor parameters** (Eqs. (46), (63)):
--   $$K=\Big\lceil\frac{cn}{\log_2(n+2)}\Big\rceil,\qquad \Lambda_K=\sum_{k=0}^K\frac{\pi^k}{k!},\qquad \alpha_k=\frac{\pi^k}{\Lambda_K\,k!},\qquad \gamma=\frac{e^{-i\pi 2^{-n}}}{\Lambda_K}.$$
--
--   2. **The $|k\rangle$ register.** For $0\le k\le K$, $|k\rangle$ is the computational basis state writing $k$ in binary (most significant bit first) on $r=\lceil\log_2(K+1)\rceil$ qubits; $|k\rangle\otimes v$ places it before a vector $v$ on further qubits.
--
--   3. **Tuple encoding** (Eq. (43)): for $(\ell_1,\dots,\ell_k)\in\mathbb N_+^k$,
--   $$|(\ell_1,\dots,\ell_k)\rangle=|0^{\ell_1-1}1\,0^{\ell_2-1}1\cdots0^{\ell_k-1}1\rangle,$$
--   a basis state of $\sum_j\ell_j$ qubits (empty for $k=0$).
--
--   4. **The states $|\phi_{k,M}\rangle$** (Eq. (44)): $|\phi_{0,M}\rangle=|+^M\rangle$ and, for $1\le k\le M$,
--   $$|\phi_{k,M}\rangle=\sum_{\substack{\ell_1,\dots,\ell_k\in\mathbb N_+\\ \sum_j\ell_j\le M}}\frac{1}{\sqrt{2^{\sum_j\ell_j}}}\,|(\ell_1,\dots,\ell_k)\rangle|+^{M-\sum_j\ell_j}\rangle,$$
--   a vector on $M$ qubits.
--
--   5. **SELECT** (Eqs. (53)–(54)): $P_\ell=Z_\ell$ (Pauli $Z$ on the $\ell$-th data qubit) if $\ell\le n$ and $P_\ell=I$ otherwise; the input/output form of SELECT with $b$ ancillas is
--   $$|k\rangle|(\ell_1,\dots,\ell_k)\rangle|+^{M-\sum_j\ell_j}\rangle|\phi\rangle|0^b\rangle$$
--   on $r+M+n+b$ qubits, in this order.
--
--   These are the ingredients of the linear-combination-of-unitaries construction behind Theorem 10: Lemma 11 compares $|\phi_{k,M}\rangle$ with $|+^M\rangle$, Lemma 12 prepares the weights $\sqrt{\alpha_k}$ and Lemma 13 implements SELECT.
--
--   **Formalization Note** The sum defining $|\phi_{k,M}\rangle$ runs over the tuples $\ell_j=f_j+1$ with $f:\{1,\dots,k\}\to\{0,\dots,M-1\}$ and $\sum_j\ell_j\le M$, which are exactly the tuples of Eq. (44). The value of `phiState k M` for $k>M$ (an empty sum, $0$) and of the tuple vector when $\sum_j\ell_j>M$ are never used. $\lceil\log_2(K+1)\rceil$ is `Nat.clog 2 (K + 1)`, the least $r$ with $K+1\le2^r$; $\log_2$ is `Real.logb 2`, positive at $n+2\ge3$. Qubit $\ell$ of the paper is wire $\ell-1$.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.12 Eqs. (43), (44), (46); p.13 Eqs. (51), (53), (54); p.14 Eq. (63)

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets

namespace ConstOverheadCompile.Main.Supplement

open QAlgorithms ConstOverheadCompile.Main

/-! ### The Taylor-series parameters of Eqs. (46) and (63) -/

/-- Eq. (46), p.12: the truncation order `K = ⌈c n / log₂(n + 2)⌉` for the constant `c`. -/
noncomputable def taylorK (c : ℝ) (n : ℕ) : ℕ :=
  ⌈c * (n : ℝ) / Real.logb 2 ((n : ℝ) + 2)⌉₊

/-- Eq. (46), p.12: the normalizing constant `Λ_K = Σ_{k=0}^{K} π^k / k!`. -/
noncomputable def lambdaK (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), Real.pi ^ k / (k.factorial : ℝ)

/-- Eq. (46), p.12: the weights `α_k = π^k / (Λ_K k!)`, `0 ≤ k ≤ K`. -/
noncomputable def alphaK (K k : ℕ) : ℝ :=
  Real.pi ^ k / (lambdaK K * (k.factorial : ℝ))

/-- Eq. (63), p.14: the explicit complex number `γ = e^{-iπ 2^{-n}} / Λ_K` with
`K = K(c, n)` of Eq. (46). -/
noncomputable def gammaC (c : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-((Real.pi * ((1 : ℝ) / 2) ^ n : ℝ) : ℂ) * Complex.I) /
    ((lambdaK (taylorK c n) : ℝ) : ℂ)

/-- p.13 (SELECT acts on `⌈log₂(K + 1)⌉ + M + n` qubits): the width
`r = ⌈log₂(K + 1)⌉` of the register holding `|k⟩`, `0 ≤ k ≤ K`, in binary. `Nat.clog 2 (K + 1)`
is the least `r` with `K + 1 ≤ 2^r`. -/
def kWidth (K : ℕ) : ℕ :=
  Nat.clog 2 (K + 1)

/-- The vector `|k⟩ ⊗ v` on `r + m` wires: the binary basis state `|k⟩` (`natToBits r k`, most
significant bit on wire `0`) on the first `r` wires and `v` on the last `m` wires. -/
noncomputable def kTensor {m : ℕ} (r k : ℕ) (v : EuclideanSpace ℂ (Qubits m)) :
    EuclideanSpace ℂ (Qubits (r + m)) :=
  WithLp.toLp 2 fun z =>
    (if (fun i : Fin r => z (Fin.castAdd m i)) = natToBits r k then 1 else 0) *
      v (fun i : Fin m => z (Fin.natAdd r i))

/-! ### The tuple encoding and the states `|ϕ_{k,M}⟩` (Eqs. (43)–(44)) -/

/-- The partial sum `ℓ_1 + ⋯ + ℓ_{i+1}` of a tuple `(ℓ_1, …, ℓ_k)` (the tuple's entry `i : Fin k`
is the paper's `ℓ_{i+1}`). -/
def partialSum {k : ℕ} (ℓ : Fin k → ℕ+) (i : Fin k) : ℕ :=
  ∑ j : Fin k, if j ≤ i then (ℓ j : ℕ) else 0

/-- The length `Σ_j ℓ_j` of the encoding of the tuple `ℓ`. -/
def tupleLen {k : ℕ} (ℓ : Fin k → ℕ+) : ℕ :=
  ∑ j : Fin k, (ℓ j : ℕ)

/-- Eq. (43), p.12: bit `p` (`0`-based, `p < Σ_j ℓ_j`) of the string
`0^{ℓ_1 - 1} 1 0^{ℓ_2 - 1} 1 … 0^{ℓ_k - 1} 1`: it is `1` exactly at the positions
`p + 1 = ℓ_1 + ⋯ + ℓ_i`. -/
def tupleBit {k : ℕ} (ℓ : Fin k → ℕ+) (p : ℕ) : Bool :=
  decide (∃ i : Fin k, p + 1 = partialSum ℓ i)

/-- The `M`-qubit vector `|(ℓ_1, …, ℓ_k)⟩|+^{M - Σ_j ℓ_j}⟩` of Eqs. (43)–(44) (used when
`Σ_j ℓ_j ≤ M`): the basis string of Eq. (43) on the first `Σ_j ℓ_j` wires, `|+⟩` on each of the
remaining `M - Σ_j ℓ_j` wires. -/
noncomputable def tuplePlusVec (M : ℕ) {k : ℕ} (ℓ : Fin k → ℕ+) :
    EuclideanSpace ℂ (Qubits M) :=
  WithLp.toLp 2 fun z =>
    if ∀ p : Fin M, (p : ℕ) < tupleLen ℓ → z p = tupleBit ℓ p then
      ((((Real.sqrt 2)⁻¹) ^ (M - tupleLen ℓ) : ℝ) : ℂ)
    else 0

/-- The uniform superposition `|+^M⟩` on `M` qubits. -/
noncomputable def plusM (M : ℕ) : EuclideanSpace ℂ (Qubits M) :=
  WithLp.toLp 2 fun _ => ((((Real.sqrt 2)⁻¹) ^ M : ℝ) : ℂ)

/-- The tuple of positive integers `(f_1 + 1, …, f_k + 1)`. Every tuple `ℓ ∈ ℕ₊^k` with
`Σ_j ℓ_j ≤ M` arises from exactly one `f : Fin k → Fin M`. -/
def succTuple {k M : ℕ} (f : Fin k → Fin M) : Fin k → ℕ+ :=
  fun j => ⟨(f j : ℕ) + 1, Nat.succ_pos _⟩

/-- Eq. (44), p.12: `|ϕ_{0,M}⟩ = |+^M⟩` and, for `1 ≤ k ≤ M`,
`|ϕ_{k,M}⟩ = Σ_{ℓ ∈ ℕ₊^k, Σ_j ℓ_j ≤ M} 2^{-Σ_j ℓ_j / 2} |(ℓ_1, …, ℓ_k)⟩|+^{M - Σ_j ℓ_j}⟩`.
The sum runs over the tuples `succTuple f`, `f : Fin k → Fin M`, with `Σ_j ℓ_j ≤ M`. -/
noncomputable def phiState (k M : ℕ) : EuclideanSpace ℂ (Qubits M) :=
  if k = 0 then plusM M
  else
    ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin M => tupleLen (succTuple f) ≤ M),
      ((((Real.sqrt 2)⁻¹) ^ tupleLen (succTuple f) : ℝ) : ℂ) • tuplePlusVec M (succTuple f)

/-! ### The SELECT operation (Eqs. (53)–(54)) -/

/-- Eq. (54), p.13: `P_ℓ = Z_ℓ` (Pauli `Z` on the paper's qubit `ℓ`, i.e. wire `ℓ - 1`) if
`ℓ ≤ n`, and `P_ℓ = I` otherwise, as an operator on `n` qubits. -/
def selP (n : ℕ) (ℓ : ℕ+) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal fun x =>
    if h : (ℓ : ℕ) ≤ n then
      (if x ⟨(ℓ : ℕ) - 1, by have := ℓ.pos; omega⟩ then -1 else 1)
    else 1

/-- The product `∏_{j=1}^{k} P_{ℓ_j}` (the factors commute). -/
def selProd (n : ℕ) {k : ℕ} (ℓ : Fin k → ℕ+) : Matrix (Qubits n) (Qubits n) ℂ :=
  (List.ofFn fun j => selP n (ℓ j)).prod

/-- The input/output form of Eq. (53), p.13, with `b` ancillas:
`|k⟩|(ℓ_1, …, ℓ_k)⟩|+^{M - Σ_j ℓ_j}⟩|ϕ⟩|0^b⟩` on `r + M + n + b` wires, in this order: the
binary `|k⟩` on `r` wires, the `M`-qubit register, the `n`-qubit data register `ϕ`, then the
ancillas in `|0⟩`. -/
noncomputable def selectState (r M n b k : ℕ) (ℓ : Fin k → ℕ+)
    (ϕ : EuclideanSpace ℂ (Qubits n)) : EuclideanSpace ℂ (Qubits (r + M + n + b)) :=
  WithLp.toLp 2 fun z =>
    (if (fun i : Fin r => z (Fin.castAdd b (Fin.castAdd n (Fin.castAdd M i)))) = natToBits r k
      then 1 else 0) *
    tuplePlusVec M ℓ (fun i : Fin M => z (Fin.castAdd b (Fin.castAdd n (Fin.natAdd r i)))) *
    ϕ (fun i : Fin n => z (Fin.castAdd b (Fin.natAdd (r + M) i))) *
    (if ∀ i : Fin b, z (Fin.natAdd (r + M + n) i) = false then 1 else 0)

end ConstOverheadCompile.Main.Supplement


