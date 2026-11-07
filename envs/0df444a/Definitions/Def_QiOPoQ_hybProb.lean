-- Prove2me | Definitions.Def_QiOPoQ_hybProb
-- name    : QiOPoQ_hybProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:04:18.623957+00:00
-- url     : https://prove2.me/theorems/2315791c-c8c0-4e14-93a4-70955f6b330a
-- title:
--   The hybrids $H_k$ of the proof of Theorem 4.7
-- statement:
--   For $k\le2t$, the hybrid $H_k$ samples a uniform $b\in\{0,1\}^t$, computes $y:=f(b)$ and independent obfuscations $\hat C_1,\dots,\hat C_t$, where for $i<t$:
--
--   - in $H_{2i}$: $\hat C_j\leftarrow\mathrm{qiO}(1^\lambda,C_{0,\lambda})$ for $j\le i$ and $\hat C_j\leftarrow\mathrm{qiO}(1^\lambda,C_{b_j,\lambda})$ for $j>i$;
--   - in $H_{2i+1}$: the same, except $\hat C_{i+1}\leftarrow\mathrm{qiO}(1^\lambda,C_{1,\lambda})$;
--   - in $H_{2t}$: every $\hat C_j\leftarrow\mathrm{qiO}(1^\lambda,C_{0,\lambda})$.
--
--   The prover wins if its response $b'$ satisfies $f(b')=y$. `hybProb` is $p_k(\lambda)$, the winning probability of a classical adversary $A$ in $H_k$. $H_0$ has the distribution of the real challenge.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Theorem 4.7, pp.20, 22

import Mathlib
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_NUPPT
import Definitions.Def_QiOPoQ_fig6Challenge

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity QAdvFew.PoQOracle

variable {G : GateSet}

/-- The bit of the circuit obfuscated at position `j` (`0`-based; paper index `j + 1`) in hybrid
`H_k`, given the sampled `b`. Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage
and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), proof of
Theorem 4.7, pp.20 and 22: in `H_{2i}`, `Ĉ_j ← qiO(1^λ, C_{0,λ})` for `j ≤ i` and
`Ĉ_j ← qiO(1^λ, C_{b_j,λ})` for `j ≥ i + 1`; in `H_{2i+1}`, the same except
`Ĉ_{i+1} ← qiO(1^λ, C_{1,λ})`; "Hybrid 2t is defined as having sampled b and y as every other
hybrid, and all circuits being obfuscations of C_{0,λ}". -/
def hybBit (k : ℕ) (b : Str) (j : ℕ) : Bool :=
  if j < k / 2 then false else if k % 2 = 1 ∧ j = k / 2 then true else b.getD j false

/-- `E[g(Obf(x₁), …, Obf(x_k))]` over independent coins for each call. -/
noncomputable def obfListExpect (Obf : UPPT) : List Str → (List Str → ℝ) → ℝ
  | [], g => g []
  | x :: xs, g => Obf.expect x fun c => obfListExpect Obf xs fun cs => g (c :: cs)

/-- **The hybrids of the proof of Theorem 4.7.** arXiv:2609.40289, proof of Theorem 4.7, pp.20,
22: "Sample a uniformly random b ← {0, 1}^t and compute y := f(b). Compute the obfuscated circuits
Ĉ_1, . . . , Ĉ_t as follows: … Given a response b′, the prover wins if f(b′) = y." … "For a
classical PPT adversary A, let p_n be its success probability for hybrid n."

`hybProb Obf Cb f t A λ k` is `p_k(λ)`: the probability that `A(1^λ, (Ĉ_1, …, Ĉ_t, f(b)))`
outputs `b′` with `f(b′) = f(b)`, where `b` is uniform in `{0,1}^{t(λ)}` and `Ĉ_{j+1}` is an
independent obfuscation of `C_{hybBit k b j, λ}`. `H_0` uses `C_{b_j,λ}` everywhere (the real
challenge distribution) and `H_{2t}` uses `C_{0,λ}` everywhere. -/
noncomputable def hybProb (Obf : UPPT) (Cb : Bool → ℕ → Circ G) (f : Str → Str) (t : ℕ → ℕ)
    (A : NUPPT) (n k : ℕ) : ℝ :=
  avgCoins (t n) fun b =>
    obfListExpect Obf ((List.range (t n)).map fun j => obfIn Cb (hybBit k b j) n) fun cs =>
      A.expect n (tup (cs ++ [f b])) fun b' => if f b' = f b then 1 else 0

end QiOPoQ


