-- Prove2me | Definitions.Def_DHRUniq_LQCCFamily
-- name    : DHRUniq_LQCCFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:44.58235+00:00
-- url     : https://prove2.me/theorems/aee73c47-106a-4d28-b70d-d0616fc046ff
-- title:
--   Kraus operators $V^{AB}_{i_1\dots i_{2n}}$ of an $n$-round LQCC protocol
-- statement:
--   This is the round-by-round construction of the operators of Definition 4. Start from $\mathcal H^A_1\otimes\mathcal H^B_1$ with the empty history and the identity operator. In round $k$ the protocol fixes spaces $\mathcal H^A_{k+1}$, $\mathcal H^B_{k+1}$ and outcome counts $K_{2k-1},K_{2k}$, independently of the history. For every history, Alice has operators $V_{2k-1}^{i_{2k-1},\dots,i_1}:\mathcal H^A_k\to\mathcal H^A_{k+1}$ with
--
--   $$
--   \sum_{i_{2k-1}}\big(V_{2k-1}^{i_{2k-1},\dots,i_1}\big)^\dagger V_{2k-1}^{i_{2k-1},\dots,i_1}=\mathbb 1^A_k ,
--   $$
--
--   and then Bob has operators $W_{2k}^{i_{2k},\dots,i_1}:\mathcal H^B_k\to\mathcal H^B_{k+1}$ with
--
--   $$
--   \sum_{i_{2k}}\big(W_{2k}^{i_{2k},\dots,i_1}\big)^\dagger W_{2k}^{i_{2k},\dots,i_1}=\mathbb 1^B_k .
--   $$
--
--   After $n$ rounds the operator with history $(i_1,\dots,i_{2n})$ is
--
--   $$
--   V^{AB}_{i_1\dots i_{2n}}=(\mathbb 1^A_{n+1}\otimes W_{2n}^{i_{2n},\dots,i_1})(V_{2n-1}^{i_{2n-1},\dots,i_1}\otimes\mathbb 1^B_n)\cdots(\mathbb 1^A_2\otimes W_2^{i_2,i_1})(V_1^{i_1}\otimes\mathbb 1^B_1).
--   $$
--
--   **Formalization Note** Each operator depends on the whole history, whereas the spaces and outcome counts depend on the round alone, as in eqs. (7)–(8). In printed (8-a) the index runs over $k=0,\dots,n-1$ for $V_{2k+1}$; the relation above is the same after shifting $k$. The intermediate spaces are finite index types.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Definition 4, p. 5, eqs. (6)–(8)

import Mathlib

open Kronecker Matrix

namespace DHRUniq

/-- **The Kraus operators `V^{AB}_{i_1,…,i_{2n}}` of an `n`-round LQCC protocol** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2,
Definition 4, p. 5, eqs. (6)–(8)), built round by round. `LQCCFamily a b n x y ι K` says that
`K : ι → Matrix (x × y) (a × b) ℂ` is the family of products of the first `n` rounds of a protocol
that starts on `ℂ^a ⊗ ℂ^b`, has reached the spaces `H^A_{n+1} = ℂ^x`, `H^B_{n+1} = ℂ^y`, and whose
index type `ι` is the set of histories `(i_1, …, i_{2n})`.

* `start`: before any round the only history is empty and the operator is the identity.
* `round`: round `k = n + 1` chooses the next spaces `ℂ^{x'}`, `ℂ^{y'}` and outcome counts
  `KA = K_{2k-1}`, `KB = K_{2k}`, all independent of the history. Alice applies
  `V_{2k-1}^{i_{2k-1},…,i_1} : H^A_k → H^A_{k+1}` (`V h i`, `h` the earlier history), then Bob
  applies `W_{2k}^{i_{2k},…,i_1} : H^B_k → H^B_{k+1}` (`W (h, i) j`), with (8-a)
  `∑_i V†V = 1^A_k` for every history and (8-b) `∑_j W†W = 1^B_k` for every history.
  The new operator is `(1^A_{k+1} ⊗ W)(V ⊗ 1^B_k) K`, the paper's product read from right to left.

**Formalization Note** Printed (8-a) has `k = 0, …, n-1` for `V_{2k+1}`, so its unit operator
`1^A_{k+1}` is the unit of the domain of `V_{2k+1}`; `hV` is that relation after the shift
`k + 1 ↦ k`. Spaces and outcome counts depend on the round only; the operators depend on the whole
history. The inductive form spells out the sequences `(H^A_k)`, `(H^B_k)`, `(K_j)` of Definition 4
without dependent indexing of the endpoints. -/
inductive LQCCFamily (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    ℕ → (x y ι : Type) → [Fintype x] → [DecidableEq x] → [Fintype y] → [DecidableEq y] →
      (ι → Matrix (x × y) (a × b) ℂ) → Prop
  | start : LQCCFamily a b 0 a b Unit (fun _ => 1)
  | round {n : ℕ} {x y ι x' y' : Type} [Fintype x] [DecidableEq x] [Fintype y] [DecidableEq y]
      [Fintype x'] [DecidableEq x'] [Fintype y'] [DecidableEq y']
      {K : ι → Matrix (x × y) (a × b) ℂ} (hK : LQCCFamily a b n x y ι K)
      (KA KB : ℕ) (V : ι → Fin KA → Matrix x' x ℂ) (W : ι × Fin KA → Fin KB → Matrix y' y ℂ)
      (hV : ∀ h, ∑ i, (V h i)ᴴ * V h i = 1) (hW : ∀ h, ∑ j, (W h j)ᴴ * W h j = 1) :
      LQCCFamily a b (n + 1) x' y' ((ι × Fin KA) × Fin KB)
        (fun t => ((1 : Matrix x' x' ℂ) ⊗ₖ W t.1 t.2) *
          ((V t.1.1 t.1.2 ⊗ₖ (1 : Matrix y y ℂ)) * K t.1.1))

end DHRUniq


