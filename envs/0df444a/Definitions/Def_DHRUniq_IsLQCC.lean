-- Prove2me | Definitions.Def_DHRUniq_IsLQCC
-- name    : DHRUniq_IsLQCC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:37.582498+00:00
-- url     : https://prove2.me/theorems/f9760af9-f3aa-4b32-86bb-35c7ab03c5f8
-- title:
--   LQCC operation
-- statement:
--   A map $\Lambda:\mathcal T(\mathcal H^A\otimes\mathcal H^B)\to\mathcal T(\mathcal K^A\otimes\mathcal K^B)$ is an **LQCC operation** (local quantum operations assisted by bidirectional classical communication) if there exist $n>0$ and an $n$-round protocol from $\mathcal H^A,\mathcal H^B$ to $\mathcal K^A,\mathcal K^B$ with operators $V^{AB}_{i_1\dots i_{2n}}$ such that, for all $\sigma$,
--
--   $$
--   \Lambda(\sigma)=\sum_{i_1,\dots,i_{2n}}V^{AB}_{i_1\dots i_{2n}}\,\sigma\,V^{AB\,\dagger}_{i_1\dots i_{2n}}.
--   $$
--
--   This is the class of operations under which entanglement may not increase.
--
--   **Formalization Note** The local spaces may change between input and output. The formula holds for every matrix, so $\Lambda$ is linear; complete positivity and trace preservation follow from its form. The published `WildeQIT.EntManip.IsLOCC` is a different presentation and is not used.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Definition 4, p. 5

import Mathlib
import Definitions.Def_DHRUniq_LQCCFamily

open Matrix

namespace DHRUniq

/-- **LQCC operation** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Definition 4, p. 5): a map
`Λ : T(H^A ⊗ H^B) → T(K^A ⊗ K^B)` for which there are `n > 0` rounds with
`H^{A(B)}_1 = H^{A(B)}`, `H^{A(B)}_{n+1} = K^{A(B)}` such that
`Λ(σ) = ∑_{i_1,…,i_{2n}} V^{AB}_{i_1…i_{2n}} σ V^{AB†}_{i_1…i_{2n}}` for all `σ` (eq. (6)), with
the operators of `LQCCFamily`.

**Formalization Note** `H^A = ℂ^a`, `H^B = ℂ^b`, `K^A = ℂ^{a'}`, `K^B = ℂ^{b'}`; the local spaces
may change, in either direction of dimension. The formula holds for every matrix `σ`, so `Λ` is
linear; complete positivity and trace preservation follow from the form. The published
`WildeQIT.EntManip.IsLOCC` is a different presentation and is not reused. -/
def IsLQCC {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ) : Prop :=
  ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (K : ι → Matrix (a' × b') (a × b) ℂ),
    0 < n ∧ LQCCFamily a b n a' b' ι K ∧ ∀ σ, Λ σ = ∑ i, K i * σ * (K i)ᴴ

end DHRUniq


