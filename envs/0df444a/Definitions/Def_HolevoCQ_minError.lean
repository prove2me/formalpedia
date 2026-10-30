-- Prove2me | Definitions.Def_HolevoCQ_minError
-- name    : HolevoCQ_minError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:58.036094+00:00
-- url     : https://prove2.me/theorems/e76636cf-5953-43d1-9a86-6b20ad2bcd72
-- title:
--   Minimal average error probability $p(n,N)$
-- statement:
--   Let $p(n,N)$ be the minimum of the average error probability $P_{er}$ over all codes $(u_1,X_1),\dots,(u_N,X_N)$ of size $N$ with words $u_k\in A^n$ of length $n$ and positive decision operators on $\mathcal H^{\otimes n}$ with $\sum_kX_k\le I$:
--
--   $$
--   p(n,N)=\min_{(u_k,X_k)}\frac1N\sum_{k=1}^N\big[1-\mathrm{Tr}\,S_{u_k}X_k\big].
--   $$
--
--   The coding theorem (4) describes the behaviour of $p(n,2^{nR})$.
--
--   **Formalization Note** Words may repeat. The minimum is the real `sInf`; the set is nonempty and bounded below by $0$.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, p.2

import Mathlib
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_HolevoCQ_IsSubPOVM
import Definitions.Def_HolevoCQ_avgError

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, p.2: `p(n, N)`, the minimum of the average error probability
`P_er = (1/N) Σ_k [1 − Tr S_{u_k} X_k]` over all codes of size `N` with words of length `n`: a
code is a sequence `(u₁, X₁), …, (u_N, X_N)` of words `u_k ∈ Aⁿ` and positive operators `X_k`
on `H^{⊗n}` with `Σ_k X_k ≤ I`.

**Formalization Note.** Words may repeat (`c : Fin N → Fin n → A` is any sequence). The real
`sInf` is the paper's minimum: the set is nonempty (e.g. all `X_k = 0`) and bounded below by
`0`. At `N = 0` the value is `0`. -/
noncomputable def minError {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (n N : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ c : Fin N → Fin n → A, ∃ X : Fin N → Matrix (Fin n → D) (Fin n → D) ℂ,
    IsSubPOVM X ∧ e = avgError (fun k => wordState S n (c k)) X}

end HolevoCQ


