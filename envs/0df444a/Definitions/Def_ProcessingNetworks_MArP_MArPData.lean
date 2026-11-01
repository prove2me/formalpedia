-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_MArPData
-- name    : ProcessingNetworks_MArP_MArPData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:57.973406+00:00
-- url     : https://prove2.me/theorems/ea97ebbb-42f2-4e33-822e-57a7bf5c3379
-- title:
--   ARMC data and arrivals data of a Markovian arrival process (Section E.1)
-- statement:
--   The data of a Markovian arrival process with $I$ arrival classes consist of:
--
--   1. the **ARMC data** $(\mathcal S,p,\Lambda)$: the state space $\mathcal S=\{1,\dots,d\}$, an initial distribution $p$, and a generator matrix $\Lambda$ whose jump matrix is irreducible;
--   2. a finite **batch space** $\Delta=\{\delta^1,\dots,\delta^r\}\subset\mathbb Z_+^I$;
--   3. the **arrivals data** $(\beta,q)$: rates $\beta_k(s)\ge 0$, and for each pair of states a sub-probability distribution $q_1(s,\tilde s),\dots,q_r(s,\tilde s)$, that is, $q_k(s,\tilde s)\ge 0$ and $\sum_{k=1}^r q_k(s,\tilde s)\le 1$, with the convention $q_k(s,s)=0$.
--
--   **Formalization Note** States and batch types are indexed by `Fin d` and `Fin r`. Since $\delta^1,\dots,\delta^r$ are the elements of the set $\Delta$, the map $k\mapsto\delta^k$ is injective. Generators satisfy property (D.2) here, so $d\ge 2$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Section E.1, p.304 (PDF p.320)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_MArP_jumpMatrix

namespace ProcessingNetworks.MArP

/-- The data of a Markovian arrival process with `I` arrival classes, `d` regulating states and `r`
batch types (Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2, Section E.1, p.304,
PDF p.320): the ARMC data `(S, p, Λ)` with `S = {1, …, d}`, initial distribution `p`, and generator
`Λ` whose jump matrix is irreducible; the batch space `Δ = {δ¹, …, δʳ} ⊂ ℤ₊^I`; and the arrivals data
`(β, q)` with `β_k(s) ≥ 0`, `q_k(s, s̃) ≥ 0`, `∑_k q_k(s, s̃) ≤ 1` and `q_k(s, s) = 0`.

**Formalization Note.** States and batch types are indexed by `Fin d` and `Fin r` (the book counts
from 1). `batch_injective` records that `δ¹, …, δʳ` are the elements of the set `Δ`. Property (D.2)
is part of `IsGenerator`, so `d ≥ 2`. -/
structure MArPData (I d r : ℕ) where
  p : PMF (Fin d)
  Λ : Fin d → Fin d → ℝ
  generator : IsGenerator Λ
  irreducible : ProcessingNetworks.Stability.Irreducible (jumpMatrix generator)
  δ : Fin r → Fin I → ℕ
  batch_injective : Function.Injective δ
  β : Fin r → Fin d → ℝ
  q : Fin r → Fin d → Fin d → ℝ
  β_nonneg : ∀ k s, 0 ≤ β k s
  q_nonneg : ∀ k s s', 0 ≤ q k s s'
  q_sum_le : ∀ s s', ∑ k, q k s s' ≤ 1
  q_diag : ∀ k s, q k s s = 0

end ProcessingNetworks.MArP


