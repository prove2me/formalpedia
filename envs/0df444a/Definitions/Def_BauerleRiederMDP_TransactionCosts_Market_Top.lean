-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Top
-- name    : BauerleRiederMDP_TransactionCosts_Market_Top
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:08.322829+00:00
-- url     : https://prove2.me/theorems/decbcbb3-0542-4ff3-ac2c-5d1334ae6dee
-- title:
--   Maximal reward operator $T_n$ of the transaction cost model
-- statement:
--   For $v:E\to[-\infty,\infty)$,
--   $$T_nv(x)=\sup_{(a_0,a_1)\in D(x)}\mathbb E\, v\big(a_0(1+i_{n+1}),\ a_1\tilde R_{n+1}\big),\qquad x\in E.$$
--
--   **Formalization Note** The supremum is taken in $[-\infty,\infty]$ (`EReal`), with no default value.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.3.1 c), p.19 (PDF 34); §4.5, p.108 (PDF 122)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_admissibleSet
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Lop

namespace BauerleRiederMDP.TransactionCosts

/-- The maximal reward operator of the transaction cost model (Bäuerle & Rieder 2011,
Definition 2.3.1 c), p.19, PDF 34; for §4.5, p.108, PDF 122):
`T_n v(x) = sup_{(a₀, a₁) ∈ D(x)} IE v(a₀(1 + i_{n+1}), a₁ R̃_{n+1})`.

**Formalization Note.** The supremum is taken in `EReal`, a complete lattice, so it is the
book's supremum in `[−∞, ∞]` with no default value. -/
noncomputable def Market.Top {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (v : ℝ × ℝ → EReal) (x : ℝ × ℝ) : EReal :=
  ⨆ a ∈ admissibleSet M.c x, M.Lop n v x a

end BauerleRiederMDP.TransactionCosts


