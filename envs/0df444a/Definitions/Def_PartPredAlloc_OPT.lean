-- Prove2me | Definitions.Def_PartPredAlloc_OPT
-- name    : PartPredAlloc_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:15.598962+00:00
-- url     : https://prove2.me/theorems/bd9fbfa5-7ebc-4fe8-8025-9298cfbaf658
-- title:
--   Type counts $n_1,n_2$ and the offline optimum $OPT(\vec v)$, eq. (1)
-- statement:
--   For a sequence $\vec v$ of length $n$, let $n_1$ and $n_2$ be the numbers of type-1 and type-2 customers in it. With $b$ units of inventory, the optimum offline (clairvoyant) solution accepts all type-1 customers and, if $n_1<b$, $\min\{n_2,b-n_1\}$ type-2 customers, so its revenue is
--
--   $$
--   OPT(\vec v)=\min\{b,n_1\}+a\min\{n_2,(b-n_1)^+\},\qquad (x)^+=\max\{x,0\}.
--   $$
--
--   It depends on $\vec v$ only through $n_1,n_2$, so it is the same for the adversarial sequence $\vec v_I$ and for every arrival sequence obtained from it by permuting positions.
--
--   **Formalization Note** $b-n_1$ is computed in $\mathbb R$.
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, §3, eq. (1), p.9

import Mathlib
import Definitions.Def_PartPredAlloc_Cust

namespace PartPredAlloc

/-- `n₁`: the number of type-1 customers in a sequence `v` of length `n` (arXiv:1810.00447v1, §3,
p.9). -/
def nType1 {n : ℕ} (v : Fin n → Cust) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => v i = Cust.high)).card

/-- `n₂`: the number of type-2 customers in a sequence `v` of length `n` (arXiv:1810.00447v1, §3,
p.9). -/
def nType2 {n : ℕ} (v : Fin n → Cust) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => v i = Cust.low)).card

/-- The optimum offline revenue, eq. (1) of Hwang–Jaillet–Manshadi (arXiv:1810.00447v1, §3, p.9):
`OPT(v) = min{b, n₁} + a · min{n₂, (b − n₁)⁺}`, with `(x)⁺ = max{x, 0}`, for `b` units of inventory
and type-2 revenue `a`.

**Formalization Note.** It depends on `v` only through the counts `n₁, n₂`, so it is the same for
the adversarial sequence `v_I` and for every arrival sequence obtained from it by a permutation
(p.11: `OPT(V) = OPT(v_I)`). The subtraction `b − n₁` is taken in `ℝ`. -/
noncomputable def OPT {n : ℕ} (b : ℕ) (a : ℝ) (v : Fin n → Cust) : ℝ :=
  min (b : ℝ) (nType1 v) + a * min (nType2 v : ℝ) (max ((b : ℝ) - nType1 v) 0)

end PartPredAlloc


