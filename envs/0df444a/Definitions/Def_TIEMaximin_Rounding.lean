-- Prove2me | Definitions.Def_TIEMaximin_Rounding
-- name    : TIEMaximin_Rounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:39:15.032371+00:00
-- url     : https://prove2.me/theorems/fc13754d-4372-4441-9f66-689a2a0cb0c5
-- title:
--   The three properties of the rounding lottery of Lemma 4.3
-- statement:
--   A lottery over integral suballocations has the properties of Lemma 4.3 for the fractional suballocation $b$ and positive integers $k_i$ if it implements $b$, preserves all coordinates equal to one, and every supported suballocation $A$ satisfies, for every agent $i$,
--
--   $$|v_i(A_i)-v_i(b_i)|\le\Bigl(1-\frac1{k_i}\Bigr)\max_{g\in M:\,0<b_{ig}<1}v_i(g),$$
--
--   where an empty maximum is zero and $v_i(b_i)=\sum_g b_{ig}v_i(g)$.
--
--   **Formalization Note** The empty maximum is an explicit case split, not a default value of a supremum.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 4.3, eq. (15), p.21

import Mathlib
import Definitions.Def_TIEMaximin_Basic

namespace TIEMaximin

open Finset

/-- `max_{g ∈ M : 0 < b_g < 1} u(g)`, where an empty maximum is zero (Lemma 4.3, p.21 of
arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
noncomputable def maxFrac {m : ℕ} (u b : Fin m → ℝ) : ℝ :=
  if h : ({g | 0 < b g ∧ b g < 1} : Finset (Fin m)).Nonempty then
    ({g | 0 < b g ∧ b g < 1} : Finset (Fin m)).sup' h u
  else 0

/-- **The three properties of the lottery of Lemma 4.3** (p.21) for the fractional suballocation `b`:
it implements `b`, preserves all coordinates equal to one, and every supported suballocation satisfies
`|v_i(A_i) − v_i(b_i)| ≤ (1 − 1/k_i) max_{g : 0 < b_ig < 1} v_i(g)` (15).

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 4.3, p.21.

**Formalization Note.** `v_i(b_i) = Σ_g b_ig v_i(g)` (§2, p.7). A `PMF` on the finite type of integral
suballocations is automatically a finite lottery. -/
def IsRounding {n m : ℕ} (v b : Fin n → Fin m → ℝ) (k : Fin n → ℕ) (μ : PMF (SubAlloc n m)) : Prop :=
  SubImplements μ b ∧
  (∀ i g, b i g = 1 → ∀ A ∈ μ.support, A g = some i) ∧
  ∀ A ∈ μ.support, ∀ i,
    |subValOf (v i) i A - ∑ g, b i g * v i g| ≤ (1 - 1 / (k i : ℝ)) * maxFrac (v i) (b i)

end TIEMaximin


