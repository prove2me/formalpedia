-- Prove2me | Definitions.Def_PrefDeals_aagS1
-- name    : PrefDeals_aagS1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:14.578153+00:00
-- url     : https://prove2.me/theorems/1975c266-6395-41eb-9907-aab00b0f8b60
-- title:
--   Buyers $S_1$ with a positive probability of the highest valuation
-- statement:
--   Let $A\subseteq\Omega$ be a stream of impressions and $S$ a set of buyers. The algorithm splits $S$ into
--
--   $$
--   S_0=\{j\in S:\ \Pr_A[v_j=v_{(1)}(S)]=0\},\qquad S_1=S\setminus S_0 .
--   $$
--
--   The buyers in $S_1$ would win the impression with positive probability in a second-price auction among $S$; the buyers in $S_0$ never would, and receive the empty deal.
--
--   **Formalization Note** $\Pr_A[E]=0$ is written $P(A\cap E)=0$, the same condition. If $P(A)=0$, every buyer is in $S_0$.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Figure 1, p.11

import Mathlib
import Definitions.Def_PrefDeals_vmax

open MeasureTheory

namespace PrefDeals

open Classical in
/-- The buyers `S₀ = {j ∈ S | Pr_𝓘[vⱼ = v₍₁₎(S)] = 0}` who never have the highest valuation on the
stream `A` (Figure 1, p.11). -/
noncomputable def aagS0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (A : Set Ω) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun j => P (A ∩ {ω | M.v j ω = vmax M S ω}) = 0)

/-- **The buyers `S₁` with a positive probability of the highest valuation.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Figure 1, p.11: "Let
`S₀ = {j ∈ S | Pr_𝓘[vⱼ = v₍₁₎(S)] = 0}` and `S₁ = S \ S₀`."

For a stream `A ⊆ Ω` and a set of buyers `S`, `aagS0 M A S` is the set of `j ∈ S` with
`P(A ∩ {vⱼ = v₍₁₎(S)}) = 0`, and `aagS1 M A S = S \ aagS0 M A S`.

**Formalization Note.** The paper's `Pr_𝓘[E] = P(𝓘 ∩ E)/P(𝓘)`; whether it is `0` does not depend on the
normalization, so the unnormalized `P(A ∩ E) = 0` is used. If `P(A) = 0`, every buyer is in `S₀`. -/
noncomputable def aagS1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (A : Set Ω) (S : Finset (Fin n)) : Finset (Fin n) :=
  S \ aagS0 M A S

end PrefDeals


