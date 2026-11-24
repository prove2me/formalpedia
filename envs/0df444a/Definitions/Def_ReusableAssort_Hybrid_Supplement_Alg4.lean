-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Supplement_Alg4
-- name    : ReusableAssort_Hybrid_Supplement_Alg4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:17:11.445973+00:00
-- url     : https://prove2.me/theorems/ed3c319d-d3ac-4713-809f-6a694e47c4dd
-- title:
--   (EC.1) and Algorithm 4, pp. ec7–ec8 — inventory-dependent DP, thresholds and the algorithm
-- statement:
--   Objects of §EC.3.2 (non-reusable resources). Let $y$ be an LP solution and $X_{S,t,z} = y_{S,t,z}F_t(z)$.
--
--   1. **DP (EC.1).** For a product $i$, inventory level $I \ge 1$ and $t \le T$,
--   $$\mathcal E^I_{i,t} = \sum_{z} \sum_{S \in \mathcal S} X_{S,t,z} \max\bigl\{\mathcal E^I_{i,t+1},\ \phi^z(S,i)\bigl(r^z_i + \mathcal E^{I-1}_{i,t+1}\bigr) + \bigl(1 - \phi^z(S,i)\bigr)\mathcal E^I_{i,t+1}\bigr\},$$
--   with boundary values $\mathcal E^I_{i,T+1} = \mathcal E^0_{i,t} = 0$.
--   2. **Thresholds.** $Q^I_{i,t} = \mathcal E^I_{i,t+1} - \mathcal E^{I-1}_{i,t+1}$.
--   3. **Algorithm 4.** At each time $t$, after $z_t$ is revealed, sample $\hat S_t \sim \{y_{S,t,z_t}\}_S$; remove $i \in \hat S_t$ if no unit of $i$ is available or $r^{z_t}_i < Q^{I_{i,t}}_{i,t}$, where $I_{i,t}$ is the number of available units of $i$; offer $\tilde S_t$ = Sub-assortment Sampling$(\phi^{z_t}, \bar S_t, \{\phi^{z_t}(\hat S_t, i)\}_{i \in \bar S_t})$.
--
--   $\mathbb E[\mathrm{Rev}_4]$ is the expected revenue of Algorithm 4 from time $1$ with full inventory.
--
--   **Formalization Note** $\mathcal E^I_{i,t}$ is defined for every $I \ge 0$; only $I \le c_i$ is used. Ties $r^{z_t}_i = Q^{I_{i,t}}_{i,t}$ keep the product, as on the page.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec7 (PDF 33), (EC.1); p. ec8 (PDF 34), Algorithm 4

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_Process

namespace ReusableAssort.Hybrid.Supplement

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

/-- The inventory-dependent DP (EC.1), p. ec7: `E I y i m t = 𝓔^m_{i,t}` for `t ≤ T` and
`m ≥ 1`, with the boundary values `𝓔^0_{i,t} = 0` and `𝓔^m_{i,T+1} = 0` (and `0` for all
`t > T`):
`𝓔^m_{i,t} = Σ_z Σ_{S∈𝒮} X_{S,t,z} max{𝓔^m_{i,t+1}, ϕ^z(S,i)(r^z_i + 𝓔^{m−1}_{i,t+1})
  + (1 − ϕ^z(S,i)) 𝓔^m_{i,t+1}}`. -/
noncomputable def E (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    (m t : ℕ) : ℝ :=
  if _h : T < t then 0 else
  if m = 0 then 0 else
  ∑ z, ∑ S ∈ I.feas, X I y t z S *
    max (E I y i m (t + 1))
      (I.phi z S i * (I.r z i + E I y i (m - 1) (t + 1))
        + (1 - I.phi z S i) * E I y i m (t + 1))
termination_by T + 1 - t

/-- The inventory-dependent revenue thresholds `Q^m_{i,t} = 𝓔^m_{i,t+1} − 𝓔^{m−1}_{i,t+1}`
of Algorithm 4 (p. ec8). -/
noncomputable def Q (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    (t m : ℕ) : ℝ :=
  E I y i m (t + 1) - E I y i (m - 1) (t + 1)

/-- Keep probability of product `i ∈ Ŝ_t` at step `k` (time `t = t₀ + k`) under Algorithm 4
(lines 4–7): with `I_{i,t}` the units of `i` currently on hand, `i` is removed if there is no
available unit or `r^{z_t}_i < Q^{I_{i,t}}_{i,t}`, and kept otherwise. -/
noncomputable def alg4Keep (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (t₀ : ℕ) (ret : Fin n → ℕ → ℕ)
    (k : Fin (T + 1 - t₀)) (v : Fin (T + 1 - t₀) → Step n T Z) (i : Fin n) : ℝ :=
  let m := onHand I t₀ ret v i k.1
  if m = 0 then 0 else if Q I y i (t₀ + k.1) m ≤ I.r (v k).1 i then 1 else 0

/-- Expected revenue of Algorithm 4 (p. ec8) over times `1, …, T`, started with full
inventory: simulation `Ŝ_t ∼ y_{·,t,z_t}`, the discarding of `alg4Keep`, then Procedure 1 on
`(ϕ^{z_t}, S̄_t, {ϕ^{z_t}(Ŝ_t, i)})`. -/
noncomputable def expRevAlg4 (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) : ℝ :=
  expRevA I y 1 (alg4Keep I y 1 (fun _ _ => 0))

end ReusableAssort.Hybrid.Supplement


