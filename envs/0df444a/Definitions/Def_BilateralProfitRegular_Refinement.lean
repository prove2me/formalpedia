-- Prove2me | Definitions.Def_BilateralProfitRegular_Refinement
-- name    : BilateralProfitRegular_Refinement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:19:36.823005+00:00
-- url     : https://prove2.me/theorems/4466683f-7b68-4a3e-929a-d6228790ac4c
-- title:
--   Algorithm 8's refinement step: phase lengths (56), copies, averages, $\hat r=1/\max\{\hat L,1/(10\delta)\}$ and the event (57)
-- statement:
--   In phase $j$ of Successive Opt (Algorithm 8) the accuracy is $\varepsilon_j=\delta2^{-j}$. Refinement runs $\lceil C_0\log(2T)\rceil$ independent copies of ConOpt, each for
--   $$n=4^j\lceil C_0\log^4(2T)\rceil$$
--   loss observations; this is eq. (56). For each copy it computes the average query $\bar y=n^{-1}\sum_\tau x_\tau$ and the empirical average loss $\hat L=n^{-1}\sum_\tau Y_\tau$. It selects a copy with the smallest $\hat L$ and returns its $\bar y$ together with $\hat r=1/\max\{\hat L,1/(10\delta)\}$.
--
--   **RefineGood** is the event that (57) holds for every copy attaining the smallest $\hat L$:
--   $$\bar y\in\mathcal K,\qquad \max_{\mathcal K}r_\lambda-\varepsilon\le\hat r\le r_\lambda(\bar y)+\varepsilon.$$
--
--   **Formalization Note** Requiring (57) of every minimizing copy covers any tie-breaking rule. "Max over $\mathcal K$" is written with $\forall x\in\mathcal K$.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Algorithm 8, p.41 (PDF 43); eq. (56)–(57), p.44 (PDF 46)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Auxiliary

namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

/-! # Refinement in Successive Opt (Algorithm 8, eq. (56))

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), Algorithm 8, p.41
(PDF 43) and §6.3, p.44 (PDF 46): in phase `j`, at accuracy `ε_j = δ 2^{-j}`, refinement runs
`⌈C₀ log(2T)⌉` independent copies of ConOpt, each for `n = 4^j ⌈C₀ log⁴(2T)⌉` loss observations
(56); for each copy it averages the queries (`ȳ`) and the observations (`L̂`); it selects the copy
with the smallest `L̂` and returns its `ȳ` and `r̂ = 1/max{L̂, 1/(10δ)}`.

**Formalization Note.** A copy's trajectory is `h : Fin n → (ℝ × ℝ) × ℝ` (query, observation).
`RefineGood` is the event that (57) holds for **every** copy attaining the smallest `L̂` (so for
any tie-breaking), together with `ȳ ∈ 𝒦`; "max over `𝒦`" is written with `∀ x ∈ 𝒦`. Natural
logarithms. -/

/-- The accuracy `ε_j = δ 2^{-j}` of phase `j`. -/
noncomputable def acc (δ : ℝ) (j : ℕ) : ℝ := δ * (1 / 2) ^ j

/-- The run length `n = 4^j ⌈C₀ log⁴(2T)⌉` of phase `j` (eq. (56)). -/
noncomputable def phaseLen (C₀ : ℝ) (T j : ℕ) : ℕ := 4 ^ j * ⌈C₀ * Real.log (2 * T) ^ 4⌉₊

/-- The number `⌈C₀ log(2T)⌉` of independent copies per refinement. -/
noncomputable def numCopies (C₀ : ℝ) (T : ℕ) : ℕ := ⌈C₀ * Real.log (2 * T)⌉₊

/-- The average query `ȳ = n⁻¹ ∑_τ x_τ` of a copy. -/
noncomputable def avgQuery {n : ℕ} (h : Fin n → (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  ((n : ℝ)⁻¹) • ∑ τ, (h τ).1

/-- The empirical average loss `L̂ = n⁻¹ ∑_τ Y_τ` of a copy. -/
noncomputable def avgObs {n : ℕ} (h : Fin n → (ℝ × ℝ) × ℝ) : ℝ :=
  (∑ τ, (h τ).2) / n

/-- The auxiliary-profit estimate `r̂ = 1/max{L̂, 1/(10δ)}`. -/
noncomputable def rhatOf (δ Lhat : ℝ) : ℝ := 1 / max Lhat (1 / (10 * δ))

/-- Eq. (57) for the refinement output: for every copy `m` with the smallest `L̂`,
`ȳ_m ∈ 𝒦` and `max_{𝒦} r_λ − ε ≤ r̂ ≤ r_λ(ȳ_m) + ε`. -/
def RefineGood (E : Environment) (lam δ ε : ℝ) (K : Set (ℝ × ℝ)) {M n : ℕ}
    (hs : Fin M → Fin n → (ℝ × ℝ) × ℝ) : Prop :=
  ∀ m, (∀ m', avgObs (hs m) ≤ avgObs (hs m')) →
    avgQuery (hs m) ∈ K ∧
    (∀ x ∈ K, auxProfit E lam x - ε ≤ rhatOf δ (avgObs (hs m))) ∧
    rhatOf δ (avgObs (hs m)) ≤ auxProfit E lam (avgQuery (hs m)) + ε

end BilateralProfitRegular


