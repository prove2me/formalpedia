-- Prove2me | Definitions.Def_AvgCostLP_IsLusinSets
-- name    : AvgCostLP_IsLusinSets
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:23.257716+00:00
-- url     : https://prove2.me/theorems/60669257-c5af-4d23-8fd7-99e46fa990b3
-- title:
--   Lemma 5.1 data and the family $\hat F_b(\mathbb X)$ of (5.6)
-- statement:
--   Given an (SU) sequence $\Gamma_j$, finite measures $\nu_j$ and closed sets $B^1_{j,m,\ell}$, $B^2_{j,\ell}\subset\mathbb X$, `IsLusinSets` says that they have the properties of Lemma 5.1: for all $j$ and all $m,\ell\ge1$,
--
--   1. $\nu_j(\mathbb X\setminus B^1_{j,m,\ell})\le\ell^{-1}$ and $\nu_j(\mathbb X\setminus B^2_{j,\ell})\le\ell^{-1}$;
--   2. restricted to $B^1_{j,m,\ell}\times F_j$ the truncated cost $c^m=\min\{c,m\}$ is continuous, and restricted to $B^2_{j,\ell}\times F_j$ the kernel $q(dy\mid\cdot,\cdot)$ is continuous, where $F_j=\mathrm{proj}_{\mathbb A}(\Gamma_j)$.
--
--   `testIndicators` is the countable family
--   $$\hat F_b(\mathbb X):=\{\mathbb 1_E\mid E=(O\setminus D)\cap B^c\text{ for some }(O,D,\nu,B)\in\mathcal W_1\cup\mathcal W_2\}, \tag{5.6}$$
--   with $\mathcal W_1=\{(O_j,D_j,\nu_j,B^1_{j,m,\ell})\}$ and $\mathcal W_2=\{(O_j,D_j,\nu_j,B^2_{j,\ell})\}$.
--
--   These are the data on which the proof of Theorem 3.1 (Steps (ii)–(iv)) runs.
--
--   **Formalization Note** Indices are natural numbers, with $m,\ell\ge1$ as in the paper's $\mathbb Z_+$; continuity of $q$ into $\mathcal P(\mathbb X)$ is continuity of $(x,a)\mapsto\int f\,dq(\cdot\mid x,a)$ for every bounded continuous $f$.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.1 p.21, (5.6) p.22

import Mathlib
import Definitions.Def_AvgCostLP_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace A]

/-- Yu, arXiv:1905.12095v3, Lemma 5.1, p.21: the closed sets `B¹_{j,m,ℓ}` and `B²_{j,ℓ}` have the
properties of Lemma 5.1 for the compact sets `Γ_j`, the finite measures `ν_j` and the finite sets
`F_j = proj_A(Γ_j)`: for all `j` and all `m, ℓ ≥ 1`,

1. `ν_j(X \ B¹_{j,m,ℓ}) ≤ ℓ⁻¹` and `ν_j(X \ B²_{j,ℓ}) ≤ ℓ⁻¹`;
2. restricted to `B¹_{j,m,ℓ} × F_j` the truncated cost `c^m = min{c, m}` is continuous, and
   restricted to `B²_{j,ℓ} × F_j` the kernel `q(dy | ·, ·)` is continuous.

**Formalization Note** Indices are natural numbers; `j` is shifted to start at `0` (as for `Γ_j`),
while `m, ℓ ∈ ℤ₊` are kept and the conditions are required for `m, ℓ ≥ 1`. Continuity of the
kernel into `P(X)` with the weak topology is written as continuity of `(x, a) ↦ ∫ f dq(· | x, a)`
for every bounded continuous `f`. -/
def IsLusinSets (M : Model X A) (Γs : ℕ → Set (X × A)) (ν : ℕ → Measure X)
    (B1 : ℕ → ℕ → ℕ → Set X) (B2 : ℕ → ℕ → Set X) : Prop :=
  ∀ j ℓ : ℕ, 1 ≤ ℓ →
    (IsClosed (B2 j ℓ) ∧ ν j (B2 j ℓ)ᶜ ≤ (ℓ : ℝ≥0∞)⁻¹ ∧
      ∀ f : X →ᵇ ℝ, ContinuousOn (fun p : X × A => ∫ y, f y ∂(M.q p))
        (B2 j ℓ ×ˢ (Prod.snd '' Γs j))) ∧
    ∀ m : ℕ, 1 ≤ m →
      IsClosed (B1 j m ℓ) ∧ ν j (B1 j m ℓ)ᶜ ≤ (ℓ : ℝ≥0∞)⁻¹ ∧
        ContinuousOn (fun p : X × A => min (M.c p) (m : ℝ≥0∞)) (B1 j m ℓ ×ˢ (Prod.snd '' Γs j))

/-- Yu, arXiv:1905.12095v3, (5.6), p.22: the countable family `F̂_b(X)` of indicator functions
`1_E` with `E = (O \ D) ∩ Bᶜ` for `(O, D, ν, B) ∈ W₁ ∪ W₂`, where
`W₁ = {(O_j, D_j, ν_j, B¹_{j,m,ℓ}) | j, m, ℓ}` and `W₂ = {(O_j, D_j, ν_j, B²_{j,ℓ}) | j, ℓ}`
(p.21). -/
def testIndicators (O D : ℕ → Set X) (B1 : ℕ → ℕ → ℕ → Set X) (B2 : ℕ → ℕ → Set X) :
    Set (X → ℝ) :=
  {h | ∃ j m ℓ : ℕ, 1 ≤ m ∧ 1 ≤ ℓ ∧ h = ((O j \ D j) ∩ (B1 j m ℓ)ᶜ).indicator 1} ∪
    {h | ∃ j ℓ : ℕ, 1 ≤ ℓ ∧ h = ((O j \ D j) ∩ (B2 j ℓ)ᶜ).indicator 1}

end AvgCostLP


