-- Prove2me | Definitions.Def_BilateralOptRegret_Oracle
-- name    : BilateralOptRegret_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:28.421913+00:00
-- url     : https://prove2.me/theorems/903338d1-a5c9-4e52-bba4-41792226bd82
-- title:
--   Definition 4.1 — the $(c_1,c_2,A)$-refinement oracle
-- statement:
--   Fix $K$, $c_1,c_2>0$ and a positive function $A(K,\delta)$. A procedure Refine is a **$(c_1,c_2,A)$-refinement oracle** if, for every $\varepsilon\in(0,1]$, $\delta\in(0,1)$ and every input $(G,\hat F,\varepsilon,\delta)$ with
--   $$\{x\in\mathcal X_K:\mathrm{gap}(x)\le c_1\varepsilon\}\subseteq G\subseteq\mathcal X_K,\qquad \max_{x\in G}|\hat F(x)-F(x)|\le\varepsilon,$$
--   with probability at least $1-\delta$ it returns $(G',\hat F')$ satisfying the same conditions with precision $\varepsilon'=\varepsilon/8$; and on the same event it uses at most
--   $$A(K,\delta)\big(\varepsilon'^{-3}+K\varepsilon'^{-2}\big)$$
--   observations, each at an action with $\mathrm{gap}(x)\le c_2\varepsilon$.
--
--   This interface separates the regret analysis of Algorithm 1 from the construction of the refinement procedure.
--
--   **Formalization Note** One program serves all laws: the guarantee is quantified over $L$ after the program. The pair of conditions is the predicate `Invariant`, and conditions (15), (16) of p.26 are `Invariant` with $c=128\,\ell_K$. The estimates are a function on all of $\mathcal X_K$; their values off $G$ are unconstrained.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Definition 4.1, p.15

import Mathlib
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-! # The refinement oracle (Definition 4.1)

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…), Definition 4.1, p.15.

**Formalization Note.** A procedure `Refine` takes `(G, F̂, ε, δ)` and is one program for all laws: it
cannot read `L`. `G ⊆ X_K` is by type. `F̂` is a function on all of `X_K`, whose values off `G` are not
constrained by the input conditions; the guarantee is for every such function. The output
conditions, the count (4) and the gap of the queries hold on one event (`succProb`). `Invariant` is
the pair of conditions of Definition 4.1; (15) and (16), p.26, are `Invariant L K (128 * ℓ_K) ε`. -/

/-- A refinement procedure on the grid of size `2^n + 1`: from `(G, F̂, ε, δ)` to `(G′, F̂′)`. -/
abbrev RefineProc (n : ℕ) : Type :=
  Finset (Act n) → (Act n → ℝ) → ℝ → ℝ → QTree (Act n) (Finset (Act n) × (Act n → ℝ))

/-- The input conditions of Definition 4.1 at constant `c` and precision `ε`:
`{x ∈ X_K : gap(x) ≤ c ε} ⊆ G` and `max_{x ∈ G} |F̂(x) − F(x)| ≤ ε`. -/
def Invariant (L : Measure (ℝ × ℝ)) (K : ℕ) (c ε : ℝ) (G : Finset (Grid K))
    (Fhat : Grid K → ℝ) : Prop :=
  (∀ q : Grid K, gap L K q ≤ c * ε → q ∈ G) ∧ ∀ q ∈ G, |Fhat q - F L (pt K q)| ≤ ε

/-- **Definition 4.1, p.15.** `Refine` is a `(c₁, c₂, A)`-refinement oracle at `K = 2^n + 1`: for every
law, every `ε ∈ (0, 1]`, `δ ∈ (0, 1)` and input satisfying the conditions at `(c₁, ε)`, with probability
at least `1 − δ` the output satisfies them at `(c₁, ε′)`, `ε′ = ε/8`; and on the same event it uses at
most `A(K, δ) (ε′⁻³ + K ε′⁻²)` observations (4), each at an action with `gap(x) ≤ c₂ ε`. -/
def IsRefinementOracle (n : ℕ) (c₁ c₂ : ℝ) (A : ℕ → ℝ → ℝ) (Refine : RefineProc n) : Prop :=
  ∀ L : Measure (ℝ × ℝ), IsValLaw L → ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
    ∀ (G : Finset (Act n)) (Fhat : Act n → ℝ), Invariant L (Kof n) c₁ ε G Fhat →
      ENNReal.ofReal (1 - δ) ≤
        succProb L (Kof n) (Refine G Fhat ε δ) (fun o =>
          Invariant L (Kof n) c₁ (ε / 8) o.1.1 o.1.2 ∧
          (o.2.length : ℝ) ≤
            A (Kof n) δ * ((ε / 8) ^ (-3 : ℤ) + (Kof n : ℝ) * (ε / 8) ^ (-2 : ℤ)) ∧
          ∀ q ∈ o.2, gap L (Kof n) q ≤ c₂ * ε)

end BilateralOptRegret


