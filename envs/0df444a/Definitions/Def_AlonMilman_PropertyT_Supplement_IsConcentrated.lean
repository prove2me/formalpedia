-- Prove2me | Definitions.Def_AlonMilman_PropertyT_Supplement_IsConcentrated
-- name    : AlonMilman_PropertyT_Supplement_IsConcentrated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:25:24.576524+00:00
-- url     : https://prove2.me/theorems/7b3cb3bf-9b01-4405-8c50-06e014e26037
-- title:
--   Definition 1.2 — Lévy families and concentrated (Lévy) families of graphs
-- statement:
--   Let $\{G_i\}$ be a family of finite graphs, let $\rho_i$ be the diameter of $G_i$, and let $\alpha(i, \rho) = \alpha(G_i, \rho)$ be the concentration function of $G_i$ (the largest proportion of vertices at distance more than $\rho$ from a set containing at least half of the vertices).
--
--   1. A sequence $\{G_i\}_{i \ge 0}$ is a **Lévy family** if for every $\varepsilon > 0$
--   $$\lim_{i \to \infty} \alpha(i, \varepsilon \rho_i) = 0.$$
--   2. The family $\{G_i\}$ is a **concentrated (Lévy) family** if there exist constants $c > 0$ and $h > 0$ such that for every index $i$ and every radius $\rho > 0$
--   $$\alpha(i, \rho) \le c \cdot \exp\!\Big(-\Big[\frac{h \rho}{\sqrt{\rho_i}}\Big]\Big),$$
--   where $[x]$ denotes the integer part of $x$.
--
--   The constants $c, h$ do not depend on $i$ or on $\rho$. A concentrated family is a Lévy family in a strong quantitative sense: half of the vertices, enlarged by a multiple of $\sqrt{\rho_i}$, already cover all but an exponentially small proportion of the graph. Theorems 3.2 and 3.4 of the paper give examples.
--
--   **Formalization Note** The page says "there exist constants $c, h$"; they are taken positive, since with $h \le 0$ the bound would hold for every family. The diameter is Mathlib's `SimpleGraph.diam`, which is $0$ for a one-vertex graph and for a disconnected graph. For a disconnected graph the page's diameter is $\infty$ and $h\rho/\sqrt{\infty} = 0$, which agrees with Lean's $h\rho/\sqrt 0 = 0$; for a one-vertex graph $\alpha = 0$ and the bound holds for any $c > 0$. The integer part is `Nat.floor` of a nonnegative number. A concentrated family may be indexed by any type; a Lévy family is a sequence indexed by $\mathbb N$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 74, Definition 1.2

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_Supplement_concentrationFun

namespace AlonMilman.PropertyT.Supplement

/-- A family `{G_i}` of finite simple graphs is a **concentrated (Lévy) family** (Alon–Milman
1985, Definition 1.2, p. 74) if there are constants `c > 0`, `h > 0` such that for every index
`i` and every radius `ρ > 0`
`α(G_i, ρ) ≤ c · exp(−[h ρ / √ρ_i])`,
where `ρ_i = diam G_i` and `[x]` is the integer part. `SimpleGraph.diam` is `0` for a graph with
one vertex and for a disconnected graph (whose diameter is `∞` on the page); in both cases the
quotient `h ρ / √ρ_i` is `0` in Lean, as `hρ/√∞ = 0` is on the page for a disconnected graph. -/
def IsConcentrated {ι : Type} (V : ι → Type) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, SimpleGraph (V i)) : Prop :=
  ∃ c h : ℝ, 0 < c ∧ 0 < h ∧ ∀ i, ∀ ρ : ℝ, 0 < ρ →
    concentrationFun (G i) ρ ≤
      c * Real.exp (-(⌊h * ρ / Real.sqrt ((G i).diam : ℝ)⌋₊ : ℝ))

/-- A sequence `{G_i}` of finite simple graphs is a **Lévy family** (Alon–Milman 1985,
Definition 1.2, p. 74) if for every `ε > 0`, `α(G_i, ε ρ_i) → 0` as `i → ∞`, where
`ρ_i = diam G_i`. -/
def IsLevyFamily (V : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, SimpleGraph (V i)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto (fun i => concentrationFun (G i) (ε * ((G i).diam : ℝ))) Filter.atTop
      (nhds 0)

end AlonMilman.PropertyT.Supplement


