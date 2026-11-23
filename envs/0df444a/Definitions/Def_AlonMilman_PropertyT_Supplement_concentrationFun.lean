-- Prove2me | Definitions.Def_AlonMilman_PropertyT_Supplement_concentrationFun
-- name    : AlonMilman_PropertyT_Supplement_concentrationFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:24:51.174572+00:00
-- url     : https://prove2.me/theorems/da7192b9-fdcf-4e6f-8aae-0d4b2f12da7f
-- title:
--   Definition 1.2 — the metric enlargement $A_\rho$ and the concentration function $\alpha(G,\rho)$ of a finite graph
-- statement:
--   Let $G = (V, E)$ be a finite graph on $n = |V|$ vertices, with graph distance $\rho(u, v)$ (the length of a shortest path; $+\infty$ between different connected components). For $A \subseteq V$ write $\mu(A) = |A|/n$ for the normalized counting measure and $\rho(v, A) = \min_{a \in A} \rho(v, a)$.
--
--   For a set $A \subseteq V$ and a radius $\rho$, the **metric enlargement** of $A$ is
--
--   $$A_\rho = \{\, v \in V : \rho(v, A) \le \rho \,\}.$$
--
--   The **concentration function** of $G$ is defined by
--
--   $$1 - \alpha(G, \rho) = \min\{\, \mu(A_\rho) : A \subseteq V,\ \mu(A) \ge \tfrac12 \,\},$$
--
--   that is, $\alpha(G, \rho)$ is the largest proportion of vertices that can lie at distance more than $\rho$ from a set containing at least half of the vertices.
--
--   For a family $\{G_i\}$ Alon and Milman write $\alpha(i, \rho)$ for $\alpha(G_i, \rho)$; small values of $\alpha$ for moderate $\rho$ express that the uniform measure on $V$ is concentrated around every set of half measure. This function is the input of the definitions of Lévy and concentrated families.
--
--   **Formalization Note** The minimum ranges over all $A \subseteq V$ with $2|A| \ge n$ (the page's $A \subset V$ is read as $A \subseteq V$; including $A = V$ does not change the minimum). The graph is a `SimpleGraph` on a finite type. For the graph with no vertices the measure $\mu$ is undefined and the convention $\alpha = 0$ is used.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 74, Definition 1.2

import Mathlib

namespace AlonMilman.PropertyT.Supplement

open Classical in
/-- The metric enlargement `A_ρ = {v ∈ V : ρ(v, A) ≤ ρ}` of a vertex set `A` in a finite simple
graph `G` (Alon–Milman 1985, Definition 1.2, p. 74): the vertices joined to some `a ∈ A` by a
path of length at most `ρ`. Vertices in other connected components than every point of `A` are at
infinite distance and are not in `A_ρ`. -/
noncomputable def enlargement {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) (ρ : ℝ) : Finset V :=
  Finset.univ.filter (fun v => ∃ a ∈ A, G.Reachable a v ∧ (G.dist a v : ℝ) ≤ ρ)

open Classical in
/-- The concentration function `α(G, ρ)` of a finite simple graph `G` on `n = |V|` vertices
(Alon–Milman 1985, Definition 1.2, p. 74):
`1 − α(G, ρ) = min { |A_ρ| / n : A ⊆ V, |A| / n ≥ 1/2 }`, i.e.
`α(G, ρ) = max { 1 − |A_ρ| / n : A ⊆ V, 2|A| ≥ n }`.
The maximum is over a nonempty finite family (it contains `A = V`).
Convention: `α = 0` for the graph with no vertices, where the normalised counting measure is
undefined. -/
noncomputable def concentrationFun {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (ρ : ℝ) : ℝ :=
  if Fintype.card V = 0 then 0
  else
    ((Finset.univ : Finset (Finset V)).filter
        (fun A => (Fintype.card V : ℝ) ≤ 2 * (A.card : ℝ))).sup'
      ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, by
        rw [Finset.card_univ]
        have : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
        linarith⟩⟩
      (fun A => 1 - ((enlargement G A ρ).card : ℝ) / (Fintype.card V : ℝ))

end AlonMilman.PropertyT.Supplement


