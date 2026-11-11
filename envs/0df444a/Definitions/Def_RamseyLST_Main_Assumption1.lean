-- Prove2me | Definitions.Def_RamseyLST_Main_Assumption1
-- name    : RamseyLST_Main_Assumption1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:00.7545+00:00
-- url     : https://prove2.me/theorems/18bc25fb-a18e-4386-8d96-5058cac5126b
-- title:
--   Assumption 1 — the properties required of the bounded-aspect-ratio subroutine
-- statement:
--   Let $\alpha_0\ge1$, $C_D\ge1$, and let $\psi:[1,\infty)\to[0,1]$ be non-increasing. A subroutine **satisfies Assumption 1** with parameters $\alpha_0,C_D,\psi$ (p. 18) if for every connected weighted graph $\tilde G$, every candidate core $\tilde Z^{in}\subseteq V(\tilde G)$ and every weight function $\tilde w:\tilde Z^{in}\to\mathbb R_{\ge0}$ its output is a weighted
--
--   $$\big(\alpha_0,\ \psi(\Phi_{\tilde G}(\tilde Z^{in})),\ C_D\big)\text{-Ramsey spanning tree of }\tilde G\text{ with respect to }\tilde w.$$
--
--   It satisfies the assumption **strongly** if all these trees are strong. For a class $\mathcal Y$ of metric spaces, it satisfies the assumption **on $\mathcal Y$** if this is required only for inputs with $(\tilde Z^{in},d_{\tilde G})\in\mathcal Y$.
--
--   The predicate here states this for a subroutine given abstractly. For every admissible input there exist a spanning tree and a core with these properties, and the inputs are restricted to non-empty candidate cores. A strong flag selects the strong stretch bound, and a class $\mathcal Y$ restricts the inputs; taking $\mathcal Y$ to be the class of all spaces gives the unrestricted assumption.
--
--   This is the hypothesis of Corollary 10.
--
--   **Formalization Note** Graphs $\tilde G$ range over finite types with an `ARTreeCover.WGraph`, assumed connected. The space $(\tilde Z^{in},d_{\tilde G})$ is the subtype of the finset $\tilde Z^{in}$ with the real distance `rdist`. A deterministic subroutine is a function, and "every input has an output with the properties" is equivalent to its existence by choice. Quantifying only over non-empty candidate cores weakens the assumption; the reduction never calls the subroutine on an empty core.
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 18 (PDF 22), Assumption 1

import Mathlib
import Definitions.Def_RamseyLST_Main_FiniteMetric
import Definitions.Def_RamseyLST_Main_RamseySpanningTree

namespace RamseyLST.Main

open ARTreeCover

/-- Assumption 1 (p. 18), for a subroutine given as a `∀ input, ∃ output` statement:
the parameters satisfy `α₀ ≥ 1`, `C_D ≥ 1`, and `ψ : [1, ∞) → [0, 1]` is non-increasing; and for
every finite connected weighted graph `G̃`, every **non-empty** candidate core `Z̃ ⊆ V(G̃)` whose
metric space `(Z̃, d_{G̃})` belongs to the class `𝒴`, and every weight function `w̃ : Z̃ → ℝ_{≥0}`,
there are a spanning tree `T̃` of `G̃` and a core `Z` such that `(T̃, Z)` is a weighted
(strong, if `strong = true`) `(α₀, ψ(Φ_{G̃}(Z̃)), C_D)`-Ramsey spanning tree of `G̃` with respect to
`w̃`. Taking `𝒴` to hold for every space gives the unrestricted assumption; taking `𝒴 = 𝒳(θ)`
gives "the assumption on `𝒳(θ)`". -/
def Assumption1 (strong : Bool) (𝒴 : MetricClass) (α₀ CD : ℝ) (ψ : ℝ → ℝ) : Prop :=
  1 ≤ α₀ ∧ 1 ≤ CD ∧ (∀ Φ : ℝ, 1 ≤ Φ → 0 ≤ ψ Φ ∧ ψ Φ ≤ 1) ∧ AntitoneOn ψ (Set.Ici 1) ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V), G.graph.Connected →
      ∀ Zin : Finset V, Zin.Nonempty → 𝒴 Zin (fun a b => rdist G a b) →
        ∀ w : V → ℝ, (∀ z ∈ Zin, 0 ≤ w z) →
          ∃ (T : SpanningTree G) (Z : Finset V),
            IsWeightedRamseySpanningTree strong G T Zin w Z α₀ (ψ (aspectRatio (rdist G) Zin)) ∧
              DiamStretchLe G T CD

end RamseyLST.Main


