-- Prove2me | Definitions.Def_MaxEntOCRS_acceptProb
-- name    : MaxEntOCRS_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:15.809996+00:00
-- url     : https://prove2.me/theorems/eff2a56f-77d0-4eec-8617-fa70f3cabfc8
-- title:
--   Acceptance probability $\theta_e/x_e$ of the simulate-then-replace scheme
-- statement:
--   In the simulate-then-replace scheme, an arriving edge $e$ that is active and addable is added with probability $\theta_e/x_e$. Here
--   $$
--   \frac{\Pr_\mu(e \in M)}{x_e \Pr_\mu[\mathrm{Add}(e)]},
--   $$
--   which for the Gibbs measure $\mu^*$ with activities $t$ equals $\theta_e/x_e$ with $\theta_e = t_e/(1+t_e)$, since $\Pr_{\mu^*}(e \in M) = \theta_e \Pr_{\mu^*}[\mathrm{Add}(e)]$.
--
--   **Formalization Note** The form above is used so that the scheme is defined for any initial distribution, in particular for the entropy maximizer before it is identified as a Gibbs measure.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_edgeMarginal
import Definitions.Def_MaxEntOCRS_addProb

namespace MaxEntOCRS

/-- The acceptance probability `θ_e/x_e` of the simulate-then-replace scheme (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4:
"if e is active and addable it adds e with probability θe/xe").

**Formalization Note** Written as `Pr_μ(e ∈ M) / (x_e · Pr_μ[Add(e)])`. For the Gibbs measure
`μ*` with activities `t` this is `θ_e/x_e`, `θ_e = t_e/(1 + t_e)`, because
`Pr_μ*(e ∈ M) = θ_e Pr_μ*[Add(e)]` (p.4); the form above is defined for any `μ`, in particular
for the entropy maximizer of Theorem 1 before it is identified as a Gibbs measure. -/
noncomputable def acceptProb {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (μ : Finset E → ℝ) (e : E) : ℝ :=
  edgeMarginal μ e / (x e * addProb G μ e)

end MaxEntOCRS


