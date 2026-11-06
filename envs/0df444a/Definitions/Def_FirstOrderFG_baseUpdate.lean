-- Prove2me | Definitions.Def_FirstOrderFG_baseUpdate
-- name    : FirstOrderFG_baseUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:06.448751+00:00
-- url     : https://prove2.me/theorems/9ab182b7-af6b-4e11-ab91-d7b40346d637
-- title:
--   Base OMD update (line 13)
-- statement:
--   The base learner updates
--   $$
--   p_{t+1}=\operatorname*{argmin}_{p\in\mathcal P}\Big\{\langle p,\tilde\ell_t\rangle+\frac1{\eta_t}D_h(p,p_t)\Big\}.
--   $$
--
--   **Formalization Note** The argmin is a `Classical.epsilon` choice of a minimizer on $\mathcal P$; the objective is continuous and strictly convex on the compact convex set $\mathcal P$, so the minimizer exists and is unique.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 13, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Pset
import Definitions.Def_FirstOrderFG_Dent

namespace FirstOrderFG

/-- **The base OMD update (Algorithm 2, line 13).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, line 13, p.10:
`p_{t+1} = argmin_{p ∈ 𝒫} {⟨p, ℓ̃_t⟩ + (1/η_t) D_h(p, p_t)}`.

**Formalization Note.** The argmin is `Classical.epsilon` of "is a minimizer on `𝒫`"; the objective
is continuous and strictly convex on the compact convex set `𝒫`, so the minimizer exists and is
unique. `⟨p, ℓ̃⟩` is summed over `V_self`. -/
noncomputable def baseUpdate {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (η : ℝ) (p lt : Fin K → ℝ) : Fin K → ℝ :=
  Classical.epsilon fun pn => pn ∈ Pset E T ∧
    IsMinOn (fun r => ∑ i ∈ Vself E, r i * lt i + 1 / η * Dent E r p) (Pset E T) pn

end FirstOrderFG


