-- Prove2me | Definitions.Def_FirstOrderFG_masterUpdate
-- name    : FirstOrderFG_masterUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:48:59.922157+00:00
-- url     : https://prove2.me/theorems/6746486f-51c5-4e80-916b-b5d43cf82a2a
-- title:
--   Master OMD update (line 14)
-- statement:
--   The master updates
--   $$
--   x_{t+1}=\operatorname*{argmin}_{x\in\mathcal X}\big\{\langle x,\tilde g_t\rangle+D_{\Psi_t}(x,x_t)\big\},
--   $$
--   with $\Psi_t$ the hybrid regularizer (25).
--
--   **Formalization Note** The argmin is a `Classical.epsilon` choice of a minimizer on $\mathcal X$; it exists and is unique.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 14, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Xset
import Definitions.Def_FirstOrderFG_binner
import Definitions.Def_FirstOrderFG_DPsi

namespace FirstOrderFG

/-- **The master OMD update (Algorithm 2, line 14).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, line 14, p.10:
`x_{t+1} = argmin_{x ∈ 𝒳} {⟨x, g̃_t⟩ + D_{Ψ_t}(x, x_t)}`, with `Ψ_t` of Eq. (25).

**Formalization Note.** The argmin is `Classical.epsilon` of "is a minimizer on `𝒳`"; the objective
is continuous and strictly convex on the compact convex set `𝒳`, so the minimizer exists and is
unique. `θ0 = θ_{t,0}` and `θ` are the rates in `Ψ_t`. -/
noncomputable def masterUpdate {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (θ0 θ : ℝ) (x g : Option (Fin K) → ℝ) :
    Option (Fin K) → ℝ :=
  Classical.epsilon fun xn => xn ∈ Xset E T ∧
    IsMinOn (fun y => binner E y g + DPsi E θ0 θ y x) (Xset E T) xn

end FirstOrderFG


