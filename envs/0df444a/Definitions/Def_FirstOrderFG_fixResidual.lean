-- Prove2me | Definitions.Def_FirstOrderFG_fixResidual
-- name    : FirstOrderFG_fixResidual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:57.66719+00:00
-- url     : https://prove2.me/theorems/95f7fb9b-deee-4f3f-b3c6-b949991ea80f
-- title:
--   Fixed-point residual $\|q-F_{p,\gamma}(q)\|_1$
-- statement:
--   The residual of $q$ for the map $F_{p,\gamma}$ is the $\ell_1$ distance
--   $$
--   \|q-F_{p,\gamma}(q)\|_1=\sum_{i\in V_{\mathrm{self}}}\big|q_i-[F_{p,\gamma}(q)]_i\big| .
--   $$
--   A distribution is an **$\varepsilon$-fixed point** when its residual is at most $\varepsilon$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Proposition A.3, p.20

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Fmap

namespace FirstOrderFG

/-- **The fixed-point residual `‖q − F_{p,γ}(q)‖₁`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3 ("a distribution `q` is an
`ε`-fixed point of a map `F` if `‖q − F(q)‖₁ ≤ ε`") and Proposition A.3, p.20.

**Formalization Note.** The `ℓ₁` norm is taken over the coordinates in `V_self`, the support of
distributions on `V_self`. -/
noncomputable def fixResidual {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ)
    (p : Fin K → ℝ) (γ : ℝ) (q : Fin K → ℝ) : ℝ :=
  ∑ i ∈ Vself E, |q i - Fmap E T p γ q i|

end FirstOrderFG


