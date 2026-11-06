-- Prove2me | Definitions.Def_FirstOrderFG_logSpread
-- name    : FirstOrderFG_logSpread
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:48:45.96292+00:00
-- url     : https://prove2.me/theorems/0a134892-d67c-449f-afa0-eabbf3f4abb2
-- title:
--   Spread $D_n$ of the log coordinate ratios
-- statement:
--   For the Picard iterates $q^{(n)}$ of $F_{p,\gamma}$,
--   $$
--   D_n=\max_{i\in V_{\mathrm{self}}}\ln\frac{q^{(n+1)}_i}{q^{(n)}_i}-\min_{i\in V_{\mathrm{self}}}\ln\frac{q^{(n+1)}_i}{q^{(n)}_i},
--   $$
--   the spread of the log ratios between consecutive iterates. It controls the residual and contracts geometrically.
--
--   **Formalization Note** Set to $0$ when $V_{\mathrm{self}}=\emptyset$; every statement using it assumes $V_{\mathrm{self}}\ne\emptyset$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, proof of Proposition A.3, p.20

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_picardIter

namespace FirstOrderFG

/-- **The spread `D_n` of the log coordinate ratios.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, proof of Proposition A.3, p.20:
`D_n ≜ max_{i ∈ V_self} ln(q_i^{(n+1)}/q_i^{(n)}) − min_{i ∈ V_self} ln(q_i^{(n+1)}/q_i^{(n)})`.

**Formalization Note.** Defined as `0` when `V_self` is empty (the paper's maximum is then
undefined); every statement using it assumes `V_self` nonempty. -/
noncomputable def logSpread {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ)
    (p : Fin K → ℝ) (γ : ℝ) (q0 : Fin K → ℝ) (n : ℕ) : ℝ :=
  if h : (Vself E).Nonempty then
    (Vself E).sup' h (fun i => Real.log (picardIter E T p γ q0 (n + 1) i / picardIter E T p γ q0 n i))
      - (Vself E).inf' h (fun i => Real.log (picardIter E T p γ q0 (n + 1) i / picardIter E T p γ q0 n i))
  else 0

end FirstOrderFG


