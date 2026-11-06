-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_init
-- name    : FirstOrderFG_Alg2_init
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:21.10434+00:00
-- url     : https://prove2.me/theorems/298935ce-7c41-45c8-b4d4-432b3a1e6e5c
-- title:
--   Initialization of Algorithm 2
-- statement:
--   An instance with inputs $(G,T,A,\theta)$ starts with $p_1$ uniform on $V_{\mathrm{self}}$, $\theta_{1,0}=\theta$, $\rho_1=2$, an empty sum in $\eta$, and
--   $$
--   x_{1,0}=\frac{M+1}{2M},\quad x_{1,i}=\frac1{2M}\ (i\in\bar V_{\mathrm{self}})\quad\text{if }0\in\mathcal B;\qquad x_1\ \text{uniform on }\mathcal B\ \text{otherwise}.
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, lines 1–3, p.10, and last paragraph of p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_State
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Bset

namespace FirstOrderFG

/-- **Initialization of an instance of Algorithm 2 with `(G, T, A, θ)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2,
lines 1 and 3, p.10, and the last paragraph of p.10: "Initialize `p₁` uniformly on `V_self`,
`x_{1,0} = (M + 1)/(2M)`, `x_{1,i} = 1/(2M)` for `i ∈ V̄_self`, and `θ_{1,0} = θ`"; "When `0 ∈ B`,
we initialize `x_{1,0} = (M+1)/(2M)` and `x_{1,i} = 1/(2M)` for `i ∈ V̄_self`; otherwise, we initialize
`x₁` uniformly on `B`"; `ρ₁ = 2`. The sum of line 5 starts empty.

**Formalization Note.** `p₁` and `x₁` vanish off `V_self` and off `B`. -/
noncomputable def Alg2.init {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (A θ : ℝ) : Alg2.State K where
  A := A
  θ := θ
  p := fun i => if i ∈ Vself E then 1 / ((Vself E).card : ℝ) else 0
  x := fun b => if b ∈ Bset E then
      (if (Vself E).Nonempty then
        (if b = none then (((Bset E).card : ℝ) + 1) / (2 * ((Bset E).card : ℝ))
          else 1 / (2 * ((Bset E).card : ℝ)))
      else 1 / ((Bset E).card : ℝ))
    else 0
  θ0 := θ
  ρ := 2
  gsum := 0
  n := 0

end FirstOrderFG


