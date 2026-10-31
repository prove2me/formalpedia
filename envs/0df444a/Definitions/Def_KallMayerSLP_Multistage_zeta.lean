-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_zeta
-- name    : KallMayerSLP_Multistage_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:05.623254+00:00
-- url     : https://prove2.me/theorems/db4a2e41-816b-4093-98b2-4e702e3dd33d
-- title:
--   The state variable $\zeta_t=(\xi_2,\dots,\xi_t)$
-- statement:
--   Given random vectors $\xi_t:\Omega\to\mathbb R^{r_t}$, the state variable of stage $t$ is $\zeta_t(\omega)=(\xi_2(\omega),\dots,\xi_t(\omega))$. Decisions of stage $t$ are functions of $\zeta_t$, which expresses nonanticipativity.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, §3, (3.1), p.248 (PDF 257)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Hist

namespace KallMayerSLP.Multistage

/-- The state variable `ζ_t = (ξ_2, …, ξ_t)` of stage `t` (Kall & Mayer, *Stochastic Linear
Programming* (2005), Chapter 3, (3.1), p.248, PDF 257). -/
def zeta {Ω : Type*} {r : ℕ → ℕ} (ξ : ∀ t, Ω → Fin (r t) → ℝ) (t : ℕ) (ω : Ω) : Hist r t :=
  fun s => ξ s ω

end KallMayerSLP.Multistage


