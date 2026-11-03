-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_path
-- name    : EnvelopeMSLP_MSLP_path
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:02.802907+00:00
-- url     : https://prove2.me/theorems/22f1d97c-160c-4785-bc57-9a21c650e9b6
-- title:
--   The sequence $x_0,x_1,\dots,x_T$ of a scenario
-- statement:
--   For a start vector $a$, a policy $x$ and a scenario $\omega$, the sequence $a,x_1(\omega),\dots,x_T(\omega)$. It supplies the previous decision $x_{t-1}$ of each stage, and $a$ at the first stage.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (7), p.11

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_Policy

namespace EnvelopeMSLP

/-- **The sequence `x₀, x_1(ω), …, x_T(ω)` of a scenario.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (7), p.11. For stage `t : Fin T`
the previous decision is `P.path a x ω t.castSucc`; the first entry is the initial vector `a`. -/
def MSLP.path {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (a : Fin (P.n 0) → ℝ) (x : P.Policy) (ω : Ω) :
    (i : Fin (T + 1)) → Fin (P.n i) → ℝ :=
  fun i => Fin.cases (motive := fun i => Fin (P.n i) → ℝ) a (fun s => x s ω) i

end EnvelopeMSLP


