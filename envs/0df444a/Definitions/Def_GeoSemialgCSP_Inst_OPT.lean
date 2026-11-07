-- Prove2me | Definitions.Def_GeoSemialgCSP_Inst_OPT
-- name    : GeoSemialgCSP_Inst_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:34.386494+00:00
-- url     : https://prove2.me/theorems/2d97a885-764c-4c6e-a4ed-2278b6a12fde
-- title:
--   Optimum of an instance
-- statement:
--   The **optimum** of an instance $I$ over the domain $X\subseteq\mathbb R^d$ is
--   $$\mathrm{OPT}(I_P)=\sup_{\phi:[n]\to X}\mathrm{val}(\phi,I_P).$$
--
--   **Formalization Note** The value takes finitely many values in $[0,1]$, so the supremum is attained when $X\neq\emptyset$ or $n=0$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_Inst
import Definitions.Def_GeoSemialgCSP_Inst_val

namespace GeoSemialgCSP

/-- **Optimum of an instance.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, printed p.7 (PDF p.8):
`OPT(I_P) = sup_{ϕ : [n] → X} val(ϕ, I_P)`.

**Formalization Note.** `val` takes finitely many values in `[0,1]`, so for nonempty `X` (or
`n = 0`) the supremum is attained; for `X = ∅` and `n ≥ 1` it is `sSup ∅ = 0`. -/
noncomputable def Inst.OPT {k d : ℕ} (X : Set (E d)) (S : Set (Fin k → E d)) (I : Inst k) : ℝ :=
  sSup {v : ℝ | ∃ ϕ : Fin I.n → E d, (∀ i, ϕ i ∈ X) ∧ v = I.val S ϕ}

end GeoSemialgCSP


