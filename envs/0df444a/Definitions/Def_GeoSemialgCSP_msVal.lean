-- Prove2me | Definitions.Def_GeoSemialgCSP_msVal
-- name    : GeoSemialgCSP_msVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:46.938141+00:00
-- url     : https://prove2.me/theorems/0ab3d747-7e70-44d2-a805-17c75e427794
-- title:
--   Value of a labelling on the multiscale instance
-- statement:
--   For a payoff $f:[q]^k\to\mathbb R$ and a labelling $\phi$ of the leaves of $T_m$ by $[q]$,
--   $$\mathrm{val}(\phi,\tilde I_f)=\mathbb E_{(a_1,\dots,a_k)\sim\tilde I}\,f(\phi(a_1),\dots,\phi(a_k)).$$
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.7 (PDF p.8); §4.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_GeoSemialgCSP_msWeight

namespace GeoSemialgCSP

/-- **Value of a labelling on `Ĩ_f`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, printed p.7 (PDF p.8), and §4.1,
printed p.10 (PDF p.11): `val(ϕ, Ĩ_f) = E_{(a₁,…,a_k) ∼ Ĩ} f(ϕ(a₁), …, ϕ(a_k))` for
`ϕ : [m] → [q]`. -/
noncomputable def msVal {k q h : ℕ} (f : (Fin k → Fin q) → ℝ) (ϕ : (Fin h → Fin k) → Fin q) : ℝ :=
  ∑ l : Fin k → (Fin h → Fin k), msWeight h l * f (ϕ ∘ l)

end GeoSemialgCSP


