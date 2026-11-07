-- Prove2me | Definitions.Def_MeanOnlyProphet_Jn
-- name    : MeanOnlyProphet_Jn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:43.287272+00:00
-- url     : https://prove2.me/theorems/0e613f27-89d6-48ca-affc-5e8b7a29271d
-- title:
--   The finite-$n$ lower bound $J_n(b,q)=C(q)A_P(0)+\int_0^1 b\,T_n$
-- statement:
--   For $n\ge1$, a drop rate $b$ and a rate $q$,
--   $$
--   J_n(b,q)=C(q)\cdot A_P(0)+\int_0^1 b(t)\,T_n(t)\,dt,\qquad C(q)=1-\theta(0)+\int_0^1 b(t)\,e^{-q(t)}\,dt .
--   $$
--   With the input rate $q=r$ it lower-bounds the expected reward of the randomly shifted rule at finite $n$, and $J_n(b,q)-L(b,q)=C(q)\,\mathcal E-\int_0^1 b\,D_n$.
--
--   **Formalization Note** The rate is $[0,\infty]$-valued with $e^{-\infty}=0$.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), App. A.2, pp.29–30 (PDF pp.30–31)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Lfun
import Definitions.Def_MeanOnlyProphet_Tn

namespace MeanOnlyProphet

/-- **The finite-`n` lower bound `J_n(b, q) = C(q) · A_P(0) + ∫_0^1 b(t) · T_n(t) dt`.** Feng, Jin, Wu,
Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.2,
p.29 (PDF p.30): "E[ALG] ≥ Jn(b, r) := C(r) · AP(0) + ∫_0^1 b(t) · Tn(t) dt."

**Formalization Note.** Rates are `ℝ≥0∞`-valued with `e^{−∞} = 0`. -/
noncomputable def Jn (n : ℕ) (b : ℝ → ℝ) (q : ℝ → ENNReal) : ℝ :=
  Cfun b q * AP n q 0 + ∫ t in (0 : ℝ)..1, b t * Tn n q t

end MeanOnlyProphet


