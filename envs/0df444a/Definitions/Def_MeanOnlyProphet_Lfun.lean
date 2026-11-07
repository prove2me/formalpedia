-- Prove2me | Definitions.Def_MeanOnlyProphet_Lfun
-- name    : MeanOnlyProphet_Lfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:54.284196+00:00
-- url     : https://prove2.me/theorems/c058267b-0a79-400b-95e3-42e9458dfb57
-- title:
--   The asymptotic lower bound $L(b,q)=C(q)A(0)+\int_0^1 b\,T_\infty$
-- statement:
--   For a drop rate $b$ with threshold $\theta(t)=\int_t^1 b$ and an acceptance rate $q$, let
--   $$
--   C(q)=1-\theta(0)+\int_0^1 b(t)\,e^{-q(t)}\,dt,\qquad
--   L(b,q)=C(q)\cdot A(0)+\int_0^1 b(t)\,T_\infty(t)\,dt .
--   $$
--   Since $\theta(0)=\int_0^1 b$, this equals $L=\theta(0)+(1-\theta(0))A(0)-\int_0^1 b(t)\,k(t)\,dt$. It lower-bounds $\mathbb E[\mathrm{ALG}]$ as $n\to\infty$ when $\mathbb E[X^*]=1$, and the paper's threshold is chosen to make $\inf_q L(b,q)$ large.
--
--   **Formalization Note** The rate is $[0,\infty]$-valued with $e^{-\infty}=0$; a real rate enters as `toRate q`.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §3.1, p.7 (PDF p.8); App. A.2, pp.29–30 (PDF pp.30–31)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Tinf
import Definitions.Def_MeanOnlyProphet_thetaOf

namespace MeanOnlyProphet

/-- **`C(q) = 1 − θ(0) + ∫_0^1 b(t) · e^{−q(t)} dt`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.2, p.29 (PDF p.30): "Define
C(r) = 1 − θ(0) + ∫_0^1 b(t) · e^{−r(t)} dt."

**Formalization Note.** `θ = thetaOf b`; the rate is `ℝ≥0∞`-valued with `e^{−∞} = 0` (`eNeg`). -/
noncomputable def Cfun (b : ℝ → ℝ) (q : ℝ → ENNReal) : ℝ :=
  1 - thetaOf b 0 + ∫ t in (0 : ℝ)..1, b t * eNeg (q t)

/-- **The asymptotic lower bound `L(b, q) = C(q) · A(0) + ∫_0^1 b(t) · T∞(t) dt`.** Feng, Jin, Wu,
Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.2,
p.30 (PDF p.31): "Using θ(0) = ∫_0^1 b(t) dt, we can rewrite L as L(b, q) := C(q) · A(0) + ∫_0^1 b(t) ·
T∞(t) dt." This equals `L = θ(0) + (1 − θ(0)) · A(0) − ∫_0^1 b(t) · k(t) dt` of §3.1, p.7.

**Formalization Note.** Rates are `ℝ≥0∞`-valued with the conventions of Lemma A.4 (`e^{−∞} = 0`,
`q · A = 0` at `q = +∞`); a real rate `q` enters as `toRate q`. -/
noncomputable def Lfun (b : ℝ → ℝ) (q : ℝ → ENNReal) : ℝ :=
  Cfun b q * areaA q 0 + ∫ t in (0 : ℝ)..1, b t * Tinf q t

end MeanOnlyProphet


