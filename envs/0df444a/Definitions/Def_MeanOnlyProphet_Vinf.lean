-- Prove2me | Definitions.Def_MeanOnlyProphet_Vinf
-- name    : MeanOnlyProphet_Vinf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:59.32305+00:00
-- url     : https://prove2.me/theorems/53705efe-90fe-4cda-b91b-7c4461f8f2ef
-- title:
--   The value function $V_t(y,x)=\inf_q V_t(y,x,q)$
-- statement:
--   Let $b$ be a drop rate with threshold $\theta(t)=\int_t^1 b$ and let $c=\max_{0\le s\le1}\{b(s)+\theta(s)\}-1$. For a rate $q$ put $S_t(s)=\exp(-\int_t^s q)$ and $A_t(s)=\int_s^1 S_t$. For $0\le y\le1$ and $x\ge0$,
--   $$
--   V_t(y,x,q)=(c\,x+y(1-\theta(t)))\,A_t(t)-y\int_t^1 b(s)\big(S_t(s)-q(s)A_t(s)\big)\,ds+\big(1-y+t\,y+y\,A_t(t)\big)\int_t^1 b(s)\,e^{-q(s)}\,ds ,
--   $$
--   and $V_t(y,x)=\inf_q V_t(y,x,q)$, the infimum over bounded nonnegative rates that are nondecreasing on each interval $[k/N_t,(k+1)/N_t)$ of a partition of $[0,1]$ into $N_t$ equal pieces. The function $V_t$ records the worst-case contribution of the unknown rate on $[t,1]$, with $L\ge\theta(0)+V_0(1,0)$.
--
--   **Formalization Note** $c$ is a parameter (statements pin it to the maximum). The infimum is a real infimum over a nonempty class ($q=0$); on $0\le y\le1$, $x\ge0$ it is bounded below by $-y\,\theta(t)$.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), App. A.1, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_MeanOnlyProphet_thetaOf

namespace MeanOnlyProphet

/-- **`S_t(s) = exp(−∫_t^s q(u) du)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*,
arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.1, p.24 (PDF p.25). Real (bounded) rates. -/
noncomputable def survFrom (q : ℝ → ℝ) (t s : ℝ) : ℝ :=
  Real.exp (-∫ u in t..s, q u)

/-- **`A_t(s) = ∫_s^1 S_t(u) du`.** Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), App. A.1,
p.24 (PDF p.25). -/
noncomputable def areaFrom (q : ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ u in s..1, survFrom q t u

/-- **`V_t(y, x, q)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), App. A.1, p.24 (PDF p.25):
`V_t(y, x, q) = (c · x + y · (1 − θ(t))) · A_t(t) − y · ∫_t^1 b(s) · (S_t(s) − q(s) · A_t(s)) ds
  + (1 − y + t · y + y · A_t(t)) · ∫_t^1 b(s) · e^{−q(s)} ds`.

**Formalization Note.** `θ = thetaOf b`; the constant `c = max_{0≤s≤1}{b(s) + θ(s)} − 1` is a
parameter (statements pin it by `IsGreatest`). -/
noncomputable def Vq (b : ℝ → ℝ) (c t y x : ℝ) (q : ℝ → ℝ) : ℝ :=
  (c * x + y * (1 - thetaOf b t)) * areaFrom q t t
    - y * ∫ s in t..1, b s * (survFrom q t s - q s * areaFrom q t s)
    + (1 - y + t * y + y * areaFrom q t t) * ∫ s in t..1, b s * Real.exp (-q s)

/-- **Rates allowed in the definition of `V_t`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version), App. A.1, p.24 (PDF p.25): "we minimize over bounded
nonnegative q that are nondecreasing separately on each time interval [tk , tk+1 ), without requiring
monotonicity across different intervals", with `t_k = k/N_t`.

**Formalization Note.** Conditions are imposed on `[0,1]`; `V_t(·,·,q)` reads `q` only on `[t,1]`, and
every rate on `[t,1]` extends to `[0,1]` within the class, so the infimum is the paper's. -/
def IsVtAdmissible (Nt : ℕ) (q : ℝ → ℝ) : Prop :=
  (∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, q s ≤ M) ∧ (∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q s) ∧
    ∀ k : ℕ, k < Nt → MonotoneOn q (Set.Ico ((k : ℝ) / Nt) (((k : ℝ) + 1) / Nt))

/-- **`V_t(y, x) = inf_q V_t(y, x, q)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*,
arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.1, p.24 (PDF p.25): "Let Vt(y, x) = inf_q
{Vt(y, x, q)}, which is well-defined for the whole domain 0 ≤ y ≤ 1 and x ≥ 0".

**Formalization Note.** A real infimum over the admissible rates (`IsVtAdmissible`). The index type is
nonempty (`q = 0`), and for `0 ≤ y ≤ 1`, `x ≥ 0` the values are bounded below by `−y · θ(t)` (property 2,
p.24), so the infimum is the paper's there; outside that domain it is never used. -/
noncomputable def Vinf (b : ℝ → ℝ) (c : ℝ) (Nt : ℕ) (t y x : ℝ) : ℝ :=
  ⨅ q : {q : ℝ → ℝ // IsVtAdmissible Nt q}, Vq b c t y x q.1

end MeanOnlyProphet


