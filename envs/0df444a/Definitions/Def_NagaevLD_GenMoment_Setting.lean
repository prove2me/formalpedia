-- Prove2me | Definitions.Def_NagaevLD_GenMoment_Setting
-- name    : NagaevLD_GenMoment_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:27.385143+00:00
-- url     : https://prove2.me/theorems/fa0aaa35-dc63-4d4d-bc03-241e0abbcacc
-- title:
--   §0, §2, pp. 745, 759, 767 — the sum S_n, the generalized moments b_gj and the negative-part factors b_j(s)
-- statement:
--   Let $X_1,\dots,X_n$ be real random variables on a probability space $(\Omega,\mathcal F,P)$, with distribution functions $F_j(u)=P(X_j<u)$, and let
--   $$S_n = X_1+\dots+X_n .$$
--   Let $g:\mathbb R\to\mathbb R$ be a function with derivative $g'$. Two families of truncated exponential moments are attached to each summand.
--
--   1. The **generalized moment** of $X_j$,
--   $$b_{gj} = \int_{u\ge 0} e^{g(u)}\,dF_j(u) = E\big[e^{g(X_j)};\,X_j\ge 0\big].$$
--   2. For a real number $s$, the **negative-part factor**
--   $$b_j(s) = e^{g(0)}\int_{u<0} e^{g'(s)u}\,dF_j(u) = e^{g(0)}\,E\big[e^{g'(s)X_j};\,X_j<0\big].$$
--
--   These are the quantities in which Theorem 2.5 of Nagaev (1979) bounds the upper tail $P(S_n\ge x)$: $b_{gj}$ measures the right tail of $X_j$ on the scale $e^{g}$, and $b_j(s)$ collects the contribution of the negative values of $X_j$ at the exponential tilt $h=g'(s)$.
--
--   **Formalization Note** The summands are indexed by `Fin n` (index $j$ in Lean is the paper's $j+1$). Integrals against $dF_j$ over a set of $u$ are written as expectations of $X_j$ restricted to the corresponding event, so no distribution functions appear. The paper defines $b_{gi}=\int_{0+}^{\infty}e^{g(u)}\,dF_i(u)$ (p. 759), i.e. over $u>0$; the proof of Theorem 2.5 splits $Ee^{hX_j}$ at $0-$ and bounds the whole part on $u\ge 0$ by $b_{gj}$ ((2.46), p. 767), and with the $u>0$ reading the theorem is false (an atom of $X_j$ at $0$ is then counted nowhere). The definition therefore integrates over $u\ge 0$. These are real-valued Bochner integrals; statements that use $b_{gj}$ as a finite number assume the integrability of $e^{g(X_j)}$ on $\{X_j\ge 0\}$ explicitly.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 745, §0 (S_n, F_i); p. 759, §2 (b_gi); p. 767, Theorem 2.5 (b_j(x))

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.GenMoment

open MeasureTheory

/-- The generalized moment `b_gj = E[e^{g(X_j)}; X_j ≥ 0]` (p. 759), taken over the event
`X_j ≥ 0` (the reading the proof of Theorem 2.5 uses, see (2.46)). -/
noncomputable def bg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (g : ℝ → ℝ) (j : Fin n) : ℝ :=
  ∫ ω in {ω | 0 ≤ X j ω}, Real.exp (g (X j ω)) ∂P

/-- `b_j(s) = e^{g(0)} E[e^{g'(s) X_j}; X_j < 0]` (Theorem 2.5, p. 767), where `g'` is the
derivative of `g`. -/
noncomputable def bj {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (g g' : ℝ → ℝ) (j : Fin n) (s : ℝ) : ℝ :=
  Real.exp (g 0) * ∫ ω in {ω | X j ω < 0}, Real.exp (g' s * X j ω) ∂P

end NagaevLD.GenMoment


