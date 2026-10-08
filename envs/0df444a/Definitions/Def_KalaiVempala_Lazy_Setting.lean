-- Prove2me | Definitions.Def_KalaiVempala_Lazy_Setting
-- name    : KalaiVempala_Lazy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:26.654514+00:00
-- url     : https://prove2.me/theorems/060b2310-1ae7-4e69-bd0d-b5bab10577fb
-- title:
--   §1.1, §3.1, §4, pp. 293–304 — the argmin oracle, the Laplace law μ, the FLL grid point and the FLL* chain
-- statement:
--   **Setting of Follow the Lazy Leader.** In the linear online decision problem of Kalai and Vempala a decision maker picks $d_t$ from a decision set $\mathcal D \subset \mathbb R^n$, then sees a state $s_t \in \mathbb R^n$ and pays $d_t \cdot s_t$. Write $s_{1:t} = s_1 + \dots + s_t$ (with $s_{1:0} = 0$). These are the objects needed to state Lemma 1.2; items 1 and 2 are imported from the shared definitions `KalaiVempala.Additive.Setting` (`IsArgminOracle`) and `KalaiVempala.Multiplicative.Setting` (`laplaceLaw`), items 3–6 are defined here.
--
--   1. **The argmin oracle.** A map $M : \mathbb R^n \to \mathbb R^n$ is an argmin oracle for $\mathcal D$ when, for every $x$, $M(x) \in \mathcal D$ and $M(x) \cdot x \le d \cdot x$ for all $d \in \mathcal D$, i.e. $M(x) = \operatorname{arg\,min}_{d \in \mathcal D} d \cdot x$ with arbitrary tie-breaking.
--   2. **The Laplace law.** For $\varepsilon > 0$, $\mu$ is the probability measure on $\mathbb R^n$ with density
--   $$d\mu(x) = (\varepsilon/2)^n\, e^{-\varepsilon |x|_1}, \qquad |x|_1 = \textstyle\sum_i |x_i| .$$
--   It is the perturbation law of FPL\*($\varepsilon$) and of FLL\*($\varepsilon$).
--   3. **The FLL grid point.** An offset $p \in \mathbb R^n$ determines the grid $G = \{p + \tfrac1\varepsilon z : z \in \mathbb Z^n\}$. For $x \in \mathbb R^n$ the grid point is
--   $$g(x, p)_i = p_i + \frac{\lceil \varepsilon (x_i - p_i) \rceil}{\varepsilon}, \qquad i = 1, \dots, n,$$
--   the unique point of $G$ in the half-open cube $x + [0, 1/\varepsilon)^n$. FLL($\varepsilon$) draws $p$ uniformly from $[0,1/\varepsilon]^n$ once and on period $t$ plays $M(g_{t-1})$ with $g_{t-1} = g(s_{1:t-1}, p)$.
--   4. **The FLL\* acceptance probability.** For a current perturbation $p$ and state $v$,
--   $$a(v, p) = \min\Big\{1, \frac{d\mu(p - v)}{d\mu(p)}\Big\} = \min\big\{1, e^{-\varepsilon(|p - v|_1 - |p|_1)}\big\}.$$
--   5. **One FLL\* update.** If $p_t$ has law $\nu$ and the state of period $t$ is $v = s_t$, then with probability $a(v, p_t)$ FLL\* sets $p_{t+1} = p_t - v$ and otherwise $p_{t+1} = -p_t$. The joint law of $(p_t, p_{t+1})$ is
--   $$J_{\varepsilon, v}(\nu) = \int \Big( a(v,p)\, \delta_{(p,\, p - v)} + (1 - a(v,p))\, \delta_{(p,\, -p)} \Big)\, d\nu(p).$$
--   6. **The law of $p_t$.** Against a fixed state sequence $s_1, s_2, \dots$, the law $\nu_t$ of FLL\*'s perturbation is defined by $\nu_1 = \mu$ and $\nu_{t+1}$ = the second marginal of $J_{\varepsilon, s_t}(\nu_t)$.
--
--   These are the algorithms of §3.1 and §4 of the paper, written as laws against an oblivious (fixed) state sequence, which is the setting of Lemma 1.2.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and $d \cdot s$ is `dotProduct`. The oracle is a predicate, not a chosen minimiser. $s_{1:t}$ and the uniform law on $[0, 1/\varepsilon]^n$ are `prefixSum` and `perturbLaw` from the published definition `OracleRO.ApproxFPL.FPL`. The grid point is the explicit ceiling formula, so no choice is involved; for $\varepsilon \le 0$ it is junk and every theorem assumes $\varepsilon > 0$. The joint law uses `Measure.bind` and `Measure.dirac`. The law sequence is 1-based: `fllStarLaw ε s 0` is set to $\mu$ and is never used. The oracle and the Laplace law are not redefined: they are the shared definitions of this paper's missions.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), pp. 293–294 §1.1 (M, FPL*, μ), p. 302 §3.1 (FLL(ε)), p. 304 §4 (FLL*(ε))

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory

namespace KalaiVempala.Lazy

/-- The grid point of FLL(ε) (p. 302). The offset `p` determines the grid
`G = {p + (1/ε) z | z ∈ ℤⁿ}`; for `ε > 0`, `fllGridPoint ε x p` is the unique point of `G` in
the half-open cube `x + [0, 1/ε)ⁿ`, computed coordinatewise as `p_i + ⌈ε (x_i - p_i)⌉ / ε`.
At period `t` FLL(ε) plays `M(g_{t-1})` with `g_{t-1} = fllGridPoint ε (prefixSum s (t - 1)) p`. -/
noncomputable def fllGridPoint {n : ℕ} (ε : ℝ) (x p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => p i + (⌈ε * (x i - p i)⌉ : ℝ) / ε

/-- The acceptance probability of step 3(a) of FLL*(ε) (p. 304), `min(1, dμ(p - v)/dμ(p))` with
`p = p_t` and `v = s_t`. The normalising constant of `dμ` cancels in the ratio, which is
`e^{-ε(|p - v|₁ - |p|₁)}`. -/
noncomputable def fllStarAccept {n : ℕ} (ε : ℝ) (v p : Fin n → ℝ) : ℝ :=
  min 1 (Real.exp (-(ε * (∑ i, |p i - v i| - ∑ i, |p i|))))

/-- One update of FLL*(ε) (p. 304, step 3) as the joint law of `(p_t, p_{t+1})`, when `p_t` has
law `ν` and the state of period `t` is `v = s_t`: with probability `fllStarAccept ε v p_t` set
`p_{t+1} = p_t - v` (step 3(a)), otherwise `p_{t+1} = -p_t` (step 3(b)). -/
noncomputable def fllStarJoint {n : ℕ} (ε : ℝ) (v : Fin n → ℝ) (ν : Measure (Fin n → ℝ)) :
    Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ν.bind fun p => ENNReal.ofReal (fllStarAccept ε v p) • Measure.dirac (p, p - v)
    + ENNReal.ofReal (1 - fllStarAccept ε v p) • Measure.dirac (p, -p)

/-- The law of the perturbation `p_t` of FLL*(ε) (p. 304) against the fixed state sequence `s`:
`p_1 ∼ μ` (step 1) and `p_{t+1}` is obtained from `p_t` and `s_t` by `fllStarJoint`.
Periods are 1-based as on the page; index `0` is unused and set to `μ`. -/
noncomputable def fllStarLaw {n : ℕ} (ε : ℝ) (s : ℕ → Fin n → ℝ) : ℕ → Measure (Fin n → ℝ)
  | 0 => KalaiVempala.Multiplicative.laplaceLaw n ε
  | 1 => KalaiVempala.Multiplicative.laplaceLaw n ε
  | k + 2 => (fllStarJoint ε (s (k + 1)) (fllStarLaw ε s (k + 1))).map Prod.snd

end KalaiVempala.Lazy


