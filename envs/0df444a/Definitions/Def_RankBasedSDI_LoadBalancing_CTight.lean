-- Prove2me | Definitions.Def_RankBasedSDI_LoadBalancing_CTight
-- name    : RankBasedSDI_LoadBalancing_CTight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:37.45955+00:00
-- url     : https://prove2.me/theorems/3dfea164-aef8-4d95-8980-b760ce36dbae
-- title:
--   Modulus of continuity $w_t(f,\delta)$ and C-tightness of a sequence of processes
-- statement:
--   For a path $f:\mathbb R_+\to\mathbb R^m$ write $\|f\|^*_t=\sup_{s\in[0,t]}\|f(s)\|$, and define the **modulus of continuity**
--
--   $$
--   w_t(f,\delta)=\sup\{\|f(u)-f(s)\| : u,s\in[0,t],\ |u-s|\le\delta\}.
--   $$
--
--   A sequence of $\mathbb R^m$-valued processes $Z^n$ on $(\Omega,\mathcal F,P)$ is **C-tight** if both of the following hold:
--
--   1. for every $t\ge0$: $\lim_{K\to\infty}\limsup_{n\to\infty}P(\|Z^n\|^*_t>K)=0$;
--   2. for every $t\ge0$ and $\varepsilon>0$: $\lim_{\delta\downarrow0}\limsup_{n\to\infty}P(w_t(Z^n,\delta)>\varepsilon)=0$.
--
--   For processes with càdlàg paths this is equivalent to tightness of the laws in $D(\mathbb R_+,\mathbb R^m)$ with every limit point supported on continuous paths (Jacod–Shiryaev, Prop. VI.3.26).
--
--   **Formalization Note** The limits are written out with explicit quantifiers: for every $\eta>0$ there is $K$ (respectively $\delta>0$) such that the probability is at most $\eta$ for all large $n$. The norm is the $\ell^1$ norm of the referenced `supDist`, which is equivalent to the paper's Euclidean norm, so C-tightness is unchanged. Suprema are taken in $[0,\infty]$.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 3, §1.1 (‖f‖*_t, w_t(f, δ)); C-tightness as used in Proposition 4.1(i) and Lemma 4.4(iii), p. 11 and p. 13

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory Filter
open scoped ENNReal

namespace RankBasedSDI.LoadBalancing

open BellWilliams2001.ThresholdPolicy

/-- The modulus of continuity of §1.1 (Atar & Ichiba, arXiv:2409.15121v1, p. 3),
`w_t(f, δ) = sup{‖f(u) − f(s)‖ : u, s ∈ [0, t], |u − s| ≤ δ}`, for `ℝ^m`-valued paths, with the
`ℓ¹` norm of `supDist` (equivalent to the paper's Euclidean norm), computed in `[0, ∞]`. -/
noncomputable def modulus {m : ℕ} (f : ℝ → Fin m → ℝ) (t δ : ℝ) : ℝ≥0∞ :=
  ⨆ (u : ℝ) (s : ℝ) (_ : u ∈ Set.Icc 0 t ∧ s ∈ Set.Icc 0 t ∧ |u - s| ≤ δ),
    ENNReal.ofReal (∑ i, |f u i - f s i|)

/-- **C-tightness** of a sequence of `ℝ^m`-valued processes `Z n` on `(Ω, P)`, in the
Jacod–Shiryaev VI.3.26 form: for every `t ≥ 0`,
`lim_{K→∞} limsup_n P(‖Z n‖*_t > K) = 0`, and for every `t ≥ 0`, `ε > 0`,
`lim_{δ↓0} limsup_n P(w_t(Z n, δ) > ε) = 0`. For processes with càdlàg paths this is equivalent
to tightness of the laws in `D(ℝ₊, ℝ^m)` with every limit point supported on continuous paths.
The limits are written out with explicit quantifiers, and `‖·‖*_t = supDist · 0 t` is the `ℓ¹`
sup-norm on `[0, t]` in `[0, ∞]`. -/
def IsCTight {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℕ}
    (Z : ℕ → Ω → ℝ → Fin m → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∀ᶠ n in atTop,
    P {ω | ENNReal.ofReal K < supDist (Z n ω) (fun _ _ => 0) t} ≤ ENNReal.ofReal η) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
    P {ω | ENNReal.ofReal ε < modulus (Z n ω) t δ} ≤ ENNReal.ofReal η)

end RankBasedSDI.LoadBalancing


