-- Prove2me | Definitions.Def_UninformedMG_divRes
-- name    : UninformedMG_divRes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:21.893506+00:00
-- url     : https://prove2.me/theorems/08aef012-7209-40bf-b3c5-c7f5b443a1ca
-- title:
--   Divergence $D_{\mathcal H_{\mathrm{res}}}$ of the refined regularizer, uniform start $z^1$ and comparators $z^{v,x}$
-- statement:
--   The refined regularizer (20) is $\mathcal H_{\mathrm{res}}(z)=H\sum_vw(v)\log w(v)+\sum_{h,s,v,a}z_{h,s,v,a}\log\frac{z_{h,s,v,a}}{w(v)}$. Its **divergence** is
--   $$D_{\mathcal H_{\mathrm{res}}}(z'\,\|\,z)=H\,\mathrm{KL}(w'\|w)+\sum_{h,s,v}w'(v)\,\mathrm{KL}\big(\pi'_h(\cdot\mid s,v)\,\big\|\,\pi_h(\cdot\mid s,v)\big),$$
--   where terms with $w'(v)=0$ contribute zero and $\mathrm{KL}(p\|q)=\sum_ip_i\log(p_i/q_i)$.
--
--   The **uniform start** (6) is $z^1_{h,s,v,a}=1/(N|A_h|)$, i.e. $w^1(v)=1/N$ and $\pi^1_h(a\mid s,v)=1/|A_h|$. For a candidate $v$ and a mixed Markov policy $x$, the **comparator** is $z^{v,x}_{h,s,v',a}=\mathbf 1\{v'=v\}x_h(a\mid s)$, the pair $(\mathbf 1\{\cdot=v\},x)$.
--
--   **Formalization Note** The divergence is defined by the formula on p.16, because $\mathcal H_{\mathrm{res}}$ is defined only on $\mathcal Z$. KL is the platform definition `GraphAlignment.Impossible.kl`. If the second argument vanishes where the first does not, the paper's value is $+\infty$ while Lean's is finite. Every use in the mission has a positive second argument.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Eq. (20), p.11 (PDF p.13); divergence and comparator, p.16 (PDF p.18); Eq. (6), p.5 (PDF p.7)

import Mathlib
import Definitions.Def_UninformedMG_IsJoint
import Definitions.Def_GraphAlignment_Impossible_InfoMeasures

namespace UninformedMG

open GraphAlignment.Impossible

variable {H : ℕ}

/-- **Divergence of the refined regularizer** (p.16 = PDF p.18; regularizer Eq. (20), p.11):
for `z' = w'π'` and `z = wπ`,
`D_{ℋres}(z' ‖ z) = H KL(w' ‖ w) + ∑_{h,s,v} w'(v) KL(π'_h(·|s,v) ‖ π_h(·|s,v))`, where terms with
`w'(v) = 0` contribute zero. `KL(p ‖ r) = ∑_i p_i log(p_i / r_i)` (natural log, p.3) is the
platform's `GraphAlignment.Impossible.kl`.

**Formalization Note.** `ℋ_res(z) = H ∑_v w(v) log w(v) + ∑ z log(z / w(v))` depends on `z`
through `w`, which is defined only on `Z`, so the divergence is defined by the formula the paper
gives for it rather than as a Bregman divergence. A term `p log(p / r)` with `p = 0` is `0`, and
`w'(v) = 0` multiplies its term by `0`, as in the paper. When the second argument vanishes where
the first does not, the paper's value is `+∞` while Lean's `Real.log 0 = 0` gives a finite
number; every use in the mission has a strictly positive second argument (the uniform start and
the algorithm's iterates). -/
noncomputable def divRes {G : Game H} (V : CandClass G) (w' : V.C → ℝ) (π' : CPolicy V)
    (w : V.C → ℝ) (π : CPolicy V) : ℝ :=
  (H : ℝ) * kl w' w + ∑ h : Fin H, ∑ s, ∑ v, w' v * kl (π' h s v) (π h s v)

/-- Uniform weights `w¹(v) = 1/N` of the start (Eq. (6), p.5), `N = |V|`. -/
noncomputable def unifW {G : Game H} (V : CandClass G) : V.C → ℝ :=
  fun _ => 1 / (Fintype.card V.C : ℝ)

/-- Uniform action distributions `π¹_h(a | s, v) = 1/|A_h|` of the start (Eq. (6), p.5); together
with `unifW` they give `z¹_{h,s,v,a} = 1/(N |A_h|)`. -/
noncomputable def unifPi {G : Game H} (V : CandClass G) : CPolicy V :=
  fun h _ _ _ => 1 / (Fintype.card (G.Act h) : ℝ)

/-- Comparator weights of `z^{v,x}` (p.16): the point mass `1{v' = v}`. -/
def cmpW {G : Game H} (V : CandClass G) (v : V.C) : V.C → ℝ :=
  fun v' => if v' = v then 1 else 0

/-- Comparator policies of `z^{v,x}` (p.16): `π_h(· | s, v') = x_h(· | s)` for every `v'`, so that
`z^{v,x}_{h,s,v',a} = 1{v' = v} x_h(a | s)`. -/
def cmpPi {G : Game H} (V : CandClass G) (x : LPolicy G) : CPolicy V :=
  fun h s _ a => x h s a

end UninformedMG


