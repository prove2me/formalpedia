-- Prove2me | Definitions.Def_FairReplay_Supplement_TwoClassFamily_QLB
-- name    : FairReplay_Supplement_TwoClassFamily_QLB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:49:03.624276+00:00
-- url     : https://prove2.me/theorems/9e3d8191-e0e5-4cb8-887a-a112923fedad
-- title:
--   Information lower program $Q_{\mathrm{LB}}(d)$, $K_{\mathrm{ctrl}}$, $K_{\mathrm{bnd}}$, $b_2$, $b_3$
-- statement:
--   With $r=1-p-s-\tau$, define
--   $$K_{\mathrm{ctrl}}(d)=r\log\frac{r}{r-d},\qquad K_{\mathrm{bnd}}(\tau,d)=\tau\log\frac{\tau}{\tau+d}+r\log\frac{r}{r-d},$$
--   $b_2=\tfrac12(\tau^{-1}+r^{-1})$ and $b_3=\tfrac13(r^{-2}-\tau^{-2})$. Let $R_{x,i}=1$ if group $S_i$ contains $x$ and no other high vertex (a **boundary-only** group), and $0$ otherwise. The **information lower program** is
--   $$Q_{\mathrm{LB}}(d)=\min_{n\ge 0}\Big\{c^\top n:\ \sum_i\big(K_{\mathrm{ctrl}}C_{x,i}+K_{\mathrm{bnd}}R_{x,i}\big)n_i\ge \mathrm{kl}(1-\delta,\delta)\ \ \forall x\in A\Big\}.$$
--   $K_{\mathrm{ctrl}}$ and $K_{\mathrm{bnd}}$ are the KL divergences of one query of a control group and of a boundary-only group containing the changed candidate.
--
--   **Formalization Note** The minimum over real $n\ge 0$ is an infimum in $[0,\infty]$, equal to $\infty$ when infeasible. $\mathrm{kl}(x,y)=x\log\frac xy+(1-x)\log\frac{1-x}{1-y}$.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9(i), eq. (65), (iv), eq. (69), p.19 and proof of (i), p.21 (PDF pp.21, 23)

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_Supplement_TwoClassFamily
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP

namespace FairReplay.Supplement

/-- `K_ctrl(d) = r log(r/(r − d))`, `r = 1 − p − s − τ` (Theorem 10.9, proof of (i), p.21): the KL of
one query of a control group containing the changed candidate. -/
noncomputable def Kctrl (p s τ d : ℝ) : ℝ :=
  (1 - p - s - τ) * Real.log ((1 - p - s - τ) / ((1 - p - s - τ) - d))

/-- `K_bnd(τ, d) = τ log(τ/(τ + d)) + r log(r/(r − d))`, `r = 1 − p − s − τ` (Theorem 10.9, proof of
(i), p.21): the KL of one query of a boundary-only group containing the changed candidate. -/
noncomputable def Kbnd (p s τ d : ℝ) : ℝ :=
  τ * Real.log (τ / (τ + d)) + (1 - p - s - τ) * Real.log ((1 - p - s - τ) / ((1 - p - s - τ) - d))

/-- `b2 = (τ⁻¹ + r⁻¹)/2` (Theorem 10.9(iv), eq. (69), p.19), `r = 1 − p − s − τ`. -/
noncomputable def b2 (p s τ : ℝ) : ℝ :=
  (τ⁻¹ + (1 - p - s - τ)⁻¹) / 2

/-- `b3 = (r⁻² − τ⁻²)/3` (Theorem 10.9(iv), eq. (69), p.19), `r = 1 − p − s − τ`. -/
noncomputable def b3 (p s τ : ℝ) : ℝ :=
  (((1 - p - s - τ) ^ 2)⁻¹ - (τ ^ 2)⁻¹) / 3

namespace TwoClassFamily

/-- `R_{x,i} = 1`: group `i` is a **boundary-only** group for `x` — it contains `x` and no other high
vertex (Theorem 10.9, proof of (i), p.21: "If the group contains x but no other high vertex"). -/
def IsBoundary (F : TwoClassFamily) (x : Fin F.n) (i : Fin F.k) : Prop :=
  x ∈ F.S i ∧ ∀ y ∈ F.S i, y ≠ x → F.high y = false

/-- The boundary matrix `R` as a `0/1` real matrix. -/
noncomputable def bnd (F : TwoClassFamily) (x : Fin F.n) (i : Fin F.k) : ℝ := by
  classical exact if F.IsBoundary x i then 1 else 0

/-- **The information lower program** `QLB(d)` (Sah, Zhang, Lian, *Testing Fairness of Evolving
Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…,
Theorem 10.9(i), eq. (65), and (iv), p.19 (PDF p.21)):
`min_{n ≥ 0} { c⊤n : (K_ctrl C + K_bnd R) n ≥ kl(1 − δ, δ) 1 }`, rows indexed by the candidates
`x ∈ A`.

**Formalization Note** The infimum over real `n ≥ 0` is taken in `[0, ∞]`; it is `∞` when the
program is infeasible (some candidate lies in no group). `kl` is
`BanditAlgorithm.bernoulliRelativeEntropy`. -/
noncomputable def QLB (F : TwoClassFamily) (p s τ d δ : ℝ) : ENNReal :=
  ⨅ (nv : Fin F.k → ℝ) (_ : ∀ i, 0 ≤ nv i)
    (_ : ∀ x ∈ F.A, BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ ≤
      ∑ i, (Kctrl p s τ d * F.ctrl x i + Kbnd p s τ d * F.bnd x i) * nv i),
    ENNReal.ofReal (∑ i, F.c i * nv i)

end TwoClassFamily

end FairReplay.Supplement


