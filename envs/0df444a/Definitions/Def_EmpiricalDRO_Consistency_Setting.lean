-- Prove2me | Definitions.Def_EmpiricalDRO_Consistency_Setting
-- name    : EmpiricalDRO_Consistency_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:05:46.491518+00:00
-- url     : https://prove2.me/theorems/e33ac3d9-7dff-4cef-808e-f800fefb4bda
-- title:
--   (76), pp. 33–34 — the dual summand −λ log(1 − t/λ) with its boundary convention
-- statement:
--   This item defines the dual summand in (76). The shared `EmpiricalDRO.Coverage.Setting` module supplies the Burg generator and the lower robust value used below.
--
--   1. **The Burg generator** (p. 6). $\phi(t)=-\log t+t-1$ for $t>0$, and $\phi(t)=+\infty$ for $t\le 0$ (the convention $\log 0=-\infty$).
--   2. **The empirical Burg ball** (19), p. 8. For a sample of size $n$ and a radius $\eta$,
--   $$
--   \mathcal U_n(\eta)=\Big\{w\in\mathbb R^n:\ -\frac1n\sum_{i=1}^n\log(nw_i)\le\eta,\ \sum_{i=1}^n w_i=1,\ w_i\ge 0\Big\}.
--   $$
--   On the simplex, $\frac1n\sum_i\phi(nw_i)=-\frac1n\sum_i\log(nw_i)$ because $\sum_i(nw_i-1)/n=0$, so $\mathcal U_n(\rho/n)$ is the published $\phi$-divergence ball `probUncertaintySet burg (1/n,…,1/n) (ρ/n)`.
--   3. **The two empirical DRO values** (26)–(27), p. 11. For data $z=(z_1,\dots,z_n)$,
--   $$
--   \underline Z_n=\min_{w\in\mathcal U_n(\rho/n)}\sum_{i=1}^n z_iw_i,\qquad \overline Z_n=\max_{w\in\mathcal U_n(\rho/n)}\sum_{i=1}^n z_iw_i .
--   $$
--   The maximum is the published `GenEmpLik.Expansion.robustMean burg ρ z`; the shared Coverage module defines the minimum, `robustLower burg ρ z`. With $z_i=h(x;\xi_i)$ and $\rho=\chi^2_{1,1-\alpha}/2$ these are the paper's $\underline Z_n(x)$ and $\overline Z_n(x)$.
--   4. **The dual summand** of (76), pp. 33–34. For $\lambda>0$, $-\lambda\log(1-t/\lambda)$ if $t<\lambda$ and $+\infty$ if $t\ge\lambda$; for $\lambda=0$, the printed convention $-0\log(1-t/0):=0$ for $t\le 0$ and $:=\infty$ for $t>0$.
--
--   These objects are used in Theorem 3 (strong consistency of $\underline Z_n(x)$ and $\overline Z_n(x)$) and in the steps of its proof.
--
--   **Formalization Note** Divergences and the dual summand are valued in `EReal`, so infinite values are represented and never collapse to a junk real. For $n\ge1$ and $\rho\ge0$ the set of values $\{\sum_i z_iw_i\}$ is nonempty (it contains the uniform weight) and bounded (it lies in the simplex), so the real `sInf`/`sSup` are the attained minimum and maximum. The dual summand at $\lambda<0$ is never used. `burg` and `robustLower` are provided by the frozen shared `EmpiricalDRO.Coverage.Setting` module.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 6 (Burg φ), p. 8 (19), p. 11 (26)–(27), pp. 33–34 (76) and the convention after it

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_EmpiricalDRO_Coverage_Setting

namespace EmpiricalDRO.Consistency

/-- The summand `−λ log(1 − t/λ)` of the Lagrangian dual (76), p. 33, with the convention printed on
p. 34: for `λ > 0` it is `−λ log(1 − t/λ)` when `t < λ` and `+∞` when `t ≥ λ` (the conjugate of
`−log r + r − 1` is `−log(1 − s)` for `s < 1` and `∞` for `s ≥ 1`); for `λ = 0` it is
`−0 log(1 − t/0) := 0` for `t ≤ 0` and `:= ∞` for `t > 0`. The value at `λ < 0` is never used:
the dual infimum ranges over `λ ≥ 0`. -/
noncomputable def dualTerm (lam t : ℝ) : EReal :=
  if 0 < lam then
    (if t < lam then ((-lam * Real.log (1 - t / lam) : ℝ) : EReal) else ⊤)
  else
    (if t ≤ 0 then 0 else ⊤)

end EmpiricalDRO.Consistency


