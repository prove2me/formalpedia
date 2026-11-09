-- Prove2me | Definitions.Def_MultiNashRepair_Knobs
-- name    : MultiNashRepair_Knobs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:41.640129+00:00
-- url     : https://prove2.me/theorems/4514f40a-a61e-4f11-bf65-f7ee334bb3d7
-- title:
--   The repair controls $c, t, \rho, \beta, \nu, R_0, G_0, Q, a_u, L_0$, the threshold $S_u$ and the potential $\widehat\Phi_u$
-- statement:
--   For an activation fraction $f_0$ and a repair step scale $u$ define
--   $$c=1-u+\tfrac{u^2}{2}-u^3,\quad t=f_0u,\quad \rho=1-(1-f_0)u+\tfrac{(1-f_0)^2u^2}{2}\qquad(5.3)$$
--   $$u_0=u-u^2,\quad \beta=ct(1+u_0),\quad \nu=cu_0\qquad(5.4)$$
--   $$R_0=\frac{1-\rho}{\beta},\quad G_0=1+R_0,\quad Q=\frac{\nu}{\beta}\qquad(5.5)$$
--   $$a_u=R_0(Q-1),\quad L_0=\frac{ct}{1-c},\quad Q_0=tQ\qquad(5.6)$$
--   the overlap bound $C_u(H)=R_0\frac{1+H}{1+QH}$, the **descent threshold** $S_u(H)=1+H+C_u(H)$ (3.13), the **repair contribution** $D(H)=\beta(G_0+QH)$ (3.6), the **repair coefficient** (5.45)
--   $$K_u(H)=G_0+\frac{H[D(H)-(1-c)G_0]}{ct}+M\Bigl[(1-a_u)\log\frac{T}{H}+a_u\log\frac{1+QT}{1+QH}\Bigr],\quad T=c(H+t),\ M=\frac{H(H+t)}{t},$$
--   with $K_u(0)=G_0$, and the potentials
--   $$F_u(H)=-\frac{G_0}{H}+(1-a_u)\log\frac{H}{f_0}+a_u\log(1+QH),\quad \Phi_u(\varsigma,H)=\frac{\varsigma}{H}+F_u(H),\quad \widehat\Phi_u(\varsigma,H)=\Phi_u(\varsigma,H)+\frac{2d}{H}.$$
--
--   These are the fixed controls of Algorithm 1 and the potential whose increase bounds the number of iterations.
--
--   **Formalization Note** The paper's $f_0,u$ are rational; here they are real so that the scalar milestones hold on the paper's verification ranges. Statements restrict to $0<u\le1/16$, $f_0\in[7/12,3/5]$, and $H>0$ for the potential, where all denominators and logarithm arguments are positive.
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), §3.3, (3.13), p.10; (3.6), p.8; §5.1, (5.3)–(5.6), pp.15–16; (5.43), (5.45), p.36; (5.51), p.38

import Mathlib

noncomputable section

namespace MultiNashRepair

/-- **The repair controls as functions of the activation fraction `f0` and the repair step
scale `u`** (Tang, Ding, Fang, arXiv:2611.06076, §3.3 p.10 and §5.1 pp.15–16, displays
(3.13), (3.6) and (5.3)–(5.6); the potential (5.43), (5.51) and the coefficient (5.45),
pp.36–38).

For a pair `k = (f0, u)` of reals:
`c = 1 − u + u²/2 − u³`, `t = f0 u`, `ρ = 1 − (1 − f0)u + (1 − f0)²u²/2` (5.3);
`u0 = u − u²`, `β = c t (1 + u0)`, `ν = c u0` (5.4);
`R0 = (1 − ρ)/β`, `G0 = 1 + R0`, `Q = ν/β` (5.5);
`a_u = R0 (Q − 1)`, `L0 = c t/(1 − c)`, `Q0 = t Q` (5.6);
`C_u(H) = R0 (1 + H)/(1 + Q H)`, `S_u(H) = 1 + H + C_u(H)` (3.13), p.16;
`D(H) = β (G0 + Q H)` (3.6);
`K_u(H)` of (5.45) with `T = c(H + t)`, `M = H(H + t)/t`, and `K_u(0) = G0`;
`F_u(H) = −G0/H + (1 − a_u) log(H/f0) + a_u log(1 + Q H)` and `Φ_u(ς, H) = ς/H + F_u(H)`
(5.43); `Φ̂_u(ς, H) = Φ_u(ς, H) + 2d/H` (5.51).

**Formalization Note.** The paper's `f0` and `u` are rational; these are real functions so that
the scalar milestones can be stated for every real `f0`, `u` in the paper's verification ranges.
Division is total (`x/0 = 0`) and `Real.log` is `0` on nonpositive arguments; every statement
using these functions restricts to `0 < u ≤ 1/16`, `f0 ∈ [7/12, 3/5]` and, for the potential,
`H > 0`, where every denominator and logarithm argument is positive. `K_u(0) = G0` is the
paper's continuous extension (Lemma 5.11, p.37). -/
structure Knobs where
  /-- the activation fraction `f0` -/
  f0 : ℝ
  /-- the repair step scale `u` -/
  u : ℝ

namespace Knobs

variable (k : Knobs)

/-- `c = 1 − u + u²/2 − u³` (5.3). -/
def c : ℝ := 1 - k.u + k.u ^ 2 / 2 - k.u ^ 3
/-- `t = f0 u` (5.3). -/
def t : ℝ := k.f0 * k.u
/-- `ρ = 1 − (1 − f0)u + (1 − f0)²u²/2` (5.3). -/
def rho : ℝ := 1 - (1 - k.f0) * k.u + (1 - k.f0) ^ 2 * k.u ^ 2 / 2
/-- `u0 = u − u²` (5.4). -/
def u0 : ℝ := k.u - k.u ^ 2
/-- `β = c t (1 + u0)` (5.4). -/
def beta : ℝ := k.c * k.t * (1 + k.u0)
/-- `ν = c u0` (5.4). -/
def nu : ℝ := k.c * k.u0
/-- `R0 = (1 − ρ)/β` (5.5). -/
def R0 : ℝ := (1 - k.rho) / k.beta
/-- `G0 = 1 + R0` (5.5). -/
def G0 : ℝ := 1 + k.R0
/-- `Q = ν/β` (5.5). -/
def Q : ℝ := k.nu / k.beta
/-- `a_u = R0 (Q − 1)` (5.6). -/
def au : ℝ := k.R0 * (k.Q - 1)
/-- `L0 = c t/(1 − c)` (5.6). -/
def L0 : ℝ := k.c * k.t / (1 - k.c)
/-- `Q0 = t Q` (5.6). -/
def Q0 : ℝ := k.t * k.Q
/-- `C_u(H) = R0 (1 + H)/(1 + Q H)` (p.16). -/
def Cu (H : ℝ) : ℝ := k.R0 * (1 + H) / (1 + k.Q * H)
/-- The descent threshold `S_u(H) = 1 + H + C_u(H)` ((3.13), p.10). -/
def Su (H : ℝ) : ℝ := 1 + H + k.Cu H
/-- The total repair contribution `D = β (G0 + Q H)` ((3.6), p.8). -/
def Dsh (H : ℝ) : ℝ := k.beta * (k.G0 + k.Q * H)
/-- The repair coefficient `K_u(H)` of (5.45), p.36, with `K_u(0) = G0` (Lemma 5.11, p.37). -/
def Ku (H : ℝ) : ℝ :=
  if H = 0 then k.G0 else
    k.G0 + H * (k.Dsh H - (1 - k.c) * k.G0) / (k.c * k.t)
      + H * (H + k.t) / k.t *
        ((1 - k.au) * Real.log (k.c * (H + k.t) / H)
          + k.au * Real.log ((1 + k.Q * (k.c * (H + k.t))) / (1 + k.Q * H)))
/-- `F_u(H) = −G0/H + (1 − a_u) log(H/f0) + a_u log(1 + Q H)` ((5.43), p.36). -/
def Fu (H : ℝ) : ℝ :=
  -k.G0 / H + (1 - k.au) * Real.log (H / k.f0) + k.au * Real.log (1 + k.Q * H)
/-- `Φ_u(ς, H) = ς/H + F_u(H)` ((5.43), p.36). -/
def Phiu (ς H : ℝ) : ℝ := ς / H + k.Fu H
/-- `Φ̂_u(ς, H) = Φ_u(ς, H) + 2d/H` ((5.51), p.38; equivalently (4.11), p.14). -/
def Phihat (d ς H : ℝ) : ℝ := k.Phiu ς H + 2 * d / H

end Knobs

end MultiNashRepair


