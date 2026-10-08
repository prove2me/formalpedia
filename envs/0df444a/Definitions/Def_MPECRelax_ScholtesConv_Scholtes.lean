-- Prove2me | Definitions.Def_MPECRelax_ScholtesConv_Scholtes
-- name    : MPECRelax_ScholtesConv_Scholtes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:51:15.470982+00:00
-- url     : https://prove2.me/theorems/63f99f9d-95b6-4d64-a45f-0af6ad165e39
-- title:
--   Scholtes' global relaxation R^S(t) and the active index sets I_G(x), I_H(x), I_GH(x; t)
-- statement:
--   For a parameter $t$, **Scholtes' relaxed program** $R^S(t)$ replaces the complementarity constraint of the MPEC (1) by an inequality:
--   $$\min f(x)\quad\text{s.t.}\quad g_i(x)\le0\ (i=1,\dots,m),\ \ h_j(x)=0\ (j=1,\dots,p),\ \ G_i(x)\ge0,\ \ H_i(x)\ge0,\ \ G_i(x)H_i(x)\le t\ (i=1,\dots,l).$$
--   Its feasible set is $X^S(t)$. A **stationary point** of $R^S(t)$ is a KKT point of this standard nonlinear program in the sense of (2): $x$ is feasible and there are multipliers $\lambda,\gamma,\nu,\delta\ge0$ (complementary to their constraints) and $\mu$ such that
--   $$0=\nabla f(x)+\sum_{i=1}^m\lambda_i\nabla g_i(x)+\sum_{i=1}^p\mu_i\nabla h_i(x)-\sum_{i=1}^l\gamma_i\nabla G_i(x)-\sum_{i=1}^l\nu_i\nabla H_i(x)+\sum_{i=1}^l\delta_i\big[H_i(x)\nabla G_i(x)+G_i(x)\nabla H_i(x)\big],$$
--   which is (4) of the paper. For the convergence analysis the paper uses the active sets at a point $x$
--   $$I_G(x)=\{i\mid G_i(x)=0\},\qquad I_H(x)=\{i\mid H_i(x)=0\},\qquad I_{GH}(x;t)=\{i\mid H_i(x)G_i(x)=t\},$$
--   together with $I_g(x)=\{i\mid g_i(x)=0\}$.
--
--   The relaxation is the oldest of the five schemes compared in the paper; as $t\downarrow0$ it recovers the MPEC.
--
--   **Formalization Note** $R^S(t)$ is the NLP with inequality constraints $g_i\le0$, $-G_i\le0$, $-H_i\le0$, $G_iH_i-t\le0$ (in this order, indexed by `Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l`) and equality constraints $h_j=0$. "Stationary point of $R^S(t)$" is the KKT-point predicate of the NLP file, applied to this program; its gradient of $-G_i$ is $-\nabla G_i$ and of $G_iH_i-t$ is $H_i\nabla G_i+G_i\nabla H_i$ for $C^1$ data, which gives the signs of (4).
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 8–9, R^S(t) (p. 8), index sets I_g(x), I_G(x), I_H(x), I_GH(x; t) (p. 9)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC

namespace MPECRelax.ScholtesConv

namespace MPEC

variable {n m p l : ℕ}

/-- Scholtes' relaxed program R^S(t) (p. 8) as an NLP. Inequality constraints, in this order:
`g_i ≤ 0`, `−G_i ≤ 0`, `−H_i ≤ 0`, `G_i H_i − t ≤ 0`; equality constraints `h_j = 0`.
A stationary point of R^S(t) is `(P.RS t).IsKKTPoint x`; its feasible set `X^S(t)` is
`{x | (P.RS t).Feasible x}`. -/
def RS (P : MPEC n m p l) (t : ℝ) : NLP n (Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l) (Fin p) where
  f := P.f
  g := Sum.elim P.g (Sum.elim (fun i x => -P.G i x)
         (Sum.elim (fun i x => -P.H i x) (fun i x => P.G i x * P.H i x - t)))
  h := P.h

/-- `I_G(x) = {i | G_i(x) = 0}` (p. 9). (`I_g(x)` is `P.Ig x`.) -/
def IG (P : MPEC n m p l) (x : E n) : Set (Fin l) := {i | P.G i x = 0}

/-- `I_H(x) = {i | H_i(x) = 0}` (p. 9). -/
def IH (P : MPEC n m p l) (x : E n) : Set (Fin l) := {i | P.H i x = 0}

/-- `I_{GH}(x; t) = {i | H_i(x) G_i(x) = t}` (p. 9). -/
def IGH (P : MPEC n m p l) (x : E n) (t : ℝ) : Set (Fin l) := {i | P.H i x * P.G i x = t}

end MPEC

end MPECRelax.ScholtesConv


