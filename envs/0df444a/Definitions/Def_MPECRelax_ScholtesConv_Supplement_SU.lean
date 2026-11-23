-- Prove2me | Definitions.Def_MPECRelax_ScholtesConv_Supplement_SU
-- name    : MPECRelax_ScholtesConv_Supplement_SU
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:31:27.171897+00:00
-- url     : https://prove2.me/theorems/030c4b22-03e0-4361-8ac2-34d3386388d9
-- title:
--   §3.4, pp. 20–22 — the Steffensen–Ulbrich relaxation R^SU(t) with θ, ϕ, Φ^SU, and I_Φ(x, t)
-- statement:
--   Let $\theta:[-1,1]\to\mathbb R$ satisfy
--
--   1. $\theta$ is twice continuously differentiable on $[-1,1]$;
--   2. $\theta(-1)=\theta(1)=1$;
--   3. $\theta'(-1)=-1$ and $\theta'(1)=1$;
--   4. $\theta''(-1)=\theta''(1)=0$;
--   5. $\theta''(x)>0$ for all $x\in(-1,1)$.
--
--   For $t>0$ put
--   $$\varphi(a;t)=\begin{cases}|a|,&|a|\ge t,\\ t\,\theta(a/t),&|a|<t,\end{cases}\qquad \Phi^{SU}(x_1,x_2;t)=x_1+x_2-\varphi(x_1-x_2;t).$$
--   The local relaxation of Steffensen and Ulbrich is
--   $$R^{SU}(t):\quad \min f(x)\ \ \text{s.t.}\ \ g_i(x)\le0,\ h_j(x)=0,\ G_i(x)\ge0,\ H_i(x)\ge0,\ \Phi^{SU}(G_i(x),H_i(x);t)\le0,$$
--   with feasible set $X^{SU}(t)$, and for $x\in X^{SU}(t)$ (p. 22)
--   $$I_\Phi(x,t)=\{i : \Phi^{SU}(G_i(x),H_i(x);t)=0\}.$$
--
--   This is the program of Theorems 3.11 and 3.12.
--
--   **Formalization Note** $\theta$ is a function $\mathbb R\to\mathbb R$ whose values off $[-1,1]$ are never used; the derivatives in conditions 1–5 are taken within $[-1,1]$, so they are one-sided at $\pm1$. $R^{SU}(t)$ is an NLP with inequality constraints $g_i\le0$, $-G_i\le0$, $-H_i\le0$, $\Phi^{SU}(G_i,H_i;t)\le0$ (in this order) and equality constraints $h_j=0$. The index sets $I_G(x)=\{i : G_i(x)=0\}$ and $I_H(x)=\{i : H_i(x)=0\}$ of p. 22 are the published `MPEC.IG` and `MPEC.IH`.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 20–21, R^SU(t), Φ^SU, ϕ, conditions (a)–(e) on θ; p. 22, index sets

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC

open Set

namespace MPECRelax.ScholtesConv.Supplement

variable {n m p l : ℕ}

/-- The conditions (a)–(e) of p. 20–21 on `θ : [−1, 1] → ℝ`, for `θ : ℝ → ℝ` whose values
off `[−1, 1]` play no role; derivatives at the endpoints are one-sided (within `[−1, 1]`):
(a) `θ` is twice continuously differentiable on `[−1, 1]`; (b) `θ(−1) = θ(1) = 1`;
(c) `θ'(−1) = −1`, `θ'(1) = 1`; (d) `θ''(−1) = θ''(1) = 0`; (e) `θ''(x) > 0` on `(−1, 1)`. -/
def IsSUTheta (θ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 θ (Icc (-1) 1) ∧
  θ (-1) = 1 ∧ θ 1 = 1 ∧
  derivWithin θ (Icc (-1) 1) (-1) = -1 ∧ derivWithin θ (Icc (-1) 1) 1 = 1 ∧
  iteratedDerivWithin 2 θ (Icc (-1) 1) (-1) = 0 ∧ iteratedDerivWithin 2 θ (Icc (-1) 1) 1 = 0 ∧
  ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < iteratedDerivWithin 2 θ (Icc (-1) 1) x

/-- `ϕ(a; t) = |a|` if `|a| ≥ t`, and `t θ(a/t)` if `|a| < t` (p. 20). -/
noncomputable def phiSU (θ : ℝ → ℝ) (a t : ℝ) : ℝ :=
  if t ≤ |a| then |a| else t * θ (a / t)

/-- `Φ^SU(x₁, x₂; t) = x₁ + x₂ − ϕ(x₁ − x₂; t)` (p. 20). -/
noncomputable def PhiSU (θ : ℝ → ℝ) (x₁ x₂ t : ℝ) : ℝ :=
  x₁ + x₂ - phiSU θ (x₁ - x₂) t

/-- The local relaxation R^SU(t) of Steffensen and Ulbrich (p. 20) as an NLP. Inequality
constraints, in this order: `g_i ≤ 0` (index `inl i`), `−G_i ≤ 0` (`inr (inl i)`),
`−H_i ≤ 0` (`inr (inr (inl i))`), `Φ^SU(G_i(x), H_i(x); t) ≤ 0` (`inr (inr (inr i))`);
equality constraints `h_j = 0`. Its feasible set `X^SU(t)` is `{x | (RSU P θ t).Feasible x}`. -/
noncomputable def RSU (P : MPEC n m p l) (θ : ℝ → ℝ) (t : ℝ) :
    NLP n (Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l) (Fin p) where
  f := P.f
  g := Sum.elim P.g (Sum.elim (fun i x => -P.G i x)
         (Sum.elim (fun i x => -P.H i x) (fun i x => PhiSU θ (P.G i x) (P.H i x) t)))
  h := P.h

/-- `I_Φ(x, t) = {i | Φ^SU(G_i(x), H_i(x); t) = 0}` (p. 22). (`I_G(x)`, `I_H(x)` are the
published `MPEC.IG`, `MPEC.IH`.) -/
def IPhiSU (P : MPEC n m p l) (θ : ℝ → ℝ) (x : E n) (t : ℝ) : Set (Fin l) :=
  {i | PhiSU θ (P.G i x) (P.H i x) t = 0}

end MPECRelax.ScholtesConv.Supplement


