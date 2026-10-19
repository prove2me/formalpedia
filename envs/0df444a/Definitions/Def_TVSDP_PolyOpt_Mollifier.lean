-- Prove2me | Definitions.Def_TVSDP_PolyOpt_Mollifier
-- name    : TVSDP_PolyOpt_Mollifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:22.235866+00:00
-- url     : https://prove2.me/theorems/31f07b46-2f13-4e7e-a1cb-5cb744899a73
-- title:
--   Definition 3 and Remark 1, p. 11 — the mollifying operator $\mathcal M_v f(t)=\int_0^1 vJ(v(t-s))f(s)\,ds$ on $[0,1]$
-- statement:
--   This file defines the mollifying operators $\mathcal M_v$ of Definition 3.
--
--   Let $J:\mathbb R\to\mathbb R$ be the standard bump
--
--   $$J(t)=\begin{cases} c\,\exp\!\left(-\dfrac{1}{1-t^2}\right), & |t|<1,\\[4pt] 0, & |t|\ge 1,\end{cases}$$
--
--   where $c=\left(\int_{-1}^1 \exp(-1/(1-t^2))\,dt\right)^{-1}$, so that $\int_{\mathbb R}J=1$. For a nonnegative integer $v$ and a function $f$, the mollified function is
--
--   $$(\mathcal M_v f)(t)=\int_0^1 v\,J(v(t-s))\,f(s)\,ds .$$
--
--   Following Remark 1, $\mathcal M_v$ acts entrywise on vector-valued functions, $\mathcal M_v f=(\mathcal M_v f_i)_i$, and on matrix-valued functions, $\mathcal M_v P=(\mathcal M_v P_{ij})_{ij}$.
--
--   The operator integrates only over $[0,1]$, so it is not normalized near the endpoints: for $v\ge1$, $\mathcal M_v 1(0)=\mathcal M_v 1(1)=1/2$. The proof of Theorem 4 uses $\mathcal M_v$ to replace a strictly feasible solution by a continuous one.
--
--   **Formalization Note** The page writes $J(t)=c\exp(-1/(1-t^2))$ "when $t\in[-1,1]$", where the formula is undefined at $t=\pm1$; here $J(\pm1)=0$, which changes no integral. The constant is named `cJ` to avoid a clash with the objective $c$.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, p. 11, Definition 3 and Remark 1

import Mathlib

namespace TVSDP.PolyOpt

/-- The normalizing constant `c` of Definition 3, chosen so that `∫_ℝ J = 1`. -/
noncomputable def cJ : ℝ :=
  (∫ t in (-1:ℝ)..1, Real.exp (-1 / (1 - t ^ 2)))⁻¹

/-- The bump `J` of Definition 3: `J(t) = c exp(-1/(1 - t²))` for `|t| < 1` and `J(t) = 0` otherwise.
(The page writes `t ∈ [-1, 1]`, where the formula is undefined at `t = ±1`; there `J` is `0`.) -/
noncomputable def J (t : ℝ) : ℝ :=
  if |t| < 1 then cJ * Real.exp (-1 / (1 - t ^ 2)) else 0

/-- The mollifying operator of Definition 3, for `v ∈ ℕ`:
`(𝓜_v f)(t) = ∫₀¹ v J(v (t - s)) f(s) ds`. -/
noncomputable def Mv (v : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..1, (v : ℝ) * J (v * (t - s)) * f s

/-- `𝓜_v` acting entrywise on vector-valued functions (Remark 1). -/
noncomputable def MvVec {n : ℕ} (v : ℕ) (f : ℝ → Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun i => Mv v (fun s => f s i) t

/-- `𝓜_v` acting entrywise on matrix-valued functions (Remark 1). -/
noncomputable def MvMat {m : ℕ} (v : ℕ) (P : ℝ → Matrix (Fin m) (Fin m) ℝ) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => Mv v (fun s => P s j k) t

end TVSDP.PolyOpt


