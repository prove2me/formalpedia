-- Prove2me | Definitions.Def_IQCAlg_HeavyBall_Setting
-- name    : IQCAlg_HeavyBall_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:13.135135+00:00
-- url     : https://prove2.me/theorems/b21e5185-030a-48d6-91b1-5584612cbc74
-- title:
--   §1.1, §2, Prop. 1, (4.11), App. B — S(m, L) on ℝ, the gradient (4.11), the Heavy-ball run with x₋₁ = x₀, its tuning, the cycle (B.3), P, ε̄
-- statement:
--   This file fixes the objects of the Heavy-ball counterexample of Lessard, Recht and Packard (Section 4.6 and Appendix B).
--
--   1. **The class $S(m,L)$ in one dimension.** For $0<m<L$, a function $f:\mathbb R\to\mathbb R$ belongs to $S(m,L)$ if it is continuously differentiable, strongly convex with parameter $m$ (that is, $f(ax+by)\le af(x)+bf(y)-ab\,\tfrac m2|x-y|^2$ for $a,b\ge 0$, $a+b=1$), and its derivative is $L$-Lipschitz: $|f'(x)-f'(y)|\le L|x-y|$.
--   2. **The gradient (4.11).**
--   $$\nabla f(x)=\begin{cases}25x & x<1,\\ x+24 & 1\le x<2,\\ 25x-24 & x\ge 2.\end{cases}$$
--   3. **The Heavy-ball run.** For a map $g$ (playing the role of $\nabla f$), a step size $\alpha$, a momentum $\beta$ and a starting point $x_0$, the sequence $x_0,x_1,x_2,\dots$ is defined by $x_{k+1}=x_k-\alpha g(x_k)+\beta(x_k-x_{k-1})$ with the initialization $x_{-1}=x_0$; hence $x_1=x_0-\alpha g(x_0)$.
--   4. **Proposition 1's tuning.** With $\kappa=L/m$, the Heavy-ball parameters optimal on quadratics are
--   $$\alpha=\frac{4}{(\sqrt L+\sqrt m)^2},\qquad \beta=\Bigl(\frac{\sqrt\kappa-1}{\sqrt\kappa+1}\Bigr)^2 .$$
--   5. **Recursion (B.1).** A real sequence satisfies (B.1) if $x_{k+2}=\tfrac{13}{9}x_{k+1}-\tfrac49x_k-\tfrac19\nabla f(x_{k+1})$ for every $k\ge 0$, with $\nabla f$ from (4.11).
--   6. **The cycle (B.3).** $p=792/1225$, $q=-2208/1225$, $r=2592/1225$, and $x^\star_k$ equals $p$, $q$, $r$ according as $k\equiv 0,1,2 \pmod 3$. The perturbation of a sequence $x$ is $\varepsilon_k=x_k-x^\star_k$.
--   7. **The perturbation matrix and the margin.**
--   $$P=\begin{bmatrix}-4/3 & -4/9\\ 1 & 0\end{bmatrix},\qquad \bar\varepsilon=r-2=\frac{142}{1225}.$$
--
--   These are the only objects the statements of the mission use.
--
--   **Formalization Note** The page's $S(m,L)$ is defined for $f:\mathbb R^d\to\mathbb R$; here $d=1$ and the domain is $\mathbb R$ itself, with the derivative `deriv f` in place of the gradient and $|\cdot|$ as the norm, which is the same object. The Heavy-ball run is indexed from $x_0$ (index $0$), so the page's $x_{-1}$ does not appear. $\kappa$, $\alpha$ and $\beta$ are written exactly as in Proposition 1 (with `Real.sqrt`), so that the goal is visibly about the tuning optimal for quadratics.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 3 (S(m, L)); p. 5 (Heavy-ball update rule); p. 6 (Proposition 1, last row); p. 23 (4.11); pp. 39–40 (B.1)–(B.3), P and ε̄

import Mathlib

namespace IQCAlg.HeavyBall

/-- The class `S(m, L)` of p. 3 in dimension `d = 1`: `f : ℝ → ℝ` is continuously
differentiable, strongly convex with parameter `m`, and has an `L`-Lipschitz derivative,
with `0 < m < L`. -/
structure InSmL1 (f : ℝ → ℝ) (m L : ℝ) : Prop where
  m_pos : 0 < m
  m_lt_L : m < L
  contDiff : ContDiff ℝ 1 f
  strongConvex : StrongConvexOn Set.univ m f
  lipschitz_deriv : ∀ x y : ℝ, |deriv f x - deriv f y| ≤ L * |x - y|

/-- The piecewise-linear gradient (4.11): `25x` for `x < 1`, `x + 24` for `1 ≤ x < 2`,
`25x − 24` for `x ≥ 2`. -/
noncomputable def gradF (x : ℝ) : ℝ :=
  if x < 1 then 25 * x else if x < 2 then x + 24 else 25 * x - 24

/-- The Heavy-ball run `x_{k+1} = x_k − α g(x_k) + β (x_k − x_{k−1})` (p. 5) with the
initialization `x_{−1} = x_0` (p. 39), indexed from `x_0`: `hbRun g α β x0 k` is `x_k`. -/
noncomputable def hbRun (g : ℝ → ℝ) (α β x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | 1 => x0 - α * g x0
  | k + 2 =>
      hbRun g α β x0 (k + 1) - α * g (hbRun g α β x0 (k + 1))
        + β * (hbRun g α β x0 (k + 1) - hbRun g α β x0 k)

/-- The condition ratio `κ := L / m` (Proposition 1, p. 6). -/
noncomputable def kappa (L m : ℝ) : ℝ := L / m

/-- The Heavy-ball step size of Proposition 1 (p. 6, last row): `α = 4 / (√L + √m)²`. -/
noncomputable def hbAlpha (L m : ℝ) : ℝ := 4 / (Real.sqrt L + Real.sqrt m) ^ 2

/-- The Heavy-ball momentum of Proposition 1 (p. 6, last row):
`β = ((√κ − 1) / (√κ + 1))²`. -/
noncomputable def hbBeta (L m : ℝ) : ℝ :=
  ((Real.sqrt (kappa L m) - 1) / (Real.sqrt (kappa L m) + 1)) ^ 2

/-- A sequence satisfies (B.1): `x_{k+2} = (13/9) x_{k+1} − (4/9) x_k − (1/9) ∇f(x_{k+1})`
for every `k`, with `∇f` the gradient (4.11). -/
def IsB1Traj (x : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, x (k + 2) = 13 / 9 * x (k + 1) - 4 / 9 * x k - 1 / 9 * gradF (x (k + 1))

/-- The limit point `p` of (B.3). -/
noncomputable def pC : ℝ := 792 / 1225
/-- The limit point `q` of (B.3). -/
noncomputable def qC : ℝ := -2208 / 1225
/-- The limit point `r` of (B.3). -/
noncomputable def rC : ℝ := 2592 / 1225

/-- The limit sequence `x⋆_k` of p. 40: `p, q, r, p, q, r, …`. -/
noncomputable def cyc (k : ℕ) : ℝ :=
  if k % 3 = 0 then pC else if k % 3 = 1 then qC else rC

/-- The perturbation `ε_k = x_k − x⋆_k` of a sequence `x` from the cycle (p. 40). -/
noncomputable def eps (x : ℕ → ℝ) (k : ℕ) : ℝ := x k - cyc k

/-- The matrix `P = [[−4/3, −4/9], [1, 0]]` of the perturbation recursion (p. 40). -/
noncomputable def Pm : Matrix (Fin 2) (Fin 2) ℝ := !![-4 / 3, -4 / 9; 1, 0]

/-- `ε̄ = r − 2 = 142/1225`, the distance from the cycle to the nearest transition point
of `f` (p. 40). -/
noncomputable def epsBar : ℝ := 142 / 1225

end IQCAlg.HeavyBall


