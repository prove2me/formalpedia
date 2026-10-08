-- Prove2me | Definitions.Def_SpikedWishart_SoftEdge_Airy
-- name    : SpikedWishart_SoftEdge_Airy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:38:25.209598+00:00
-- url     : https://prove2.me/theorems/2e4ee5fd-0d87-492e-81d0-133235086202
-- title:
--   §1.2.1, pp. 1646–1647; (201) — Airy function, Airy kernel (12), s^{(m)}, t^{(m)}, Fredholm series and F_k
-- statement:
--   This file defines the limit laws $F_k$ of the soft-edge regime, from the Airy function up.
--
--   For a vertex $c\in\mathbb C$ and angles $\theta_{\rm in},\theta_{\rm out}$, the **ray integral** of $\varphi$ is the integral along the broken line coming in from $\infty e^{i\theta_{\rm in}}$ to $c$ and going out to $\infty e^{i\theta_{\rm out}}$:
--   $$
--   \int_0^\infty \varphi(c+te^{i\theta_{\rm out}})\,e^{i\theta_{\rm out}}\,dt-\int_0^\infty \varphi(c+te^{i\theta_{\rm in}})\,e^{i\theta_{\rm in}}\,dt .
--   $$
--
--   1. The **Airy function** (10): $\mathrm{Ai}(u)=\frac1{2\pi}\int e^{iua+\frac i3a^3}\,da$ along the contour from $\infty e^{5i\pi/6}$ to $\infty e^{i\pi/6}$ (vertex $0$).
--   2. The **Airy kernel**, in the form (12): $A(u,v)=\int_0^\infty \mathrm{Ai}(u+z)\,\mathrm{Ai}(z+v)\,dz$.
--   3. For $m\ge1$, (13): $s^{(m)}(u)=\frac1{2\pi}\int e^{iua+\frac i3a^3}\frac{1}{(ia)^m}\,da$ along the same pair of directions, with vertex $-i$ so that the pole $a=0$ lies above the contour.
--   4. For $m\ge1$, (14): $t^{(m)}(v)=\frac1{2\pi}\int e^{iva+\frac i3a^3}(-ia)^{m-1}\,da$ (vertex $0$).
--   5. The **Fredholm determinant** of a kernel $K$ on $L^2((x,\infty))$, as its Fredholm series
--   $$
--   \det(1-K)_{L^2((x,\infty))}=\sum_{n=0}^\infty\frac{(-1)^n}{n!}\int_{(x,\infty)^n}\det\big[K(u_i,u_j)\big]_{i,j=1}^n\,du_1\cdots du_n .
--   $$
--   6. The distribution functions
--   $$
--   F_k(x)=\det\Big(1-A-\sum_{m=1}^k s^{(m)}\otimes t^{(m)}\Big)_{L^2((x,\infty))},
--   $$
--   i.e. the Fredholm series of the kernel $A(u,v)+\sum_{m=1}^k s^{(m)}(u)\,t^{(m)}(v)$. For $k=0$ this is $F_0(x)=\det(1-A_x)$, the GUE Tracy–Widom distribution.
--
--   These are the limits in Theorem 1.1(a): $F_k$ is the law of the rescaled largest sample eigenvalue when exactly $k$ population eigenvalues sit at the critical value $1+\gamma^{-1}$.
--
--   **Formalization Note** The paper defines $F_k$ by the resolvent formula (17) of Definition 1.1; its proof (pp. 1676–1677) shows that the limit is the finite-rank-perturbation determinant (201), and that (201) equals (17) by (202) and Lemma 3.3. Here $F_k$ is defined by (201) directly, without the conjugation by $e^{-\varepsilon u}$, which does not change any finite determinant $\det[K(u_i,u_j)]$. The Airy kernel is defined by (12), not by the divided difference (11), whose diagonal would be the junk value $0$; the identity (11) = (12) is a milestone. The contour integrals are Bochner integrals along rays where the integrands decay like $e^{-t^3/3}$; $\mathrm{Ai}$, $s^{(m)}$, $t^{(m)}$ are the real parts of these (real-valued) integrals. If the Fredholm series were not summable its Lean value would be $0$; summability is part of the Lemma 3.3 milestone.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1646–1647, §1.2.1, (10)–(14), Definition 1.1; p. 1676, (201)

import Mathlib

namespace SpikedWishart.SoftEdge

open MeasureTheory Complex

/-- Integral of `φ` along the broken line that comes in from `∞·e^{iθin}` to the vertex `c` and goes
back out to `∞·e^{iθout}`: the outgoing ray `c + t e^{iθout}` minus the ray `c + t e^{iθin}`
(traversed inwards), `t > 0`. -/
noncomputable def rayIntegral (c : ℂ) (θin θout : ℝ) (φ : ℂ → ℂ) : ℂ :=
  (∫ t in Set.Ioi (0 : ℝ), φ (c + (t : ℂ) * exp ((θout : ℂ) * I)) * exp ((θout : ℂ) * I)) -
    ∫ t in Set.Ioi (0 : ℝ), φ (c + (t : ℂ) * exp ((θin : ℂ) * I)) * exp ((θin : ℂ) * I)

/-- The Airy function, (10): `Ai(u) = (1/2π) ∫ e^{iua + i a³/3} da` on the contour from
`∞e^{5iπ/6}` to `∞e^{iπ/6}` (vertex `0`); real part taken (the integral is real). -/
noncomputable def Ai (u : ℝ) : ℝ :=
  ((1 / (2 * (Real.pi : ℂ))) *
    rayIntegral 0 (5 * Real.pi / 6) (Real.pi / 6)
      (fun a => exp (I * (u : ℂ) * a + I * a ^ 3 / 3))).re

/-- The Airy kernel in the form (12): `A(u, v) = ∫₀^∞ Ai(u + z) Ai(z + v) dz`. -/
noncomputable def airyKernel (u v : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), Ai (u + z) * Ai (z + v)

/-- `s^{(m)}(u)`, (13): `(1/2π) ∫ e^{iua + i a³/3} (ia)^{-m} da` on the contour from `∞e^{5iπ/6}`
to `∞e^{iπ/6}` with vertex `-i`, so that `a = 0` lies above the contour; real part taken. -/
noncomputable def sFn (m : ℕ) (u : ℝ) : ℝ :=
  ((1 / (2 * (Real.pi : ℂ))) *
    rayIntegral (-I) (5 * Real.pi / 6) (Real.pi / 6)
      (fun a => exp (I * (u : ℂ) * a + I * a ^ 3 / 3) / (I * a) ^ m)).re

/-- `t^{(m)}(v)`, (14): `(1/2π) ∫ e^{iva + i a³/3} (-ia)^{m-1} da` on the contour from
`∞e^{5iπ/6}` to `∞e^{iπ/6}` (vertex `0`); real part taken. Used for `m ≥ 1`. -/
noncomputable def tFn (m : ℕ) (v : ℝ) : ℝ :=
  ((1 / (2 * (Real.pi : ℂ))) *
    rayIntegral 0 (5 * Real.pi / 6) (Real.pi / 6)
      (fun a => exp (I * (v : ℂ) * a + I * a ^ 3 / 3) * (-I * a) ^ (m - 1))).re

/-- The Fredholm determinant `det(1 - K)` on `L²((x, ∞))`, as its Fredholm series
`Σ_n (-1)^n/n! ∫_{(x,∞)^n} det[K(u_i, u_j)]_{i,j<n} du`. -/
noncomputable def fredholmDet (K : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((-1 : ℝ) ^ n / (n.factorial : ℝ)) *
    ∫ u in Set.pi Set.univ (fun _ : Fin n => Set.Ioi x),
      (Matrix.of fun i j : Fin n => K (u i) (u j)).det

/-- The kernel of `F_k`: the Airy kernel plus the rank-`k` perturbation `Σ_{m=1}^k s^{(m)} ⊗ t^{(m)}`
of (201). -/
noncomputable def kernelFk (k : ℕ) (u v : ℝ) : ℝ :=
  airyKernel u v + ∑ m ∈ Finset.Icc 1 k, sFn m u * tFn m v

/-- `F_k(x)` (Definition 1.1, in the form (201)): `det(1 - A_x - Σ_{m=1}^k s^{(m)} ⊗ t^{(m)})` on
`L²((x, ∞))`. `F_0(x) = det(1 - A_x)` is the GUE Tracy–Widom distribution. -/
noncomputable def F (k : ℕ) (x : ℝ) : ℝ :=
  fredholmDet (kernelFk k) x

end SpikedWishart.SoftEdge


