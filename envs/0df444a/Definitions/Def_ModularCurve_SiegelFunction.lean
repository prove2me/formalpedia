-- Prove2me | Definitions.Def_ModularCurve_SiegelFunction
-- name    : ModularCurve_SiegelFunction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/33e410c1-f37e-5b55-99c8-baca633e37b4
-- title:
--   Siegel functions of level N as q-products
-- statement:
--   For a natural number $N$, integers $r,s$ and a complex number $z$, [`ModularCurve.siegelFun N r s z`](../def/ModularCurve_SiegelFunction.html#L10) is the explicit product
--   $$-e^{\pi i s(r-N)/N^{2}}\; e^{\pi i\left((r/N)^{2}-r/N+1/6\right)z}\;\bigl(1-q_a\bigr)\prod_{n\ge 0}\bigl(1-q^{\,n+1}q_a\bigr)\bigl(1-q^{\,n+1}q_a^{-1}\bigr),$$
--   where $q=e^{2\pi i z}$ and $q_a=e^{2\pi i (rz+s)/N}$, and where the inner power $q^{n+1}$ is literally $e^{2\pi i z}$ raised to the natural-number exponent $n+1$. Writing $a=(a_1,a_2)=(r/N,s/N)$, the first exponential is $-e^{2\pi i a_2(a_1-1)/2}$, the second is $q^{B_2(a_1)/2}$ with $B_2(x)=x^{2}-x+1/6$ the second Bernoulli polynomial, and $q_a=e^{2\pi i(a_1z+a_2)}$; thus the definition is the classical Siegel function $g_a$ in the Kubert–Lang normalisation, indexed by a pair of integers rather than by a reduced residue pair, so $r$ and $s$ are not taken modulo $N$.
--
--   The function is defined for every $z\in\mathbb{C}$, with no hypothesis on $N$, $r$, $s$; the infinite product is Mathlib's unconditional `∏'`, which agrees with the usual limit exactly when the factors form a multipliable family, as happens for $z$ in the upper half-plane, where the product converges absolutely. Since the divisions are field divisions, the case $N=0$ degenerates: the factor $1-e^{2\pi i(rz+s)/N}$ becomes $1-e^{0}=0$, so `siegelFun 0 r s z = 0` for all $r,s,z$. The companion declaration [`ModularCurve.siegelFun_def`](../def/ModularCurve_SiegelFunction.html#L19) records the defining identity as an equation available for rewriting. No analytic property (modularity of $g_a^{12N}$, the relation to Klein forms and $\eta^2$, absence of zeros and poles on the upper half-plane) is asserted here; only the $q$-product itself is fixed.
--
--   **Relation to Mathlib.** Mathlib has no Siegel or Klein functions; this is the project's own definition, built from Mathlib's `Complex.exp` and its unconditional infinite product `∏'`.
--
--   **Where it is used.** This explicit $q$-product is the basic analytic object in the project's development of modular units of level $N$ on modular curves, and is imported by the modules that establish their transformation and divisor properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_SiegelFunction.lean

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def siegelFun (N : ℕ) (r s : ℤ) (z : ℂ) : ℂ :=
  -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
    (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
    ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
        Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
      (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
        (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹))

theorem siegelFun_def (N : ℕ) (r s : ℤ) (z : ℂ) :
    siegelFun N r s z =
      -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
        ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
            Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
          (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
            (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹)) :=
  rfl

end ModularCurve

end


