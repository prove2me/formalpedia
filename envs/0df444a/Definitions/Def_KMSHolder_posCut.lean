-- Prove2me | Definitions.Def_KMSHolder_posCut
-- name    : KMSHolder_posCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:05.879105+00:00
-- url     : https://prove2.me/theorems/5fa2ed7e-b44d-47af-aefc-86816b2ab8c6
-- title:
--   Cut-off $u \mapsto \min(1, Nu^+)\,\mathrm{clamp}(u, 1/N, N)^z$
-- statement:
--   For $n \in \mathbb N$, $N = n + 1$ and $z \in \mathbb C$ let
--
--   $$
--   c_{N,z}(u) = \min(1, N u^+) \cdot \big(\max(1/N, \min(N, u))\big)^z, \qquad u^+ = \max(u, 0),
--   $$
--
--   with the principal complex power of a positive real. It is a bounded continuous function on $\mathbb R$ that vanishes for $u \le 0$. As $N \to \infty$ it tends to $u^z$ for $u > 0$ and to $0$ for $u \le 0$, and for $\Re z \ge 0$ the family is dominated by $\max(1, u^{\Re z})$ on $u > 0$.
--
--   Applied through the functional calculus of a positive operator $T$ these cut-offs approximate $T^z$ with the **support convention** $T^z = 0$ on $\ker T$ (so $T^0$ is the support projection of $T$), the convention of Araki and Masuda for powers of relative modular operators of non-faithful functionals.
--
--   **Formalization Note** Because the first factor vanishes at $u \le 0$, Lean's convention $0^0 = 1$ for complex powers never enters.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §3, pp.4–6 (powers Δ^z_{φ,Ω})

import Mathlib

namespace KMSHolder

/-- The cut-off `u ↦ min(1, N·u⁺) · clamp(u, 1/N, N)^z` with `N = n + 1` and `u⁺ = max(u, 0)`, a
bounded continuous function on `ℝ` for every `z ∈ ℂ` (complex power of a positive real).

As `N → ∞` it converges pointwise to `u ↦ u^z` for `u > 0` and to `0` for `u ≤ 0`; for `ℜz ≥ 0`
it is dominated by `max(1, u^{ℜz})` on `u > 0`. Applied through the calculus of a positive
operator `T` it approximates `T^z` with the **support convention** `T^z = 0` on `ker T` (so `T⁰`
is the support projection), Araki–Masuda's convention for `Δ^z_{φ,Ω}` when `φ` is not faithful
(Jäkel–Robl, arXiv:1103.3608v2, §3, pp.4–6). At `u ≤ 0` the first factor vanishes, so Lean's
`0 ^ (0 : ℂ) = 1` never enters. -/
noncomputable def posCut (n : ℕ) (z : ℂ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
      (fun u : ℝ => ((min 1 (((n : ℝ) + 1) * max u 0) : ℝ) : ℂ))
      (by fun_prop) 1
      (by
        intro u
        have h0 : 0 ≤ ((n : ℝ) + 1) * max u 0 :=
          mul_nonneg (by positivity) (le_max_right _ _)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one h0)]
        exact min_le_left _ _) *
    (BoundedContinuousFunction.mkOfCompact
        (⟨fun x : Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) => (((x : ℝ) : ℂ)) ^ z,
          by
            apply Continuous.cpow (by fun_prop) continuous_const
            intro x
            apply Complex.ofReal_mem_slitPlane.2
            exact lt_of_lt_of_le (by positivity) x.2.1⟩ :
          C(Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1), ℂ))).compContinuous
      ⟨Set.projIcc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
          (by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [Nat.cast_nonneg (α := ℝ) n]),
        continuous_projIcc⟩

end KMSHolder


