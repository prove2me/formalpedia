-- Prove2me | Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
-- name    : SymNormLoad_IsMonotoneSymmetricNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:46.465311+00:00
-- url     : https://prove2.me/theorems/ab48805e-9cf0-4738-adb6-1c952133f305
-- title:
--   Monotone symmetric norm on $\mathbb R^M$
-- statement:
--   A function $\Psi:\mathbb R^M\to\mathbb R$ is a **monotone symmetric norm** if
--
--   1. it is a norm: $\Psi(x)\ge0$, $\Psi(x)=0$ only for $x=0$, $\Psi(ax)=|a|\,\Psi(x)$ for $a\in\mathbb R$, and $\Psi(x+y)\le\Psi(x)+\Psi(y)$;
--   2. it is **symmetric**: $\Psi(x_{\pi(1)},\dots,x_{\pi(M)})=\Psi(x)$ for every permutation $\pi$ of the coordinates;
--   3. it is **monotone** on the nonnegative orthant: $0\le x\le y$ (coordinatewise) implies $\Psi(x)\le\Psi(y)$.
--
--   Examples are the $\ell_q$ norms ($1\le q\le\infty$), the top-$K$ norms and the ordered norms. In the paper, "symmetric norm" always means a monotone symmetric norm; it is the objective $\Psi(L)$ applied to the machine-load vector $L$.
--
--   **Formalization Note** $\Psi$ is a plain function on `Fin M → ℝ` with the axioms above as fields; Mathlib's norm on `Fin M → ℝ` (the sup norm) is never used. Monotonicity is required only on the orthant, as in the paper; no sign invariance, continuity or normalization is assumed.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 1.1 "Symmetric norms", p.3

import Mathlib

namespace SymNormLoad

/-- **Monotone symmetric norm.** Chen–Im–Sirri, *Online Load Balancing under Symmetric Norms*,
manuscript (STOC 2027 submission), §1.1 "Symmetric norms", p.3: a norm `Ψ : ℝ^M → ℝ_{≥0}` is
*symmetric* if it is invariant under coordinate permutations, and *monotone* if `0 ≤ x ≤ y`
implies `Ψ(x) ≤ Ψ(y)`; the paper's "symmetric norm" means a monotone symmetric norm.

**Formalization Note** `Ψ` is a plain function `(Fin M → ℝ) → ℝ` and the norm axioms are the
fields below (nonnegativity, definiteness, absolute homogeneity, triangle inequality); it is
never Mathlib's sup norm on `Fin M → ℝ`. Machines are indexed by `Fin M` (0-based). The order on
`Fin M → ℝ` is pointwise. Monotonicity is only required on the nonnegative orthant, as on p.3;
no sign invariance, continuity or normalization is assumed. -/
structure IsMonotoneSymmetricNorm {M : ℕ} (Ψ : (Fin M → ℝ) → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ Ψ x
  eq_zero : ∀ x, Ψ x = 0 → x = 0
  smul : ∀ (a : ℝ) (x : Fin M → ℝ), Ψ (a • x) = |a| * Ψ x
  triangle : ∀ x y, Ψ (x + y) ≤ Ψ x + Ψ y
  perm : ∀ (σ : Equiv.Perm (Fin M)) (x : Fin M → ℝ), Ψ (x ∘ σ) = Ψ x
  mono : ∀ x y : Fin M → ℝ, 0 ≤ x → x ≤ y → Ψ x ≤ Ψ y

end SymNormLoad


