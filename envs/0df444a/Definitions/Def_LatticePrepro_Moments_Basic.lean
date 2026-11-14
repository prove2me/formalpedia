-- Prove2me | Definitions.Def_LatticePrepro_Moments_Basic
-- name    : LatticePrepro_Moments_Basic
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:16.285357+00:00
-- url     : https://prove2.me/theorems/a333c663-8521-4bc9-9622-9101e3596272
-- title:
--   Coefficient functions and their moments (Definitions 4.1–4.2)
-- statement:
--   Let $F$ be a commutative ring and $\Omega$ a commutative $F$-algebra. In the paper, $F = \mathbb{F}_p$ is the prime field and $\Omega$ is an extension field of the moment field.
--
--   - **Coefficient functions** (Definition 4.1) are finitely supported functions $f\colon \Omega \to F$; the support $\operatorname{supp} f = \{\alpha \in \Omega : f(\alpha) \ne 0\}$ is finite.
--   - **Moments** (`moment`, Definition 4.2). For an integer $k \ge 0$, the $k$-th moment of $f$ is
--   $$\mathcal M_k(f) = \sum_{\alpha \in \operatorname{supp} f} f(\alpha)\cdot \alpha^k \ \in \Omega,$$
--   where $f(\alpha)\cdot\alpha^k$ is the scalar multiplication of $F$ on $\Omega$, with the convention $0^0 = 1$.
--
--   The bundle also records two evaluation rules: the zero function has all moments $0$, and the function equal to $c$ at a single point $\alpha$ and $0$ elsewhere has $\mathcal M_k = c \cdot \alpha^k$. In particular the indicator $\mathbf{1}_\alpha$ has moments $\alpha^k$, as noted after Definition 4.2.
--
--   Moments connect evaluation tables to field elements. A moment representation (Definition 4.4) requires the moment maps of light evaluation tables to agree with the moments of sparse coefficient functions, and the soundness proof of Theorem 4.6 recovers an accepting assignment from coefficient functions through their moments.
--
--   **Formalization Note**: Coefficient functions are Mathlib's finitely supported functions `Ω →₀ F`, and `moment f k` is `f.sum (fun α c => c • α ^ k)`. In the paper coefficient functions live on varying finite extensions; the formalization uses one fixed extension field $\Omega$ throughout. The simp lemmas `moment_zero` and `moment_single` are included in the bundle.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definitions 4.1–4.2 (\label{def:coefficient-functions}, \label{def:coefficient-moments}); Lean: LatticePrepro/Moments/Basic.lean, LatticePrepro.moment

import Mathlib

/-!
# Coefficient functions and moments

A *coefficient function* (Definition 4.1 of the paper) is a finitely supported function from a
field `Ω` to a coefficient ring `F` (in the paper, the prime field `𝔽_p`). We model it as a
`Finsupp` `Ω →₀ F`. Its `k`-th moment (Definition 4.2) is `∑ α, f α • α ^ k ∈ Ω`.

The main facts proved here are:
* `moment` is `F`-linear (`momentₗ`);
* the Vandermonde identification lemma (Lemma 4.3): a function supported on at most `t` points
  whose first `t` moments vanish is zero;
* the binomial identity for the moments of a translation difference (equation (20)).
-/

namespace LatticePrepro

open Finsupp

section Moment

variable {F Ω : Type*} [CommRing F] [CommRing Ω] [Algebra F Ω]

/-- The `k`-th moment `∑ α, f α • α ^ k` of a finitely supported `f : Ω →₀ F`
(Definition 4.2; with the convention `0 ^ 0 = 1`). -/
noncomputable def moment (f : Ω →₀ F) (k : ℕ) : Ω :=
  f.sum fun α c => c • α ^ k

@[simp] lemma moment_zero (k : ℕ) : moment (0 : Ω →₀ F) k = 0 := by
  simp [moment]

@[simp] lemma moment_single (α : Ω) (c : F) (k : ℕ) :
    moment (single α c) k = c • α ^ k := by
  simp [moment, sum_single_index]

end Moment

end LatticePrepro


