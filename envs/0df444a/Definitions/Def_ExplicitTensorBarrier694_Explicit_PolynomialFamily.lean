-- Prove2me | Definitions.Def_ExplicitTensorBarrier694_Explicit_PolynomialFamily
-- name    : ExplicitTensorBarrier694_Explicit_PolynomialFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:39.688442+00:00
-- url     : https://prove2.me/theorems/c662df07-d2fb-48c4-91dd-c80176941dda
-- title:
--   Definition 3.2 — polynomial tensor and central Koszul family
-- statement:
--   Let $e\ge2$, $s=2e-1$, and let $f_1,\ldots,f_s\in\mathbb C[t]$ be monic polynomials with pairwise distinct degrees strictly below $e^2$. In the standard bases define
--
--   $$Q_f(t)_{\ell uv}=f_\ell(2^{u+v}t),\qquad M_f(t)=K_{e-1}(Q_f(t)).$$
--
--   The nullity is $\dim_{\mathbb C}\ker M_f(t)$, for arbitrary $t\in\mathbb C$. Monicity excludes the zero polynomial, so the natural-number polynomial degree represents the ordinary degree without ambiguity. Polynomial labels are reindexed by $\{0,\ldots,s-1\}$; $u,v$ already range from $0$ to $e-1$ in the source. The matrix is square of size $e\binom{s}{e-1}$ on the stated domain. These objects support the full nullity-sum result, without a determinant-nonvanishing assumption.
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Definition 3.2, p.8 (PDF p.8) and Section 3 standing assumptions p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Koszul

open scoped BigOperators

namespace ExplicitTensorBarrier694.Explicit

/-- The full hypotheses in Definition 3.2, p.8. Monicity excludes zero, so
natDegree is the ordinary degree and distinct natDegrees means distinct degrees. -/
def PolynomialData (e : ℕ) (f : Fin (2 * e - 1) → Polynomial ℂ) : Prop :=
  (∀ l, (f l).Monic) ∧ Function.Injective (fun l => (f l).natDegree) ∧
    ∀ l, (f l).natDegree < e ^ 2

/-- Q_f(t), Definition 3.2. The one-based polynomial index is relabeled by Fin s;
u and v were already zero-based in the source, so powers are unchanged. -/
noncomputable def polynomialTensor {e : ℕ}
    (f : Fin (2 * e - 1) → Polynomial ℂ) (t : ℂ) : Tensor (2 * e - 1) e e :=
  fun l u v => (f l).eval ((2 : ℂ) ^ (u.val + v.val) * t)

/-- M_f(t) is exactly K_{e-1}(Q_f(t)). -/
noncomputable def polynomialKoszul {e : ℕ}
    (f : Fin (2 * e - 1) → Polynomial ℂ) (t : ℂ) :=
  koszul (e - 1) (polynomialTensor f t)

/-- Actual dimension of the kernel, not just an indicator of singularity. -/
noncomputable def polynomialNullity {e : ℕ}
    (f : Fin (2 * e - 1) → Polynomial ℂ) (t : ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (polynomialKoszul f t).mulVecLin)

end ExplicitTensorBarrier694.Explicit


