-- Prove2me | Definitions.Def_TRSHolderKL_IsKZeroInf
-- name    : TRSHolderKL_IsKZeroInf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:47.289981+00:00
-- url     : https://prove2.me/theorems/1d6894b4-54c4-4056-b806-da174a42f052
-- title:
--   The desingularizing class $\mathcal K(0,+\infty)$
-- statement:
--   $$
--   \mathcal K(0,+\infty)=\{\varphi\in C^0[0,+\infty)\cap C^1(0,+\infty):\ \varphi(0)=0,\ \varphi\text{ concave},\ \varphi'>0\}.
--   $$
--   A typical member is $\varphi(s)=\tau s^\rho$ with $\tau>0$, $\rho\in(0,1]$, which is how Lemma 4.1 turns a Hölderian error bound into a KL inequality.
--
--   **Formalization Note** $\varphi:\mathbb R\to\mathbb R$; only its values on $[0,+\infty)$ matter. Continuity and concavity are on $[0,+\infty)$; $C^1$ and $\varphi'>0$ are on $(0,+\infty)$.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 4.1, p.14

import Mathlib

namespace TRSHolderKL

/-- The class `𝒦(0, +∞)` of Jiang and Li, arXiv:1911.11955v2, Lemma 4.1, p.14 (from
Bolte et al., Corollary 6): `φ ∈ C⁰[0, +∞) ∩ C¹(0, +∞)`, `φ(0) = 0`, `φ` concave and
`φ′ > 0`.

**Formalization Note.** `φ : ℝ → ℝ`; only its values on `[0, +∞)` matter. Concavity is on
`[0, +∞)` and `φ′ > 0` on `(0, +∞)`, where `φ` is `C¹`. -/
def IsKZeroInf (φ : ℝ → ℝ) : Prop :=
  ContinuousOn φ (Set.Ici 0) ∧ ContDiffOn ℝ 1 φ (Set.Ioi 0) ∧ φ 0 = 0 ∧
    ConcaveOn ℝ (Set.Ici 0) φ ∧ ∀ s : ℝ, 0 < s → 0 < deriv φ s

end TRSHolderKL


