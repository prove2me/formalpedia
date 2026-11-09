-- Prove2me | Definitions.Def_KSPolySign_pot
-- name    : KSPolySign_pot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:35:46.991313+00:00
-- url     : https://prove2.me/theorems/07276d60-1e50-4bf5-a30a-33c9878613be
-- title:
--   The matrix potential $P(y)$
-- statement:
--   For a parameter $\rho>0$ and $y\in[-1,1]^k$, the **matrix potential** is
--   $$P(y) = \min_{b\in\mathbb R,\ U,V\succ0}\ b + \rho\,\mathrm{tr}[U+V]\quad\text{subject to}\quad U^{-1}+M(y)+K_y(V)\preceq bI,\ \ V^{-1}-M(y)+K_y(U)\preceq bI.$$
--   It upper-bounds $\|M(y)\|$ (Lemma 3.4) and is the quantity the signing procedure drives down.
--
--   **Formalization Note** Written as the infimum of the objective over the feasible points. For $n\ge1$ the set of values is nonempty and bounded below by $0$, and Lemma 3.7(a) shows the infimum is attained. For $n=0$ the value is a meaningless default; all statements assume $n\ge1$.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.3, p.18 (PDF p.18); Definition 3.5, p.19 (PDF p.19)

import Mathlib
import Definitions.Def_KSPolySign_Feasible
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The matrix potential `P(y)`.**
`P(y) = min_{b ∈ ℝ, U, V ≻ 0} b + ρ tr[U + V]` over the feasible points of Definition 3.3.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.3, p.18 (PDF p.18); Definition 3.5, p.19 (PDF p.19).

**Formalization Note** Written as the infimum (`sInf`) of the objective values of feasible points.
For `n ≥ 1`, `ρ > 0` and `y ∈ [−1, 1]^k` this set is nonempty (`U = V = I` with `b` large) and
bounded below by `0` (Lemma 3.4(b)), so `sInf` is the true infimum; Lemma 3.7(a) shows it is
attained. For `n = 0` the set is all of `ℝ` and the value is Lean's junk `0`; every statement using
the potential assumes `n ≥ 1`. The trace of the Hermitian matrix `U + V` is real; its real part is
taken. -/
noncomputable def pot {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℝ) (y : Fin k → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ),
    Feasible C F y b U V ∧ v = b + ρ * (U + V).trace.re}

end KSPolySign


