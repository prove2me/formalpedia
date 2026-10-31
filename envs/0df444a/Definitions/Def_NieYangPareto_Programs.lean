-- Prove2me | Definitions.Def_NieYangPareto_Programs
-- name    : NieYangPareto_Programs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:35.863985+00:00
-- url     : https://prove2.me/theorems/70fb2237-15cd-45b3-95ae-a4edf1cd7f4c
-- title:
--   The programs (3.2), (3.3) and their optimal values $\omega^*$, $t^*$
-- statement:
--   Fix $v\in\mathbb R^m$. The linear optimization (3.2) in $w_0\in\mathbb R$ and $w\in\mathbb R^m$ is
--
--   $$
--   \omega^*:=\max\ w_0\quad\text{s.t.}\quad 1-e^Tw=0,\quad w_i\ge w_0\ (i\in[m]),\quad \sum_{i=1}^m w_i(f_i(x)-v_i)\ge0\ \text{ on }K.
--   $$
--
--   Its dual (3.3) in $t\in\mathbb R$ and a tms $y$ of degree $d$, the maximum degree of the objectives, is
--
--   $$
--   t^*:=\min\ t\quad\text{s.t.}\quad t-\langle f_i-v_i,y\rangle\ge0\ (i\in[m]),\quad 1=mt-\sum_{i=1}^m\langle f_i-v_i,y\rangle,\quad y\in\operatorname{cl}(\mathscr R_d(K)).
--   $$
--
--   These programs carry the paper's proof of Theorem 3.2.
--
--   **Formalization Note** The optimal values are a supremum and an infimum in `EReal`, so $\omega^*=-\infty$ exactly when (3.2) is infeasible and $t^*=+\infty$ when (3.3) is infeasible. No attainment is built in. The vector $v$ is arbitrary, since the proof of Theorem 3.2 uses the programs for arbitrary $v$, although §3.2 introduces them for $v\in f(K)$.
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, eqs. (3.2), (3.3), p.8

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_MOP_V

namespace NieYangPareto

open MvPolynomial

variable {n m : ℕ} {E I : Type*}

/-- The feasible set of the linear optimization (3.2) in `(w₀, w) ∈ ℝ × ℝ^m`: Nie–Yang,
arXiv:2108.04336v2, eq. (3.2), p.8: `1 - eᵀw = 0`, `w_i ≥ w₀ (i ∈ [m])`, and
`Σ_i w_i (f_i(x) - v_i) ≥ 0` on `K`.

**Formalization Note** `v` ranges over all of `ℝ^m`, because the proof of Theorem 3.2 (p.9) applies
(3.2) to arbitrary `v`, although §3.2 introduces it for `v ∈ f(K)`. -/
def MOP.feasible32 (P : MOP n m E I) (v : Fin m → ℝ) : Set (ℝ × (Fin m → ℝ)) :=
  {p | 1 - ∑ i, p.2 i = 0 ∧ (∀ i, p.1 ≤ p.2 i) ∧
    ∀ x ∈ P.K, 0 ≤ ∑ i, p.2 i * (P.obj x i - v i)}

/-- The optimal value `ω*` of (3.2): Nie–Yang, arXiv:2108.04336v2, eq. (3.2), p.8.

**Formalization Note** The page's "max" is a supremum in `EReal`, so that `ω* = ⊥` exactly when
(3.2) is infeasible. -/
noncomputable def MOP.omegaStar (P : MOP n m E I) (v : Fin m → ℝ) : EReal :=
  sSup ((fun p : ℝ × (Fin m → ℝ) => (p.1 : EReal)) '' P.feasible32 v)

/-- The feasible set of the dual program (3.3) in `(t, y)`: Nie–Yang, arXiv:2108.04336v2, eq. (3.3),
p.8: `t - ⟨f_i - v_i, y⟩ ≥ 0 (i ∈ [m])`, `1 = mt - Σ_i ⟨f_i - v_i, y⟩`, `y ∈ cl(ℛ_d(K))`.

**Formalization Note** The polynomial `f_i - v_i` is `P.f i - C (v i)`, of degree at most `d`. -/
noncomputable def MOP.feasible33 (P : MOP n m E I) (v : Fin m → ℝ) : Set (ℝ × Tms n P.d) :=
  {q | (∀ i, 0 ≤ q.1 - pair (P.f i - C (v i)) q.2) ∧
    1 = (m : ℝ) * q.1 - ∑ i, pair (P.f i - C (v i)) q.2 ∧
    q.2 ∈ closure (momentCone P.K P.d)}

/-- The optimal value `t*` of (3.3): Nie–Yang, arXiv:2108.04336v2, eq. (3.3), p.8.

**Formalization Note** The page's "min" is an infimum in `EReal`, with `t* = ⊥` when (3.3) is
unbounded below. No attainment is claimed. -/
noncomputable def MOP.tStar (P : MOP n m E I) (v : Fin m → ℝ) : EReal :=
  sInf ((fun q : ℝ × Tms n P.d => (q.1 : EReal)) '' P.feasible33 v)

end NieYangPareto


