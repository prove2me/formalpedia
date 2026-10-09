-- Prove2me | Definitions.Def_LasserreFC_Generic_Cond43
-- name    : LasserreFC_Generic_Cond43
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:28.875696+00:00
-- url     : https://prove2.me/theorems/dc5ce307-16aa-4ef4-96e5-015270525f50
-- title:
--   Condition 4.3, p. 14 — the nonvanishing conditions (a)–(d) on the input polynomials
-- statement:
--   Condition 4.3 of Nie's paper lists the polynomials in the coefficients of $(f,h,g)$ whose nonvanishing makes the classical optimality conditions hold at every local minimizer. Here each item is stated through the defining property of its polynomial.
--
--   Let $m_1\le n$ and $(f,h,g)$ be admissible for the degrees $d_0$, $d_i$, $d'_j$. For $J\subseteq[m_2]$ write $(h_1,\dots,h_{m_1},g_j\ (j\in J))$ for the constraint tuple, homogenised at the nominal degrees $d_i$, $d'_j$.
--
--   1. **(a)** For every $J$ with $|J|=n-m_1+1$, the forms $\tilde h_1,\dots,\tilde h_{m_1},\tilde g_j$ ($j\in J$) have no common zero $0\neq\tilde x\in\mathbb C^{n+1}$ (the page: $\mathrm{Res}(h_1,\dots,h_{m_1},g_{j_1},\dots,g_{j_{n-m_1+1}})\neq0$).
--   2. **(b)** For every $J$ with $|J|\le n-m_1$, there is no $0\neq\tilde x\in\mathbb C^{n+1}$ at which all of these forms vanish and their gradients in $\tilde x$ have rank $<m_1+|J|$ (the page: $\Delta(h_1,\dots,h_{m_1},g_{j_1},\dots,g_{j_r})\neq 0$, by (2.1)).
--   3. **(c)** For every $J$ with $|J|\le n-m_1$ and every choice of one polynomial $q$ of the tuple, the system (4.5) for $p_0=f$, the remaining polynomials of the tuple, and $q$ has no solution (the page: $\mathscr R(f,p_1,\dots,p_k;p_{k+1})\neq0$ for every re-ordering).
--   4. **(d)** For every $J$ with $|J|\le n-m_1$, the system (4.10) for $(f,h_1,\dots,h_{m_1},g_j\ (j\in J))$ has no solution (the page: $\mathscr D(f,h_1,\dots,h_{m_1},g_{j_1},\dots,g_{j_r})\neq0$).
--
--   Condition 4.3 is the conjunction of (a)–(d).
--
--   **Formalization Note** The page writes each item as the nonvanishing of a resultant $\mathrm{Res}$, a discriminant $\Delta$ (§2.4), or of $\mathscr R$ from (4.6) and $\mathscr D$ from (4.11). Each of these polynomials vanishes exactly when the corresponding complex projective system is solvable (§2.4 for Res and Δ; Propositions 4.1 and 4.2 for $\mathscr R$, $\mathscr D$), so each item is stated as the unsolvability of that system. The re-ordering in (c) matters only through which polynomial plays $q$. Item (a) is vacuous when $m_1+m_2<n+1$, as on the page. The standing assumption $m_1\le n$ is a hypothesis of the theorems that use the condition.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 14, Condition 4.3; p. 5, §2.4 (Res, Δ, (2.1)); pp. 11–12, (4.6), (4.11)

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting
import Definitions.Def_LasserreFC_Generic_Homog

namespace LasserreFC.Generic

open MvPolynomial Matrix

variable {n m1 m2 : ℕ}

/-- The constraint tuple `(h₁, …, h_{m₁}, g_j (j ∈ J))` for `J ⊆ [m₂]`, indexed by `Fin m₁ ⊕ J`. -/
noncomputable def consPoly (P : POP n m1 m2) (J : Finset (Fin m2)) :
    Fin m1 ⊕ J → MvPolynomial (Fin n) ℝ :=
  Sum.elim P.h (fun j => P.g j.1)

/-- The nominal degrees `(d₁, …, d_{m₁}, d'_j (j ∈ J))` of `consPoly P J`. -/
def consDeg (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (J : Finset (Fin m2)) : Fin m1 ⊕ J → ℕ :=
  Sum.elim d (fun j => d' j.1)

/-- Condition 4.3 (a), p. 14, through the defining property of `Res` (§2.4, p. 5): for every
`J ⊆ [m₂]` with `|J| = n − m₁ + 1`, the homogenised `h̃₁, …, h̃_{m₁}, g̃_j (j ∈ J)` have no common
zero `0 ≠ x̃ ∈ ℂ^{n+1}`. (Vacuous when `m₁ + m₂ < n + 1`.) -/
def Cond43a (P : POP n m1 m2) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) : Prop :=
  ∀ J : Finset (Fin m2), J.card = n - m1 + 1 →
    ¬ ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
      ∀ e, eval xt (homog (consDeg d d' J e) (consPoly P J e)) = 0

/-- Condition 4.3 (b), p. 14, through the defining property (2.1) of `Δ` (§2.4, p. 5): for every
`J ⊆ [m₂]` with `|J| ≤ n − m₁`, there is no `0 ≠ x̃ ∈ ℂ^{n+1}` at which all of
`h̃₁, …, h̃_{m₁}, g̃_j (j ∈ J)` vanish and their gradients in all of `x̃` have rank `< m₁ + |J|`. -/
def Cond43b (P : POP n m1 m2) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) : Prop :=
  ∀ J : Finset (Fin m2), J.card ≤ n - m1 →
    ¬ ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
      (∀ e, eval xt (homog (consDeg d d' J e) (consPoly P J e)) = 0) ∧
      (Matrix.of fun (k : Fin (n + 1)) (e : Fin m1 ⊕ J) =>
          hgrad (consDeg d d' J e) (consPoly P J e) xt k).rank < m1 + J.card

/-- Condition 4.3 (c), p. 14, through Proposition 4.1: for every `J ⊆ [m₂]` with
`|J| ≤ n − m₁` and every choice of one polynomial `q = p_{k+1}` among
`h₁, …, h_{m₁}, g_j (j ∈ J)`, the system (4.5) for `(f, the others; q)` has no solution. -/
def Cond43c (P : POP n m1 m2) (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) : Prop :=
  ∀ J : Finset (Fin m2), J.card ≤ n - m1 → ∀ c : Fin m1 ⊕ J,
    ¬ Sys45 d0 P.f (fun e : {e : Fin m1 ⊕ J // e ≠ c} => consDeg d d' J e.1)
      (fun e => consPoly P J e.1) (consDeg d d' J c) (consPoly P J c)

/-- Condition 4.3 (d), p. 14, through Proposition 4.2: for every `J ⊆ [m₂]` with
`|J| ≤ n − m₁`, the system (4.10) for `(f, h₁, …, h_{m₁}, g_j (j ∈ J))` has no solution. -/
def Cond43d (P : POP n m1 m2) (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) : Prop :=
  ∀ J : Finset (Fin m2), J.card ≤ n - m1 →
    ¬ Sys410 d0 P.f (consDeg d d' J) (consPoly P J)

/-- Condition 4.3, p. 14: items (a)–(d). -/
def Cond43 (P : POP n m1 m2) (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) : Prop :=
  Cond43a P d d' ∧ Cond43b P d d' ∧ Cond43c P d0 d d' ∧ Cond43d P d0 d d'

end LasserreFC.Generic


