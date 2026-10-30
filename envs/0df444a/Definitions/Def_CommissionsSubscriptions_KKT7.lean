-- Prove2me | Definitions.Def_CommissionsSubscriptions_KKT7
-- name    : CommissionsSubscriptions_KKT7
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:34:10.752784+00:00
-- url     : https://prove2.me/theorems/9205c5a7-a7aa-496f-b35f-398ccee39cf2
-- title:
--   Optimality system (EC.3) for the relaxation (7)
-- statement:
--   For $(x,q^s,q^b)$ and multipliers $(\theta^b,\theta^s,\eta^b,\eta^s,\pi)$, with $g_j(q)=F^{-1}_{b_j}(1-q/b_j)q$ and $h_i(q)=F^{-1}_{s_i}(q/s_i)q$, the **system (EC.3)** for (7) is:
--
--   1. (EC.3a) $g'_j(q^b_j)-\theta^b_j-\eta^b_j=0$, and (EC.3b) $h'_i(q^s_i)-\theta^s_i+\eta^s_i=0$, with $g'_j(q^b_j)$, $h'_i(q^s_i)$ finite (one-sided limits at the end points, footnote 22);
--   2. (EC.3c) $\theta^b_j-\theta^s_i+\pi_{ij}-c_i=0$ for $(i,j)\in E$;
--   3. (EC.3d) $q^b_j\le b_j\perp\eta^b_j\ge0$; (EC.3e) $q^s_i\le s_i\perp\eta^s_i\ge0$; (EC.3f) $x_{ij}\ge0\perp\pi_{ij}\ge0$ on $E$;
--   4. (EC.3g) $\sum_{i:(i,j)\in E}x_{ij}=q^b_j$ for $j\in B$; (EC.3h) $\sum_{j:(i,j)\in E}x_{ij}=q^s_i$ for $i\in S$.
--
--   The multiplier $\theta^s$ becomes the price vector in the proof of Theorem 1.
--
--   **Formalization Note** A complementarity $a\le A\perp\eta\ge0$ is $a\le A$, $\eta\ge0$, $\eta(A-a)=0$. The printed index ranges "$\forall i\in B$" in (EC.3g) and "$\forall j\in S$" in (EC.3h) are typos for $j\in B$ and $i\in S$.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Proposition EC.1(iii), (EC.3a)–(EC.3h), p. ec3; Lemma EC.1(ii), p. ec4

import Mathlib
import Definitions.Def_CommissionsSubscriptions_gB
import Definitions.Def_CommissionsSubscriptions_hR
import Definitions.Def_CommissionsSubscriptions_HasBdryDeriv

namespace CommissionsSubscriptions

/-- **The optimality system (EC.3) for the relaxation (7).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Proposition EC.1(iii), (EC.3a)–(EC.3h), p. ec3, applied
to (7) through Lemma EC.1(ii), p. ec4 (`g_j(q) = F⁻¹_{b_j}(1 − q/b_j) q`,
`h_i(q) = F⁻¹_{s_i}(q/s_i) q`, `w_{ij} = c_i`). For a primal point `(x, q^s, q^b)` and multipliers
`(θ^b, θ^s, η^b, η^s, π)`:
* (EC.3a) `g′_j(q^b_j) − θ^b_j − η^b_j = 0`, with `g′_j(q^b_j)` finite;
* (EC.3b) `h′_i(q^s_i) − θ^s_i + η^s_i = 0`, with `h′_i(q^s_i)` finite;
* (EC.3c) `θ^b_j − θ^s_i + π_{ij} − c_i = 0` for `(i,j) ∈ E`;
* (EC.3d) `q^b_j ≤ b_j ⊥ η^b_j ≥ 0`; (EC.3e) `q^s_i ≤ s_i ⊥ η^s_i ≥ 0`;
* (EC.3f) `x_{ij} ≥ 0 ⊥ π_{ij} ≥ 0` for `(i,j) ∈ E`;
* (EC.3g) `Σ_{i:(i,j)∈E} x_{ij} = q^b_j` for `j ∈ B`; (EC.3h) `Σ_{j:(i,j)∈E} x_{ij} = q^s_i` for
  `i ∈ S`.

**Formalization Note (Reading 8).** Derivatives at the end points `0`, `b_j`, `s_i` are the
one-sided limits of footnote 22 (`HasBdryDeriv`), and they are finite. `hR` is used for `h_i`:
it agrees with `h_i` on `[0, s_i)`, which is all that its derivative reads. The printed index
ranges "`∀ i ∈ B`" in (EC.3g) and "`∀ j ∈ S`" in (EC.3h) are typos for `∀ j ∈ B`, `∀ i ∈ S`.
A complementarity `a ≤ A ⊥ η ≥ 0` is `a ≤ A ∧ η ≥ 0 ∧ η (A − a) = 0`. -/
def KKT7 {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ) : Prop :=
  (∀ j, HasBdryDeriv (gB M j) 0 (M.b j) (qb j) (θb j + ηb j)) ∧
    (∀ i, HasBdryDeriv (hR M i) 0 (M.s i) (qs i) (θs i - ηs i)) ∧
    (∀ e ∈ M.E, θb e.2 - θs e.1 + π e.1 e.2 - M.c e.1 = 0) ∧
    (∀ j, qb j ≤ M.b j ∧ 0 ≤ ηb j ∧ ηb j * (M.b j - qb j) = 0) ∧
    (∀ i, qs i ≤ M.s i ∧ 0 ≤ ηs i ∧ ηs i * (M.s i - qs i) = 0) ∧
    (∀ e ∈ M.E, 0 ≤ x e.1 e.2 ∧ 0 ≤ π e.1 e.2 ∧ π e.1 e.2 * x e.1 e.2 = 0) ∧
    (∀ j, ∑ i ∈ Finset.univ.filter (fun i => (i, j) ∈ M.E), x i j = qb j) ∧
    (∀ i, ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ M.E), x i j = qs i)

end CommissionsSubscriptions


