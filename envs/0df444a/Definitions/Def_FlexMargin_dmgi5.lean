-- Prove2me | Definitions.Def_FlexMargin_dmgi5
-- name    : FlexMargin_dmgi5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:39:04.581316+00:00
-- url     : https://prove2.me/theorems/01edb527-fdbb-4b8d-ae5f-7de9292a95e6
-- title:
--   The DMGI of a homogeneous design $\delta^K(\mathcal A)$, problem (5)
-- statement:
--   When all products have the same mean demand and all capacities are $1$, the term $\sum_i\mu_i y_i$ of (4) is constant for fixed $K$, and the paper uses the reduced program
--
--   $$
--   \delta^K(\mathcal A)=\min_{w,y,z}\ \sum_{j=1}^m z_j
--   $$
--
--   under the same constraints as (4): prescribed numbers $k_{tr}$ of products at price level $\beta_{tr}$ in each category, $y_i+z_j\ge p_i$ on every arc, and $z\ge0$.
--
--   Lemma 2 computes it for the alternate long chain and Proposition 1 compares long chains through it.
--
--   **Formalization Note** As for (4), $z\ge0$ is made explicit and the value is an infimum, attained for $K\in Q$.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §4, display (5), p. 20

import Mathlib
import Definitions.Def_FlexMargin_betaCoef

open Finset

namespace FlexMargin

/-- **The DMGI of a homogeneous design `δ^K(𝒜)`, problem (5).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §4, display (5), p. 20: "When µi = µj for all 1 ≤ i,j ≤ n, the term Σ_{i=1}^n µiyi in the
objective function (4) is a constant for any fixed parameter set K. Therefore, we may omit this
term without loss of optimality and the DMGI for a homogeneous design A, denoted by δK(A), is
equivalent to the optimal objective function of the following problem: δK(A) := min_{w,y,z}
Σ_{j=1}^m zj" subject to the constraints of (4).

`dmgi5 P cat A K` is the infimum of `Σ_j z_j` subject to exactly the constraints of
`FlexMargin.dmgi`: a level map `w` (`w i ≤ cat i + 1`) with `K t r` products of category `t` at level
`r ≤ t`, `y_i = β_{cat i, w i}`, `z ≥ 0`, and `y_i + z_j ≥ P (cat i)` on every arc `(j, i)` of `A`.

**Formalization Note.** Same encoding and the same added `z ≥ 0` as `FlexMargin.dmgi` (see there).
Section 4 has unit capacities, so the objective `Σ_j z_j` is `Σ_j C_j z_j` with `C ≡ 1`. For `K ∈ Q`
the infimum is attained; outside `Q` the value `sInf ∅ = 0` is junk and never used. -/
noncomputable def dmgi5 {m n T : ℕ} (P : Fin T → ℝ) (cat : Fin n → Fin T)
    (A : Finset (Fin m × Fin n)) (K : (t : Fin T) → Fin (t.val + 1) → ℕ) : ℝ :=
  sInf {v : ℝ | ∃ (w : Fin n → ℕ) (y : Fin n → ℝ) (z : Fin m → ℝ),
    (∀ i, w i ≤ (cat i).val + 1) ∧
    (∀ (t : Fin T) (r : Fin (t.val + 1)),
      (univ.filter (fun i => cat i = t ∧ w i = r.val)).card = K t r) ∧
    (∀ i, y i = betaCoef P (cat i) (w i)) ∧
    (∀ j, 0 ≤ z j) ∧
    (∀ a ∈ A, P (cat a.2) ≤ y a.2 + z a.1) ∧
    v = ∑ j, z j}

end FlexMargin


