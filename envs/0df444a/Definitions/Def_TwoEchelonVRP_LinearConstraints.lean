-- Prove2me | Definitions.Def_TwoEchelonVRP_LinearConstraints
-- name    : TwoEchelonVRP_LinearConstraints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:28:13.987528+00:00
-- url     : https://prove2.me/theorems/22e729b3-ac55-4107-a969-557b67cbe0f3
-- title:
--   Linear constraints (2)–(8) of formulation F
-- statement:
--   Let $x_{kl}$ ($k \in N_S$, $l \in \mathcal R_k$), $y_r$ ($r \in \mathcal M$) and $q_{kr}$ ($r \in \mathcal M$, $k \in N_S$) be real numbers: $x_{kl}$ says whether second-level route $l$ of satellite $k$ is used, $y_r$ whether first-level route $r$ is used, and $q_{kr}$ is the quantity delivered by route $r$ to satellite $k$. They satisfy the **linear constraints of F** when
--
--   1. (2) $\sum_{k \in N_S} \sum_{l \in \mathcal R_{ik}} x_{kl} = 1$ for every customer $i$, where $\mathcal R_{ik}$ is the set of routes of $k$ visiting $i$;
--   2. (3) $\sum_{l \in \mathcal R_k} x_{kl} \le m_k$ for every satellite $k$;
--   3. (4) $\sum_{k \in N_S} \sum_{l \in \mathcal R_k} x_{kl} \le m^2$;
--   4. (5) $\sum_{l \in \mathcal R_k} w_{kl} x_{kl} \le B_k$ for every satellite $k$;
--   5. (6) $\sum_{r \in \mathcal M} y_r \le m^1$;
--   6. (7) $\sum_{r \in \mathcal M_k} q_{kr} = \sum_{l \in \mathcal R_k} w_{kl} x_{kl}$ for every satellite $k$;
--   7. (8) $\sum_{k \in R_r} q_{kr} \le Q_1 y_r$ for every first-level route $r$;
--   8. $q_{kr} = 0$ for $k \in N_S \setminus R_r$.
--
--   Formulation F adds the integrality constraints (9)–(11); its LP relaxation LF replaces them by bounds.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §2.1, formulation (F), constraints (2)–(8), p. 300, and 'we assume q_kr = 0, k ∈ N_S \ R_r', p. 300

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_Route2
import Definitions.Def_TwoEchelonVRP_Route1

namespace TwoEchelonVRP

/-- **The linear constraints (2)–(8) of formulation F.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §2.1, formulation (F), constraints (2)–(8), p. 300,
together with the convention "we assume q_kr = 0, k ∈ N_S \ R_r" (p. 300).

Variables: `x k l` (`x_kl`, route `l ∈ 𝓡_k` of satellite `k` used), `y r` (`y_r`, first-level route
`r ∈ 𝓜` used) and `qd r k` (`q_kr`, quantity delivered by first-level route `r` to satellite `k`).

* (2) `Σ_{k ∈ N_S} Σ_{l ∈ 𝓡_ik} x_kl = 1` for every customer `i`, where `𝓡_ik` is the set of routes
  of `k` visiting `i`;
* (3) `Σ_{l ∈ 𝓡_k} x_kl ≤ m_k` for every satellite `k`;
* (4) `Σ_{k ∈ N_S} Σ_{l ∈ 𝓡_k} x_kl ≤ m²`;
* (5) `Σ_{l ∈ 𝓡_k} w_kl x_kl ≤ B_k` for every satellite `k`;
* (6) `Σ_{r ∈ 𝓜} y_r ≤ m¹`;
* (7) `Σ_{r ∈ 𝓜_k} q_kr = Σ_{l ∈ 𝓡_k} w_kl x_kl` for every satellite `k`, where `𝓜_k` is the set
  of first-level routes visiting `k`;
* (8) `Σ_{k ∈ R_r} q_kr ≤ Q_1 y_r` for every first-level route `r`;
* `q_kr = 0` for `k ∉ R_r`.

**Formalization Note.** Shared by formulation F (with (9)–(11)) and its LP relaxation LF. -/
structure LinearConstraints {ns nc : ℕ} (I : Instance ns nc) (x : Fin ns → Route2 I → ℝ)
    (y : Route1 I → ℝ) (qd : Route1 I → Fin ns → ℝ) : Prop where
  /-- (2) -/
  cover : ∀ i : Fin nc, ∑ k, ∑ l ∈ Finset.univ.filter (fun l : Route2 I => i ∈ custSet l), x k l = 1
  /-- (3) -/
  fleet_sat : ∀ k, ∑ l, x k l ≤ (I.mSat k : ℝ)
  /-- (4) -/
  fleet2 : ∑ k, ∑ l, x k l ≤ (I.m2 : ℝ)
  /-- (5) -/
  sat_cap : ∀ k, ∑ l, (load2 l : ℝ) * x k l ≤ I.B k
  /-- (6) -/
  fleet1 : ∑ r, y r ≤ (I.m1 : ℝ)
  /-- (7) -/
  balance : ∀ k, ∑ r ∈ Finset.univ.filter (fun r : Route1 I => k ∈ satSet r), qd r k
    = ∑ l, (load2 l : ℝ) * x k l
  /-- (8) -/
  cap1 : ∀ r, ∑ k ∈ satSet r, qd r k ≤ (I.Q1 : ℝ) * y r
  /-- `q_kr = 0` for `k ∈ N_S \ R_r` -/
  off_route : ∀ r k, k ∉ satSet r → qd r k = 0

end TwoEchelonVRP


