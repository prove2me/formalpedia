-- Prove2me | Definitions.Def_FairKMeans_LPOracles
-- name    : FairKMeans_LPOracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:21.178983+00:00
-- url     : https://prove2.me/theorems/5aaa13b2-8bb2-4254-b058-ce1fd74b6ca1
-- title:
--   The fair assignment LP, LP (29), exact LP oracles and LP sizes
-- statement:
--   The **fair assignment LP** of a center family $S$ minimizes $\mathrm{Cost}(P,S,\phi_S)$ over all $(\alpha,\beta)$-fair fractional assignments. Given families $P_\lambda=(p_\lambda)$, $U=(u_p)$ indexed by $P$ and candidate families $T'$, $V$, **LP (29)** is
--
--   $$\min_{\phi_{T'},z}\ \sum_{c\in T'}z_c\quad\text{s.t.}\quad \sum_{c}\phi_{T'}(p,c)=1,\ \ \phi_{T'}(p,c)\ge0,\ \ z_c\ge\sum_p\phi_{T'}(p,c)\big(\|p_\lambda-c\|^2-\|u_p-v\|^2\big)\ (c\in T',v\in V),$$
--
--   together with the fairness constraints $\beta_i\sum_p\phi_{T'}(p,c)\le\sum_{p\in P^{(i)}}\phi_{T'}(p,c)\le\alpha_i\sum_p\phi_{T'}(p,c)$ for every $c$ and $i$.
--
--   An **exact LP oracle** returns an optimal solution of the LP whenever an optimal solution exists. The fair assignment LP of $s$ centers has $ns$ variables and $n+ns+2ms$ constraints; LP (29) with $|T'|=s$, $|V|=v$ has $(n+1)s$ variables and $n+ns+sv+2ms$ constraints.
--
--   These are the two linear programs Algorithm 1 solves; footnote 1 counts the LP solver's time separately.
--
--   **Formalization Note** An oracle is a function returning a candidate solution; its specification asks nothing on inputs without an optimum, so it is satisfiable. Constraint counts include the nonnegativity constraints.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Definition 12, p.18 (PDF p.20); LP (29), p.24 (PDF p.26); sizes in the proof of Proposition 29, p.36 (PDF p.38); footnote 1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_FairKMeans_Model

namespace FairKMeans

/-!
# The two linear programs of Algorithm 1 and their exact-solver oracles

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…): the fair assignment LP
(Definition 12, p.18, PDF 20), LP (29) (p.24, PDF 26), and their sizes (proof of
Proposition 29, p.36, PDF 38). Footnote 1 (p.5, PDF 7) counts the time of the LP solver
separately.

**Formalization Note.** An LP solver is an oracle function returning a candidate solution. Its
specification is "it returns an optimal solution whenever an optimal solution exists"; this is
satisfiable (choose an optimum when one exists), and it puts no demand on infeasible or
unbounded inputs. The oracles are specified relative to the instance `I` whose data (groups and
bounds) enter the LP. Sizes count variables and constraints, nonnegativity constraints included.
-/

variable {d n m : ℕ}

/-- An oracle for the fair assignment LP: given a center family, an assignment matrix. -/
abbrev FairLPOracle (d n : ℕ) : Type := (s : ℕ) → (Fin s → E d) → (Fin n → Fin s → ℝ)

/-- The fair-LP oracle solves the fair assignment LP of every center family exactly whenever it
has an optimal solution. -/
def IsFairLPOracle (I : Instance d n m) (O : FairLPOracle d n) : Prop :=
  ∀ (s : ℕ) (S : Fin s → E d), (∃ φ, IsOptFairAssign I S φ) → IsOptFairAssign I S (O s S)

/-- `(φ, z)` is feasible for LP (29) with shifted points `P_λ`, vectors `U` and candidate
families `T'`, `V` (p.24): rows sum to one, entries nonnegative,
`z_c ≥ ∑_p φ(p,c)(‖p_λ − c‖² − ‖u_p − v‖²)` for all `c ∈ T'`, `v ∈ V`, and fairness of every
column. -/
def IsLP29Feasible {s v : ℕ} (I : Instance d n m) (pl u : Fin n → E d) (T' : Fin s → E d)
    (V : Fin v → E d) (φ : Fin n → Fin s → ℝ) (z : Fin s → ℝ) : Prop :=
  IsAssignment φ ∧
    (∀ (c : Fin s) (b : Fin v), ∑ p, φ p c * (‖pl p - T' c‖ ^ 2 - ‖u p - V b‖ ^ 2) ≤ z c) ∧
    IsFair I φ

/-- `(φ, z)` is an optimal solution of LP (29): feasible and minimizing `∑_c z_c`. -/
def IsLP29Optimal {s v : ℕ} (I : Instance d n m) (pl u : Fin n → E d) (T' : Fin s → E d)
    (V : Fin v → E d) (φ : Fin n → Fin s → ℝ) (z : Fin s → ℝ) : Prop :=
  IsLP29Feasible I pl u T' V φ z ∧
    ∀ (φ' : Fin n → Fin s → ℝ) (z' : Fin s → ℝ), IsLP29Feasible I pl u T' V φ' z' →
      ∑ c, z c ≤ ∑ c, z' c

/-- An oracle for LP (29): from `(P_λ, U, T', V)` to a pair `(φ_{T'}, z)`. -/
abbrev LP29Oracle (d n : ℕ) : Type :=
  (s v : ℕ) → (Fin n → E d) → (Fin n → E d) → (Fin s → E d) → (Fin v → E d) →
    (Fin n → Fin s → ℝ) × (Fin s → ℝ)

/-- The LP (29) oracle returns an optimal solution whenever one exists. -/
def IsLP29Oracle (I : Instance d n m) (O : LP29Oracle d n) : Prop :=
  ∀ (s v : ℕ) (pl u : Fin n → E d) (T' : Fin s → E d) (V : Fin v → E d),
    (∃ φ z, IsLP29Optimal I pl u T' V φ z) →
      IsLP29Optimal I pl u T' V (O s v pl u T' V).1 (O s v pl u T' V).2

/-- (variables, constraints) of the fair assignment LP of `s` centers: `n·s` variables;
`n` row constraints, `n·s` nonnegativity constraints and `2·m·s` fairness constraints. -/
def fairLPSize (n m s : ℕ) : ℕ × ℕ := (n * s, n + n * s + 2 * m * s)

/-- (variables, constraints) of LP (29) with `|T'| = s`, `|V| = v` (p.36): `(n+1)·s`
variables; `n` row, `n·s` nonnegativity, `s·v` `z`-constraints and `2·m·s` fairness
constraints. -/
def lp29Size (n m s v : ℕ) : ℕ × ℕ := ((n + 1) * s, n + n * s + s * v + 2 * m * s)

end FairKMeans


