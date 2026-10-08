-- Prove2me | Definitions.Def_SymBoolPCSP_LPRounding_Basic
-- name    : SymBoolPCSP_LPRounding_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:29:31.264004+00:00
-- url     : https://prove2.me/theorems/ecdcc9dd-6815-47b8-8d0c-240550a6c4f3
-- title:
--   The convex-hull LP relaxation and the acceptance rule of the §3.2 algorithm (with Maj_L, AT_L from the shared definitions)
-- statement:
--   This file fixes the objects of §3.2 of Brakensiek–Guruswami for the Boolean domain $\{0,1\}$.
--
--   **Promise families and instances.** A finite family of promise relations is $\Gamma = \{(P_R, Q_R) : R \in \tau\}$ with $P_R \subseteq Q_R \subseteq \{0,1\}^{k_R}$. An instance $\Psi = (\Psi_P, \Psi_Q)$ has variables $x_1, \dots, x_n$ and clauses $R_j(x_{j_1}, \dots, x_{j_k})$ (a variable may repeat); $\Psi_P$ reads each clause with $P_{R_j}$ and $\Psi_Q$ with $Q_{R_j}$. A function $f : \{0,1\}^L \to \{0,1\}$ is a polymorphism of $\Gamma$ if, for every $R$ and all $x^{(1)}, \dots, x^{(L)} \in P_R$, applying $f$ coordinate-wise gives a tuple in $Q_R$ (Definition 2.4). These notions come from the published setting file.
--
--   **Two function families** (p. 10). For $x \in \{0,1\}^L$,
--   $$\mathrm{Maj}_L(x) = 1 \iff \sum_{i=1}^L x_i > \frac L2, \qquad \mathrm{AT}_L(x) = 1 \iff \sum_{i=1}^L (-1)^{i-1} x_i > 0,$$
--   and both are $0$ otherwise. The paper uses them for odd $L$.
--
--   **The LP relaxation** (p. 13). The unknowns are rationals $v_1, \dots, v_n$, one per variable. A vector $v$ is a solution if
--
--   1. $0 \le v_i \le 1$ for every $i$, and
--   2. for every clause $R_j(x_{j_1}, \dots, x_{j_k})$ of $\Psi_P$, the tuple $(v_{j_1}, \dots, v_{j_k})$ lies in the convex hull of $P_{R_j}$: there are weights $\alpha_y \ge 0$, $y \in \{0,1\}^k$, vanishing outside $P_{R_j}$ and summing to $1$, with $v_{j_c} = \sum_y \alpha_y\, y_c$ for every position $c$.
--
--   **The algorithm's answer** (p. 13). For each variable $x_j$ the algorithm fixes $v_j = 0$ and re-solves the LP; if that is infeasible it fixes $v_j = 1$ and re-solves; if that is also infeasible it outputs "unsatisfiable". If every variable passes, it outputs "satisfiable". So the algorithm outputs "satisfiable" exactly when the LP is feasible and, for every $j$, it has a solution with $v_j = 0$ or a solution with $v_j = 1$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\{0,1\}$ is `Bool` with `false` $= 0$; $\Gamma$ is a pair `𝔸 𝔹 : RelStruct τ ar Bool` from the published `PCSPBLPAff_Symmetric_Setting`, with $P_R$ = `𝔸.rel R` and $Q_R$ = `𝔹.rel R`, and an instance is an `Instance τ ar`. Coordinates of $\{0,1\}^L$ are `Fin L`, so the sign $(-1)^{i-1}$ of $\mathrm{AT}_L$ becomes $(-1)^i$ for the 0-based index; $\mathrm{Maj}_L(x) = 1$ is written $L < 2\,|x|$. `Maj L` and `AT L` are `SymBoolPCSP.CFixing.Maj` and `SymBoolPCSP.CFixing.AT` from the shared definitions file `SymBoolPCSP.CFixing.Basic`; they are defined for every $L$, and statements restrict to odd $L$. The LP is stated over $\mathbb Q$; the paper notes that its solutions may be taken rational, and an LP with rational data is feasible over $\mathbb R$ iff it is feasible over $\mathbb Q$. The acceptance predicate `LPAlgAccepts` adds the conjunct "the LP is feasible", which only matters for an instance with no variables (where the loop is empty); on an instance with variables it is implied by the per-variable test. A clause whose $P_R$ is empty makes the LP infeasible, so such instances are rejected. The name `IsHullLPSol` distinguishes this LP from the Basic LP `IsLPSol` of the setting file.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, pp. 8–10 (Definitions 2.1–2.4, Maj_L and AT_L on p. 10) and p. 13 (§3.2, the LP relaxation and the algorithm)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

namespace SymBoolPCSP.LPRounding

open PCSPBLPAff.Symmetric

/-! ### The §3.2 LP algorithm (arXiv:1704.01937v2)

The Boolean domain `{0, 1}` is `Bool` (`false` = 0, `true` = 1). A finite family of promise
relations `Γ = {(P_R, Q_R)}` is a pair `𝔸 𝔹 : RelStruct τ ar Bool` with `P_R = 𝔸.rel R`,
`Q_R = 𝔹.rel R`; an instance `Ψ = (Ψ_P, Ψ_Q)` is an `X : Instance τ ar`. Coordinates of
`{0,1}^L` are indexed by `Fin L`, so the paper's 1-based index `i ∈ [L]` is `⟨i - 1, _⟩`. The Majority and
Alternating-Threshold functions `Maj_L`, `AT_L` (p. 10) are `SymBoolPCSP.CFixing.Maj` and
`SymBoolPCSP.CFixing.AT`. -/

/-- `v` is a solution of the LP relaxation of §3.2 (p. 13) for the instance `X` over the
relations `P_R = 𝔸.rel R`: every `v_j ∈ [0, 1]`, and for every clause `j` the tuple
`(v_{x̄_j(1)}, …, v_{x̄_j(k)})` lies in the convex hull of the elements of `P_{R_j}`, i.e. it is
`∑_y α_y y` for weights `α ≥ 0` supported on `P_{R_j}` with `∑_y α_y = 1`. The LP is stated
over `ℚ`. -/
def IsHullLPSol {τ : Type} {ar : τ → ℕ} (𝔸 : RelStruct τ ar Bool) (X : Instance τ ar)
    (v : Fin X.n → ℚ) : Prop :=
  (∀ i, 0 ≤ v i ∧ v i ≤ 1) ∧
  ∀ j : Fin X.m, ∃ α : (Fin (ar (X.sym j)) → Bool) → ℚ,
    (∀ y, 0 ≤ α y) ∧ (∀ y, y ∉ 𝔸.rel (X.sym j) → α y = 0) ∧ (∑ y, α y = 1) ∧
    ∀ c, v (X.scope j c) = ∑ y, α y * (if y c then 1 else 0)

/-- The §3.2 algorithm (p. 13) outputs "satisfiable" on `X`: for every variable `x_j` the LP
is feasible with `v_j = 0` fixed or with `v_j = 1` fixed. The first conjunct (the LP itself
is feasible) only matters when `X` has no variables, where the loop over variables is empty. -/
def LPAlgAccepts {τ : Type} {ar : τ → ℕ} (𝔸 : RelStruct τ ar Bool) (X : Instance τ ar) : Prop :=
  (∃ v, IsHullLPSol 𝔸 X v) ∧
  ∀ j : Fin X.n, (∃ v, IsHullLPSol 𝔸 X v ∧ v j = 0) ∨ (∃ v, IsHullLPSol 𝔸 X v ∧ v j = 1)

end SymBoolPCSP.LPRounding


