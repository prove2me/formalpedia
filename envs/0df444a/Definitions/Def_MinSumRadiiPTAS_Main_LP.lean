-- Prove2me | Definitions.Def_MinSumRadiiPTAS_Main_LP
-- name    : MinSumRadiiPTAS_Main_LP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:03:57.137331+00:00
-- url     : https://prove2.me/theorems/4ca7ebe0-3e2c-4431-bc46-44574b0374a9
-- title:
--   The Lagrangian LP $\mathrm{opt}_{f,\lambda}(X)$, its radius-restricted version $\mathrm{opt}^R_{f,\lambda}(X)$, optimal covers $\mathrm{OPT}_\lambda$, $O_R$, $O_{3R}$ and the greedy rounding of §3
-- statement:
--   Let $X \subseteq P$ be a client set and $\lambda$ an opening cost.
--
--   1. **(Lagrangian-LP)** (p. 7): variables $x_B \ge 0$ for $B \in \mathfrak B$, constraints $\sum_{B \in \mathfrak B : p \in B} x_B \ge 1$ for $p \in X$, objective $\sum_{B \in \mathfrak B} (r_B + \lambda) x_B$ (`LPFeasible`, `lpObj`). The radius-restricted LP additionally sets $x_B = 0$ when $r_B > R$ (p. 25).
--   2. `optf d λ X` $= \mathrm{opt}_{f,\lambda}(X)$ and `optfR d λ R X` $= \mathrm{opt}^R_{f,\lambda}(X)$: the infimum of the objective over the feasible solutions. `IsOptimalLP` says $x$ is feasible for the unrestricted LP with objective $\mathrm{opt}_{f,\lambda}(X)$.
--   3. **Optimal integral covers** `IsOptCover d λ allowed X O`: $O \subseteq \mathfrak B$, every ball of $O$ is allowed, $O$ covers $X$, and $\mathrm{cost}_\lambda(O) \le \mathrm{cost}_\lambda(S)$ for every allowed $S \subseteq \mathfrak B$ covering $X$. With all balls allowed this is $\mathrm{OPT}_\lambda(X)$ (p. 7); with $r_B \le R$ it is $O_R = \mathrm{OPT}^R_\lambda(P')$ (pp. 23–24); with $r_B \le 3R$ it is $O_{3R}$ (p. 25).
--   4. **Greedy rounding** (p. 7): `IsGreedyOrder d x l` says the list $l$ contains each ball $B \in \mathfrak B$ with $x_B > 0$ exactly once and nothing else, in nonincreasing order of radius (ties in any order). `greedySelect d l` processes $l$ in order and keeps a ball iff its point set is disjoint from those of all balls kept so far; `greedyRound d l` $= S' = \{\mathrm{Ball}(c_B, 3 r_B) : B \text{ kept}\}$.
--
--   **Formalization Note** The paper defines $\mathrm{opt}_{f,\lambda}(X)$ as the optimum of the packing dual (p. 7); by LP strong duality (for a metric and $\lambda \ge 0$ both programs are feasible, the primal through $x_{\mathrm{Ball}(p,0)} = 1$, and the objective is bounded below by $0$) it equals the primal optimum used here, and the infimum is attained. For the restricted LP the same holds when $R \ge 0$, which every use guarantees ($\lambda < 6R$ with $\lambda > 0$). The rounding's dual solution $y$ appears only in the proof.
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §3 p. 7, §6 pp. 23–25

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_Basic

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-!
# The Lagrangian LP, optimal covers and the greedy rounding of §3

Grandoni, Gupta, Yadav, *A PTAS for the Minimum Sum of Radii Problem* (STOC 2027 submission,
SHA-256 99b43d49…): §3, p. 7 ((Lagrangian-LP), its packing dual, `opt_{f,λ}(X)`, `OPT_λ(X)`, the
greedy rounding); §6, pp. 23–25 (`OPT^R_λ(P′)`, the radius-restricted LP value `opt^R_{f,λ}(X)`).

**Formalization Note.** LP variables are indexed by balls; only the values on `𝔅 = minimalBalls d`
matter. An LP value is the infimum of the objective over the feasible set. For a metric `d`, a
client set `X` and `λ ≥ 0` the feasible set is nonempty (`x_{Ball(p,0)} = 1`) whenever the zero-radius
balls are allowed (always for the unrestricted LP, and for `R ≥ 0` in the restricted one) and the
objective is `≥ 0`, so the infimum is a finite minimum. The paper defines `opt_{f,λ}(X)` as the
optimum of the packing dual (p. 7); by LP strong duality (both programs feasible and bounded) it
equals the primal optimum used here. Integral optima range over sets of balls of `𝔅`. -/

/-- Feasibility for (Lagrangian-LP) on the client set `X`, using only the balls of `𝔅` that satisfy
`allowed` (all of them, or `r_B ≤ R`): `x_B ≥ 0` on `𝔅`, `x_B = 0` on the balls not allowed, and
`∑_{B ∈ 𝔅, p ∈ B} x_B ≥ 1` for every `p ∈ X` (p. 7, p. 25). -/
def LPFeasible {n : ℕ} (d : Fin n → Fin n → ℝ) (allowed : Ball n → Prop) (X : Finset (Fin n))
    (x : Ball n → ℝ) : Prop :=
  (∀ B ∈ minimalBalls d, 0 ≤ x B) ∧
    (∀ B ∈ minimalBalls d, ¬ allowed B → x B = 0) ∧
    ∀ p ∈ X, 1 ≤ ∑ B ∈ (minimalBalls d).filter (fun B => p ∈ B.pts d), x B

/-- The objective of (Lagrangian-LP): `∑_{B ∈ 𝔅} (r_B + λ) x_B` (p. 7). -/
noncomputable def lpObj {n : ℕ} (d : Fin n → Fin n → ℝ) (lam : ℝ) (x : Ball n → ℝ) : ℝ :=
  ∑ B ∈ minimalBalls d, (B.radius + lam) * x B

/-- `opt_{f,λ}(X)`: the optimal value of (Lagrangian-LP) for the client set `X` (p. 7). -/
noncomputable def optf {n : ℕ} (d : Fin n → Fin n → ℝ) (lam : ℝ) (X : Finset (Fin n)) : ℝ :=
  sInf (lpObj d lam '' {x | LPFeasible d (fun _ => True) X x})

/-- `opt^R_{f,λ}(X)`: the optimal value of (Lagrangian-LP) restricted to balls of radius at most
`R` (`x_B = 0` whenever `r_B > R`), p. 25. -/
noncomputable def optfR {n : ℕ} (d : Fin n → Fin n → ℝ) (lam R : ℝ) (X : Finset (Fin n)) : ℝ :=
  sInf (lpObj d lam '' {x | LPFeasible d (fun B => B.radius ≤ R) X x})

/-- `x` is an optimal solution of the unrestricted (Lagrangian-LP) for `X`. -/
def IsOptimalLP {n : ℕ} (d : Fin n → Fin n → ℝ) (lam : ℝ) (X : Finset (Fin n))
    (x : Ball n → ℝ) : Prop :=
  LPFeasible d (fun _ => True) X x ∧ lpObj d lam x = optf d lam X

/-- `O` is a cheapest set of balls of `𝔅`, all satisfying `allowed`, that covers `X` under opening
cost `λ`: `OPT_λ(X)` for `allowed = ⊤` (p. 7), `OPT^R_λ(P′)` = `O_R` for `r_B ≤ R` (pp. 23–24),
`O_{3R}` for `r_B ≤ 3R` (p. 25). -/
def IsOptCover {n : ℕ} (d : Fin n → Fin n → ℝ) (lam : ℝ) (allowed : Ball n → Prop)
    (X : Finset (Fin n)) (O : Finset (Ball n)) : Prop :=
  O ⊆ minimalBalls d ∧ (∀ B ∈ O, allowed B) ∧ Covers d O X ∧
    ∀ S : Finset (Ball n), S ⊆ minimalBalls d → (∀ B ∈ S, allowed B) → Covers d S X →
      costL lam O ≤ costL lam S

/-- The greedy selection of §3 (p. 7): process the balls of the list in order and keep a ball iff
its point set is disjoint from the point sets of all balls kept so far (the result lists the kept
balls in processing order). -/
noncomputable def greedySelect {n : ℕ} (d : Fin n → Fin n → ℝ) (l : List (Ball n)) :
    List (Ball n) :=
  l.foldl (fun acc B => if ∀ B' ∈ acc, Disjoint (B.pts d) (B'.pts d) then acc ++ [B] else acc) []

/-- The output `S′ = {Ball(c_B, 3 r_B) : B ∈ S}` of the greedy rounding, where `S` is the greedy
selection from the processing list `l` (p. 7). -/
noncomputable def greedyRound {n : ℕ} (d : Fin n → Fin n → ℝ) (l : List (Ball n)) :
    List (Ball n) :=
  (greedySelect d l).map (fun B => B.withRadius (3 * B.radius))

/-- `l` is a valid processing list for the greedy rounding of the LP solution `x` (p. 7): it lists
every ball `B ∈ 𝔅` with `x_B > 0` exactly once and nothing else, in nonincreasing order of radius
(ties in any order). -/
def IsGreedyOrder {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Ball n → ℝ) (l : List (Ball n)) : Prop :=
  l.Nodup ∧ (∀ B, B ∈ l ↔ B ∈ minimalBalls d ∧ 0 < x B) ∧
    l.Pairwise (fun A B => B.radius ≤ A.radius)

end MinSumRadiiPTAS.Main


