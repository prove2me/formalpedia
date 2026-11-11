-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_CSP
-- name    : FasterExactColoring_ThreeColor_CSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:46.869286+00:00
-- url     : https://prove2.me/theorems/e70ff3af-ae46-4326-80f9-5feeda25defc
-- title:
--   Finite forbidden-assignment constraint systems and local elimination
-- statement:
--   An $(A,B)$ constraint satisfaction instance has finitely many active variable labels, a domain contained in $\{0,\ldots,A-1\}$ for each variable, and a finite list of forbidden simultaneous assignments. Each forbidden assignment specifies at most $B$ variable–color pairs, all on active variables. Empty domains, singleton domains and empty forbidden assignments retain their usual semantics. Inactive labels are padding for eliminated variables and do not participate in satisfaction.
--
--   A solution selects an allowed color for every active variable and fails to realize every forbidden simultaneous assignment. Search output is either a satisfying assignment with a success flag, or a rejection flag on an unsatisfiable instance. Local elimination removes exactly one active variable, preserves all other domains and all original constraints not involving that variable, and adds constraints only on its original constraint-neighbors.
--
--   The exact constants are
--   $$\Lambda=\sup\{x\ge1:x^5\le2x+2\},\qquad \lambda_{\rm cycle}=\sup\{x\ge1:x^8\le x^3+x^2+x+1\}.$$
--   Both sublevel sets contain $1$ and are bounded above by $2$. Their suprema are the unique positive roots specifying $\lambda(4,4,5,5)$ and $\lambda(5,6,7,8)$. In particular, $1.36443$ is not substituted for $\Lambda$.
--
--   The code is length-delimited and charges the supplied constraint description. These definitions retain the local clause of Lemma 3.3 as well as satisfiability.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Definition 3.1 and Eq. (1), pp. 3–4 (PDF pp. 5–6); Section 2 work factors, p. 3 (PDF p. 5)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_GraphInput

namespace FasterExactColoring.ThreeColor

/-- Definition 3.1. Active labels allow elimination without relabeling other variables.
Constraints are finite forbidden simultaneous assignments, including the empty one. -/
structure CSP (A B n : ℕ) where
  active : Finset (Fin n)
  domain : Fin n → Finset (Fin A)
  constraints : List (Finset (Fin n × Fin A))
  arity : ∀ c ∈ constraints, c.card ≤ B
  wellScoped : ∀ c ∈ constraints, ∀ p ∈ c, p.1 ∈ active

def CSP.solution {A B n : ℕ} (I : CSP A B n) (f : Fin n → ℕ) : Prop :=
  (∀ v ∈ I.active, ∃ a ∈ I.domain v, f v = a.val) ∧
  ∀ c ∈ I.constraints, ∃ p ∈ c, f p.1 ≠ p.2.val

def CSP.satisfiable {A B n : ℕ} (I : CSP A B n) : Prop := ∃ f, I.solution f

def CSP.code {A B n : ℕ} (I : CSP A B n) : List ℕ :=
  [A,B,n] ++ vertexSetCode I.active ++
    (List.finRange n).flatMap (fun v =>
      (I.domain v).card :: ((I.domain v).sort (· ≤ ·)).map Fin.val) ++
    [I.constraints.length] ++ I.constraints.flatMap (fun c =>
      c.card :: (((List.finRange n).flatMap (fun v => (List.finRange A).map (fun a => (v,a)))).filterMap (fun p => if p ∈ c then some [p.1.val,p.2.val] else none)).flatten)

def CSP.searchAnswer {A B n : ℕ} (I : CSP A B n) (y : List ℕ) : Prop :=
  (y = [0] ∧ ¬ I.satisfiable) ∨
  ∃ f, I.solution f ∧ y = 1 :: (List.finRange n).map f

def CSP.neighbors {A B n : ℕ} (I : CSP A B n) (v : Fin n) : Finset (Fin n) :=
  I.active.filter (fun u => u ≠ v ∧
    ∃ c ∈ I.constraints, (∃ p ∈ c, p.1 = v) ∧ (∃ p ∈ c, p.1 = u))

/-- Eliminated constraints are replaced locally; every untouched constraint is retained,
in its original order; no other variable domain changes. -/
def CSP.localElimination {A n : ℕ} (I J : CSP A 2 n) (v : Fin n) : Prop :=
  J.active = I.active.erase v ∧
  (∀ u, u ≠ v → J.domain u = I.domain u) ∧
  (I.satisfiable ↔ J.satisfiable) ∧
  ∃ added : List (Finset (Fin n × Fin A)),
    J.constraints = I.constraints.filter (fun c =>
      decide (∀ p ∈ c, p.1 ≠ v)) ++ added ∧
    ∀ c ∈ added, ∀ p ∈ c, p.1 ∈ I.neighbors v

/-- Eq. (1): the unique positive root of x^5 - 2x - 2. The defining
sublevel set contains 1 and is bounded above by 2. -/
noncomputable def cspBase : ℝ := sSup {x : ℝ | 1 ≤ x ∧ x^5 ≤ 2*x+2}

/-- The degree-three-cycle work factor, λ(5,6,7,8). -/
noncomputable def cycleBase : ℝ := sSup {x : ℝ | 1 ≤ x ∧ x^8 ≤ x^3+x^2+x+1}

end FasterExactColoring.ThreeColor


