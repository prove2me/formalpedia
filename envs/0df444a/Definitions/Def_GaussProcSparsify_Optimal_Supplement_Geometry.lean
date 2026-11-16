-- Prove2me | Definitions.Def_GaussProcSparsify_Optimal_Supplement_Geometry
-- name    : GaussProcSparsify_Optimal_Supplement_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:20:19.67166+00:00
-- url     : https://prove2.me/theorems/4c0ff014-8a77-4ed7-aeeb-7263dbcfe217
-- title:
--   Halfspace presentations, geometric width, Gaussian distance and cubes
-- statement:
--   A finite halfspace presentation is a list $H=((a_j,b_j))_{j<m}$ with $a_j\in\mathbb R^n$, $b_j\in\mathbb R$. Its intersection is
--   $$P_H=\{x:\langle a_j,x\rangle\le b_j\text{ for every }j<m\}.$$
--   The list length counts inequalities, including repetitions. Zero normals are allowed, so an inconsistent inequality can represent the empty set; the empty list represents the whole space. A set $K$ has geometric width at most $r$ if for some arbitrary set $T$ of unit vectors and real thresholds with $|b_t|\le r$,
--   $$K=\{x:\langle t,x\rangle\le b_t\text{ for all }t\in T\}.$$
--   Thresholds may have either sign, and $T$ may be empty or infinite. Gaussian distance is $\operatorname{dist}_G(K,L)=\gamma_n((K\setminus L)\cup(L\setminus K))$. The cube $C_n(r)$ is $\{x:-r\le x_i\le r\text{ for all }i\}$. All sets used in the theorem statements are closed and hence measurable. Gaussian distance converts a finite probability to a real number, including for empty and unbounded sets. These definitions support the geometric upper and lower bounds.
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), §1.1.2, PDF pp. 5–6 (printed pp. 4–5); §4.2, PDF p. 26 (printed p. 25), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- A finite list of closed halfspaces; zero normals and the empty list are allowed.
PDF pp. 5–6, 35. -/
def halfspaceIntersection {n : ℕ} (H : List (Vec n × ℝ)) : Set (Vec n) :=
  {x | ∀ q ∈ H, inner ℝ q.1 x ≤ q.2}

/-- Geometric width with arbitrary unit normals and signed thresholds. PDF pp. 5, 26. -/
def HasGeometricWidth {n : ℕ} (K : Set (Vec n)) (r : ℝ) : Prop :=
  ∃ T : Set (Vec n), ∃ b : Vec n → ℝ,
    (∀ t ∈ T, ‖t‖ = 1 ∧ |b t| ≤ r) ∧
      K = {x | ∀ t ∈ T, inner ℝ t x ≤ b t}

/-- Gaussian probability of symmetric difference. The probability is always finite;
this real conversion never converts an infinite measure to zero. PDF p. 5. -/
noncomputable def gaussianDistance {n : ℕ} (K L : Set (Vec n)) : ℝ :=
  (gaussian n ((K \ L) ∪ (L \ K))).toReal

/-- The coordinate cube of Theorem 5, PDF pp. 6, 34. -/
def cube (n : ℕ) (r : ℝ) : Set (Vec n) :=
  {x | ∀ i : Fin n, -r ≤ x i ∧ x i ≤ r}

end GaussProcSparsify.Optimal.Supplement


