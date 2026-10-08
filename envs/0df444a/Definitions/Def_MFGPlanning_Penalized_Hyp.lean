-- Prove2me | Definitions.Def_MFGPlanning_Penalized_Hyp
-- name    : MFGPlanning_Penalized_Hyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:33.320122+00:00
-- url     : https://prove2.me/theorems/a69ab83e-4c41-4ddf-a1c0-572f6abefd60
-- title:
--   Hypotheses (G1), (G3), (G4), (G5) on the numerical Hamiltonian and (24) on $W$
-- statement:
--   The numerical Hamiltonian $g(x_{i,j}, q_1, q_2, q_3, q_4)$ may satisfy:
--
--   1. **(G1) monotonicity**: $g$ is nonincreasing with respect to $q_1$ and $q_3$ and nondecreasing with respect to $q_2$ and $q_4$;
--   2. **(G3) differentiability**: $q \mapsto g(x_{i,j}, q)$ is of class $C^1$;
--   3. **(G4) convexity**: $q \mapsto g(x_{i,j}, q)$ is convex;
--   4. **(G5) coercivity**: uniformly with respect to $x$ and the other three variables,
--   $$
--   \lim_{q_1 \to -\infty} \frac{g}{|q_1|} = \lim_{q_2 \to +\infty} \frac{g}{q_2} = \lim_{q_3 \to -\infty} \frac{g}{|q_3|} = \lim_{q_4 \to +\infty} \frac{g}{|q_4|} = +\infty.
--   $$
--
--   Hypothesis **(24)** on $W$: $W : \mathbb R \to \mathbb R$ is a strictly convex, coercive $C^2$ function, and $V = W'$.
--
--   These are the standing assumptions of Theorem 1 of the paper, which every result of §3.2 inherits.
--
--   **Formalization Note** Each uniform limit in (G5) is written as "for every $R$ there is $L$ such that $g \ge R|q_k|$ whenever $q_k$ is beyond $L$". "Coercive" in (24) is read as superlinear, $W(m)/|m| \to +\infty$ as $|m| \to \infty$; the paper uses this on p. 7 when it states $V((0,\infty)) = (\lambda, +\infty)$. (G2), consistency with the continuous Hamiltonian $H$, only defines $H$ from $g$ and appears in no discrete statement, so it is not encoded. $g$ is given only at the grid points.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §2, (G1)–(G5), p. 4; §3.1, (24), p. 6

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid

namespace MFGPlanning.Penalized

open Filter

/-- (G₁) monotonicity (p. 4): g(x, ·) is nonincreasing in q₁ and q₃ and nondecreasing in
q₂ and q₄ (q₁, …, q₄ are the indices `0, 1, 2, 3` of `Fin 4`). -/
def G1 (d : Data) : Prop :=
  ∀ (p : Pt d) (q q' : Fin 4 → ℝ), q' 0 ≤ q 0 → q 1 ≤ q' 1 → q' 2 ≤ q 2 → q 3 ≤ q' 3 →
    d.g p q ≤ d.g p q'

/-- (G₃) differentiability (p. 4): g is of class C¹ in q at every grid point.
Formalization Note: g is only given at the grid points x_{i,j}. -/
def G3 (d : Data) : Prop :=
  ∀ p : Pt d, ContDiff ℝ 1 (d.g p)

/-- (G₄) convexity (p. 4): q ↦ g(x, q) is convex. -/
def G4 (d : Data) : Prop :=
  ∀ p : Pt d, ConvexOn ℝ Set.univ (d.g p)

/-- (G₅) coercivity (p. 4), the four limits uniform in x and in the other three variables:
g/|q₁| → +∞ as q₁ → −∞, g/q₂ → +∞ as q₂ → +∞, g/|q₃| → +∞ as q₃ → −∞,
g/|q₄| → +∞ as q₄ → +∞. -/
def G5 (d : Data) : Prop :=
  (∀ R : ℝ, ∃ L : ℝ, ∀ (p : Pt d) (q : Fin 4 → ℝ), q 0 ≤ -L → R * |q 0| ≤ d.g p q) ∧
  (∀ R : ℝ, ∃ L : ℝ, ∀ (p : Pt d) (q : Fin 4 → ℝ), L ≤ q 1 → R * q 1 ≤ d.g p q) ∧
  (∀ R : ℝ, ∃ L : ℝ, ∀ (p : Pt d) (q : Fin 4 → ℝ), q 2 ≤ -L → R * |q 2| ≤ d.g p q) ∧
  (∀ R : ℝ, ∃ L : ℝ, ∀ (p : Pt d) (q : Fin 4 → ℝ), L ≤ q 3 → R * |q 3| ≤ d.g p q)

/-- Hypothesis (24) on W (p. 6): W : ℝ → ℝ is a strictly convex, coercive C² function
(V = W'). Formalization Note: "coercive" is read as superlinear, W(m)/|m| → +∞ as |m| → ∞,
which is what the paper uses on p. 7 (V((0, ∞)) = (λ, +∞)). -/
def HypW (d : Data) : Prop :=
  ContDiff ℝ 2 d.W ∧ StrictConvexOn ℝ Set.univ d.W ∧
    Tendsto (fun m => d.W m / |m|) (cocompact ℝ) atTop

end MFGPlanning.Penalized


