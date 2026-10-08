-- Prove2me | Definitions.Def_MFGPlanning_Existence_Hyp
-- name    : MFGPlanning_Existence_Hyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:38.452594+00:00
-- url     : https://prove2.me/theorems/485266a6-baa7-490d-8196-e794e744b7b1
-- title:
--   The hypotheses (G1), (G3), (G4), (G5) on the numerical Hamiltonian and (24) on $W$
-- statement:
--   The hypotheses of §2 and §3.1 on the numerical Hamiltonian $g(x_{i,j}, q_1, q_2, q_3, q_4)$ and on $W$:
--
--   1. **(G1) monotonicity:** $g$ is nonincreasing with respect to $q_1$ and $q_3$ and nondecreasing with respect to $q_2$ and $q_4$.
--   2. **(G3) differentiability:** $g(x_{i,j},\cdot)$ is of class $C^1$.
--   3. **(G4) convexity:** $q \mapsto g(x_{i,j}, q)$ is convex.
--   4. **(G5) coercivity:** uniformly with respect to $x$ and the other three arguments,
--   $$\lim_{q_1\to-\infty}\frac{g}{|q_1|} = \lim_{q_2\to+\infty}\frac{g}{q_2} = \lim_{q_3\to-\infty}\frac{g}{|q_3|} = \lim_{q_4\to+\infty}\frac{g}{|q_4|} = +\infty.$$
--   5. **(24):** $W:\mathbb R\to\mathbb R$ is a strictly convex, coercive $C^2$ function, and $V = W'$.
--
--   These are the standing assumptions of §3.1 (with $\nu \ge 0$).
--
--   **Formalization Note** (G2) (consistency, $g(x,q_1,q_1,q_2,q_2) = H(x,q)$) only defines the continuous Hamiltonian $H$, which no discrete statement mentions, so it is not encoded. The uniform limits in (G5) are written out: for every $R$ there is $L$ such that, e.g., $q_1 \le -L$ implies $g \ge R|q_1|$ for all grid points and all $q$. "Coercive" in (24) is read as superlinear, $W(m)/|m| \to +\infty$ as $|m|\to\infty$: the paper deduces at once that $V$ maps $(0,\infty)$ onto an interval $(\lambda, +\infty)$, which needs $W' \to +\infty$; mere $W \to +\infty$ (e.g. $W = \sqrt{1+m^2}$) does not give it. (G5) is the same superlinear sense of coercivity. The directions of (G1) are components `0, 2` (nonincreasing) and `1, 3` (nondecreasing) of `Fin 4`.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §2, p. 4, (G1)–(G5); §3.1, p. 6, (24)

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid

namespace MFGPlanning.Existence

open Filter

variable (d : Data)

/-- (G1) monotonicity (p. 4): `g` is nonincreasing in `q_1`, `q_3` and nondecreasing in `q_2`, `q_4`
(components `0, 2` and `1, 3` of `Fin 4`). -/
def G1 : Prop :=
  ∀ (p : d.Pt) (q q' : Fin 4 → ℝ), q' 0 ≤ q 0 → q 1 ≤ q' 1 → q' 2 ≤ q 2 → q 3 ≤ q' 3 →
    d.g p q ≤ d.g p q'

/-- (G3) differentiability (p. 4): `g(x_{i,j}, ·)` is of class `C¹`. -/
def G3 : Prop := ∀ p : d.Pt, ContDiff ℝ 1 (d.g p)

/-- (G4) convexity (p. 4): `q ↦ g(x_{i,j}, q)` is convex. -/
def G4 : Prop := ∀ p : d.Pt, ConvexOn ℝ Set.univ (d.g p)

/-- (G5) coercivity (p. 4): `g/|q_1| → +∞` as `q_1 → −∞`, `g/q_2 → +∞` as `q_2 → +∞`,
`g/|q_3| → +∞` as `q_3 → −∞`, `g/|q_4| → +∞` as `q_4 → +∞`, each uniformly with respect to `x` and
the other three arguments. -/
def G5 : Prop :=
  (∀ R : ℝ, ∃ L : ℝ, ∀ (p : d.Pt) (q : Fin 4 → ℝ), q 0 ≤ -L → R * |q 0| ≤ d.g p q) ∧
  (∀ R : ℝ, ∃ L : ℝ, ∀ (p : d.Pt) (q : Fin 4 → ℝ), L ≤ q 1 → R * q 1 ≤ d.g p q) ∧
  (∀ R : ℝ, ∃ L : ℝ, ∀ (p : d.Pt) (q : Fin 4 → ℝ), q 2 ≤ -L → R * |q 2| ≤ d.g p q) ∧
  (∀ R : ℝ, ∃ L : ℝ, ∀ (p : d.Pt) (q : Fin 4 → ℝ), L ≤ q 3 → R * |q 3| ≤ d.g p q)

/-- Hypothesis (24) (p. 6): `W : ℝ → ℝ` is a strictly convex, coercive `C²` function, coercivity read
as superlinear growth `W(m)/|m| → +∞` as `|m| → ∞`. -/
def A24 : Prop :=
  ContDiff ℝ 2 d.W ∧ StrictConvexOn ℝ Set.univ d.W ∧
    Tendsto (fun m : ℝ => d.W m / |m|) (cocompact ℝ) atTop

end MFGPlanning.Existence


