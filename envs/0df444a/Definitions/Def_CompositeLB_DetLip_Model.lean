-- Prove2me | Definitions.Def_CompositeLB_DetLip_Model
-- name    : CompositeLB_DetLip_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:39.904977+00:00
-- url     : https://prove2.me/theorems/fc0d0058-7496-4a8f-a67a-9829f921b55b
-- title:
--   Equations (1)–(3), pp. 1–3: finite-sum objective, exact component oracle, deterministic run, and hard functions (6)–(7)
-- statement:
--   Let $m\ge2$ component functions $f_i:\mathbb R^d\to\mathbb R$ define the average objective
--
--   $$F(x)=\frac1m\sum_{i=1}^{m}f_i(x).$$
--
--   A query specifies a component $i$, point $x$, and parameter $\beta>0$. Its exact response gives $f_i(x)$, a global subgradient of $f_i$ at $x$, and a minimizer of $f_i(u)+(\beta/2)\|x-u\|^2$ over the feasible set $\mathcal X$. A deterministic algorithm chooses each query from its ordered earlier responses. The run records those responses and the resulting query points. The model also defines the $L$-Lipschitz condition of p. 3, $|g(x)-g(y)|\le L\|x-y\|$ for $x,y\in\mathcal X$, and the hard component functions $f_i$ and truncations $f_i^t$ from equations (6) and (7).
--
--   These definitions fix the oracle model for the lower bound and provide the formulas used by its supporting lemmas.
--
--   **Formalization Note** Components are indexed by `Fin m` from zero, while the paper numbers them from one; query index zero denotes the first query. Prox queries require $\beta>0$, the only case the paper's Lemmas 3 and 5 treat; p. 1 mentions $\beta=0$ only in passing for $m=1$. The proximal point is a minimizer predicate rather than an arbitrary choice. The subgradient is global on $\mathbb R^d$ (Shor's inequality), which is how the paper's components, given by formulas on $\mathbb R^d$, are answered. The value printed as $|f(x)-f(x)|$ on p. 3 is read as $|f(x)-f(y)|$. The exact oracle is a fixed function of each query and is valid even for query points outside $\mathcal X$. The indicator sum is over $r=1,\ldots,k$, and $f_i^t$ uses $r=1,\ldots,t-1$. At $k=0$ the printed coefficient $1/\sqrt{k}$ has no mathematical value; only milestones with $k\ge1$ use these functions.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Eqs. (1)–(3), p. 1; §1 Notation and Definitions, p. 3; Eqs. (6)–(7), p. 5

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient

namespace CompositeLB.DetLip

/-- Euclidean decision space of dimension `d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Equation (1): the average of the `m` component functions. -/
noncomputable def avgF {m d : ℕ} (f : Fin m → E d → ℝ) (x : E d) : ℝ :=
  (1 / (m : ℝ)) * ∑ i : Fin m, f i x

/-- Equation (3): `u` minimizes the proximal objective over the feasible set. -/
def IsProx {d : ℕ} (g : E d → ℝ) (X : Set (E d)) (β : ℝ)
    (x u : E d) : Prop :=
  u ∈ X ∧ ∀ w ∈ X, g u + β / 2 * ‖x - u‖ ^ 2 ≤
    g w + β / 2 * ‖x - w‖ ^ 2

/-- A component, point and positive proximal parameter requested from the oracle. -/
structure Query (m d : ℕ) where
  comp : Fin m
  pt : E d
  beta : ℝ
  beta_pos : 0 < beta

/-- The three entries of the exact component oracle (2). -/
structure Response (d : ℕ) where
  val : ℝ
  grad : E d
  prox : E d

/-- A deterministic algorithm chooses its next query from the ordered answers so far. -/
abbrev DetAlg (m d : ℕ) := List (Response d) → Query m d

/-- A fixed, memoryless selection of exact oracle responses. -/
abbrev Oracle (m d : ℕ) := Query m d → Response d

/-- Ordered responses after `n` queries; query index zero is the first query. -/
def history {m d : ℕ} (A : DetAlg m d) (O : Oracle m d) : ℕ → List (Response d)
  | 0 => []
  | n + 1 => history A O n ++ [O (A (history A O n))]

/-- The query at zero-based index `n`. -/
def query {m d : ℕ} (A : DetAlg m d) (O : Oracle m d) (n : ℕ) : Query m d :=
  A (history A O n)

/-- Oracle (2) with a global subgradient and a prox point in `X`. -/
def IsValidOracle {m d : ℕ} (f : Fin m → E d → ℝ) (X : Set (E d))
    (O : Oracle m d) : Prop :=
  ∀ q : Query m d,
    (O q).val = f q.comp q.pt ∧
    ShorNonsmooth.AlmostDiff.IsSubgradient (f q.comp) q.pt (O q).grad ∧
    IsProx (f q.comp) X q.beta q.pt (O q).prox

/-- The paper's pointwise `L`-Lipschitz condition on `X` (p. 3). -/
def IsLipschitzOn {d : ℕ} (L : ℝ) (g : E d → ℝ) (X : Set (E d)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, |g x - g y| ≤ L * ‖x - y‖

/-- Equation (6), for one component's indicator sequence. -/
noncomputable def hardF {d : ℕ} (b : ℝ) (k : ℕ) (v : ℕ → E d)
    (δ : ℕ → ℝ) (x : E d) : ℝ :=
  1 / Real.sqrt 2 * |b - inner ℝ x (v 0)| +
    1 / (2 * Real.sqrt (k : ℝ)) *
      ∑ r ∈ Finset.Icc 1 k,
        δ r * |inner ℝ x (v (r - 1)) - inner ℝ x (v r)|

/-- Equation (7): the terms numbered `1, …, t-1`. -/
noncomputable def hardFt {d : ℕ} (b : ℝ) (k : ℕ) (v : ℕ → E d)
    (δ : ℕ → ℝ) (t : ℕ) (x : E d) : ℝ :=
  1 / Real.sqrt 2 * |b - inner ℝ x (v 0)| +
    1 / (2 * Real.sqrt (k : ℝ)) *
      ∑ r ∈ Finset.Ico 1 t,
        δ r * |inner ℝ x (v (r - 1)) - inner ℝ x (v r)|

end CompositeLB.DetLip


