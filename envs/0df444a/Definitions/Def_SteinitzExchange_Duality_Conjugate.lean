-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Conjugate
-- name    : SteinitzExchange_Duality_Conjugate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:54:17.489914+00:00
-- url     : https://prove2.me/theorems/c8dd7d4a-2a0f-4850-bc12-e19c34b9f598
-- title:
--   Concave and convex conjugates $g^\circ$, $f^\bullet$ and concave and convex closures $\hat g$, $\check f$
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be finite and nonempty, and let $g,f:B\to\mathbb R$. The **concave conjugate** of $g$ and the **convex conjugate** of $f$ are the functions $\mathbb R^V\to\mathbb R$
--
--   $$g^\circ(p)=\min\{\langle p,x\rangle-g(x)\mid x\in B\},\qquad f^\bullet(p)=\max\{\langle p,x\rangle-f(x)\mid x\in B\}.$$
--
--   The **concave closure** of $g$ and the **convex closure** of $f$ are
--
--   $$\hat g(b)=\inf\{\langle p,b\rangle-g^\circ(p)\mid p\in\mathbb R^V\},\qquad \check f(b)=\sup\{\langle p,b\rangle-f^\bullet(p)\mid p\in\mathbb R^V\}.$$
--
--   For $b$ in the convex hull $\overline B$ both closures are finite: $\hat g$ is the smallest concave function on $\overline B$ lying above $g$ on $B$, and $\check f$ the largest convex function lying below $f$. Outside $\overline B$ the paper's values are $\hat g(b)=-\infty$ and $\check f(b)=+\infty$, and the paper regards both closures as functions on $\overline B$ only.
--
--   **Formalization Note.** All four are real-valued: the min/max is a real `⨅`/`⨆` over the finite index set $B$ (attained when $B\neq\emptyset$; junk value $0$ when $B=\emptyset$, which no statement uses), and the closures are real `⨅`/`⨆` over $p\in\mathbb R^V$. For $b\notin\overline B$ the family is unbounded and the real infimum/supremum is the junk value $0$ instead of $\mp\infty$; therefore every statement of the mission evaluates `concaveClosure B g` and `convexClosure B f` only at points of `hull B`.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 284, Eqs. (4.1), (4.2); p. 293, Eqs. (6.1), (6.2); p. 294, Eq. (6.3)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet

namespace SteinitzExchange.Duality

/-- The concave conjugate `g°(p) = min{⟨p, x⟩ − g(x) | x ∈ B}` of `g : B → ℝ` for a nonempty
finite `B ⊆ ℤ^V` (Murota 1996, p. 284, Eq. (4.1)). For nonempty `B` the infimum over the finite
index set is the minimum; for empty `B` the value is the junk value `0`, and every statement
assumes `B` nonempty. -/
noncomputable def concaveConj {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (p : V → ℝ) : ℝ :=
  ⨅ x : (B : Set (V → ℤ)), (pairing p (toReal (x : V → ℤ)) - g x)

/-- The concave closure `ĝ(b) = inf{⟨p, b⟩ − g°(p) | p ∈ ℝ^V}` (Murota 1996, p. 284, Eq. (4.2)).
For `b ∈ B̄` the family is bounded below (by `min g`) and this real infimum is the paper's value;
for `b ∉ B̄` the paper's value is `−∞` and this real infimum is the junk value `0`, so every
statement uses `concaveClosure` only at points of `B̄` (the paper regards `ĝ` as `ĝ : B̄ → ℝ`). -/
noncomputable def concaveClosure {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (b : V → ℝ) : ℝ :=
  ⨅ p : V → ℝ, (pairing p b - concaveConj B g p)

/-- The convex conjugate `f•(p) = max{⟨p, x⟩ − f(x) | x ∈ B}` of `f : B → ℝ` for a nonempty
finite `B ⊆ ℤ^V` (Murota 1996, p. 293, Eq. (6.1)). For nonempty `B` the supremum over the finite
index set is the maximum; for empty `B` the value is the junk value `0`, and every statement
assumes `B` nonempty. -/
noncomputable def convexConj {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (f : (V → ℤ) → ℝ) (p : V → ℝ) : ℝ :=
  ⨆ x : (B : Set (V → ℤ)), (pairing p (toReal (x : V → ℤ)) - f x)

/-- The convex closure `f̌(b) = sup{⟨p, b⟩ − f•(p) | p ∈ ℝ^V}` (Murota 1996, p. 293, Eq. (6.2)).
For `b ∈ B̄` the family is bounded above (by `max f`) and this real supremum is the paper's value;
for `b ∉ B̄` the paper's value is `+∞` (Eq. (6.3)) and this real supremum is the junk value `0`,
so every statement uses `convexClosure` only at points of `B̄` (the paper regards `f̌` as
`f̌ : B̄ → ℝ`). -/
noncomputable def convexClosure {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (f : (V → ℤ) → ℝ) (b : V → ℝ) : ℝ :=
  ⨆ p : V → ℝ, (pairing p b - convexConj B f p)

end SteinitzExchange.Duality


