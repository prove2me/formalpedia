-- Prove2me | Definitions.Def_SteinitzExchange_Extension_ConcaveClosure
-- name    : SteinitzExchange_Extension_ConcaveClosure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:40:35.673009+00:00
-- url     : https://prove2.me/theorems/4eff539a-1436-4f2a-97c6-d3983a80fd87
-- title:
--   Concave conjugate $g^\circ$, concave closure $\hat g$, and $\operatorname{argmax}$ over $\overline B$
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a nonempty finite set and $g:B\to\mathbb R$.
--
--   1. The **concave conjugate** of $g$ is $g^\circ:\mathbb R^V\to\mathbb R$,
--   $$g^\circ(p)=\min\{\langle p,x\rangle-g(x)\mid x\in B\}.\qquad(4.1)$$
--   2. The **concave closure** of $g$ is
--   $$\hat g(b)=\inf\{\langle p,b\rangle-g^\circ(p)\mid p\in\mathbb R^V\}.\qquad(4.2)$$
--   It is finite exactly on $\overline B$ (where it is the largest concave function on $\overline B$ lying above $g$ on $B$) and equals $-\infty$ outside $\overline B$; the paper regards it as a function $\hat g:\overline B\to\mathbb R$.
--   3. For $S\subseteq\mathbb R^V$ and $f:\mathbb R^V\to\mathbb R$, $\operatorname{argmax}_S f=\{b\in S\mid f(b)\ge f(c)\ \forall c\in S\}$; with $S=\overline B$ and $f=\hat g$ this is Eq. (4.6).
--
--   The concave closure is the continuous object through which the Extension Theorem relates M-concavity to ordinary concavity.
--
--   **Formalization Note.** $g^\circ$ is a real infimum over the finite index set $B$, which is the minimum when $B$ is nonempty (the junk value for empty $B$ is $0$; every statement assumes $B$ nonempty). $\hat g$ is a real infimum over $p\in\mathbb R^V$: for $b\in\overline B$ the family is bounded below by $\min_B g$ and the value is the paper's; for $b\notin\overline B$ the paper's value is $-\infty$ while the real infimum returns the junk value $0$, so every statement uses $\hat g$ only at points of $\overline B$.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 284, Eqs. (4.1)-(4.3); p. 285, Eqs. (4.4)-(4.6)

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet

namespace SteinitzExchange.Extension

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

/-- The maximizers of a real function `f` on a set `S ⊆ ℝ^V`:
`{b ∈ S | f(b) ≥ f(c) ∀ c ∈ S}` (Murota 1996, p. 285, Eq. (4.6), with `S = B̄`). -/
def argmaxOn {V : Type*} (S : Set (V → ℝ)) (f : (V → ℝ) → ℝ) : Set (V → ℝ) :=
  {b | b ∈ S ∧ ∀ c ∈ S, f c ≤ f b}

end SteinitzExchange.Extension


