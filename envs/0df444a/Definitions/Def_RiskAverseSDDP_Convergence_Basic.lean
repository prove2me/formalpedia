-- Prove2me | Definitions.Def_RiskAverseSDDP_Convergence_Basic
-- name    : RiskAverseSDDP_Convergence_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:44:20.292101+00:00
-- url     : https://prove2.me/theorems/dbcdf232-d8c0-4795-9e38-493fe3072494
-- title:
--   Extended-real convexity, properness and subdifferentials; decision histories in $\mathbb R^{ns}$ with the Euclidean norm (pp. 2–3)
-- statement:
--   Elementary vocabulary shared by both missions on Guigues (2016): extended-real convex analysis and the space of decision histories.
--
--   Write $\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}$.
--
--   1. A function $g:Z\to\overline{\mathbb R}$ is **proper** if $g(z)>-\infty$ for every $z$ and $g(z)<+\infty$ for at least one $z$.
--   2. A function $g:Z\to\overline{\mathbb R}$ on a real vector space $Z$ is **convex** if its epigraph $\{(z,r)\in Z\times\mathbb R:\ g(z)\le r\}$ is a convex set.
--   3. For $g:E\to\overline{\mathbb R}$ on a real inner product space $E$ and $x\in E$, the **subdifferential** of $g$ at $x$ is
--   $$
--   \partial g(x)=\{s\in E:\ g(y)\ge g(x)+\langle s,y-x\rangle\ \text{for all } y\in E\}.
--   $$
--   4. A **decision history** $x_{1:s}=(x_1,\dots,x_s)$ with $x_i\in\mathbb R^n$ is identified, as in the notation list of the paper (pp. 2–3), with the concatenated vector $[x_1;\dots;x_s]\in\mathbb R^{ns}$. The space of histories therefore carries the inner product $\langle x,y\rangle=\sum_{i=1}^s\langle x_i,y_i\rangle$ and the Euclidean norm $\|x\|=\big(\sum_{i=1}^s\|x_i\|_2^2\big)^{1/2}$ (p. 3: "the usual scalar product … the corresponding norm $\|x\|=\|x\|_2$").
--   5. The **empty history** is the unique history with $s=0$, and **appending** a decision is the map $(x_{1:s},y)\mapsto x_{1:s+1}$ with $x_{s+1}=y$.
--
--   The paper uses these notions without defining them; items 1–3 are the standard ones (Rockafellar, *Convex Analysis*, §§4 and 23). Properness and convexity express assumption (H) of §2 and (H2) of §3; the subdifferential is the object of Lemma 2.1 and Proposition 2.2 and the set from which the cut slopes of Algorithm 1 are taken; histories are the arguments of the recourse functions $\mathcal Q_t(x_{1:t-1})$, and their Euclidean norm is the one in which the $\varepsilon$-fattenings (2.2), the cuts and the Lipschitz constants of §3 are measured.
--
--   **Formalization Note** Values in $\overline{\mathbb R}$ are `EReal`. The subdifferential is the inequality in `EReal` read literally: at a point where $g(x)=+\infty$ it is empty for a proper $g$, and at a point where $g(x)=-\infty$ it is the whole space (Rockafellar's convention); every statement that uses it applies it where the function is finite. Histories are `PiLp 2 (fun _ : Fin s => EuclideanSpace ℝ (Fin n))`, the $L^2$ product of $s$ copies of $\mathbb R^n$, whose norm is exactly the Euclidean norm of the concatenation (a plain function type would carry the sup norm); decisions are indexed from $0$, so $x_i$ of the paper is coordinate $i-1$. `EProper` and `EConvex` coincide word for word with the published `ConvexSDDP.Det.Basic` notions of Girardeau–Leclère–Philpott; they are restated here because that module is not available in the drafting workspace.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, pp. 2–3, notation list

import Mathlib

namespace RiskAverseSDDP.Convergence

/-- A function into `ℝ ∪ {±∞}` (`EReal`) is *proper* when it never takes the value `-∞` and is
not identically `+∞`. -/
def EProper {Z : Type*} (g : Z → EReal) : Prop :=
  (∀ z, g z ≠ ⊥) ∧ ∃ z, g z ≠ ⊤

/-- A function `g : Z → ℝ ∪ {±∞}` on a real vector space is *convex* when its epigraph
`{(z, r) ∈ Z × ℝ | g z ≤ r}` is a convex set. -/
def EConvex {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (g : Z → EReal) : Prop :=
  Convex ℝ {q : Z × ℝ | g q.1 ≤ (q.2 : EReal)}

/-- The subdifferential `∂g(x)` of an extended-real function on a real inner product space:
the vectors `s` with `g(y) ≥ g(x) + ⟨s, y - x⟩` for every `y`. -/
def ESubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : E → EReal)
    (x : E) : Set E :=
  {s | ∀ y, g x + ((inner ℝ s (y - x) : ℝ) : EReal) ≤ g y}

/-- A decision history `x_{1:s} = (x_1, …, x_s)` with `x_i ∈ ℝⁿ`, identified with the vector
`[x_1; …; x_s] ∈ ℝ^{ns}` (p. 2): the `L²` product of `s` copies of `ℝⁿ`, so that its norm is
the Euclidean norm `(Σ_i ‖x_i‖²)^{1/2}` of the concatenated vector and its inner product is
`Σ_i ⟨x_i, y_i⟩`. -/
abbrev Hist (n s : ℕ) : Type := PiLp 2 (fun _ : Fin s => EuclideanSpace ℝ (Fin n))

/-- The empty history (`s = 0`). -/
def Hist.empty (n : ℕ) : Hist n 0 := WithLp.toLp 2 (fun i => Fin.elim0 i)

/-- Appending a decision: `(x_{1:s}, y) ↦ x_{1:s+1}` with `x_{s+1} = y`. -/
def Hist.snoc {n s : ℕ} (x : Hist n s) (y : EuclideanSpace ℝ (Fin n)) : Hist n (s + 1) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => EuclideanSpace ℝ (Fin n)) (fun i => x i) y)

end RiskAverseSDDP.Convergence


