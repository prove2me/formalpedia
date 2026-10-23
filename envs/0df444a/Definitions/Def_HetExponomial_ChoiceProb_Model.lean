-- Prove2me | Definitions.Def_HetExponomial_ChoiceProb_Model
-- name    : HetExponomial_ChoiceProb_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:08.477637+00:00
-- url     : https://prove2.me/theorems/addaaef1-65d8-442c-947f-200d02446ef2
-- title:
--   §2, §2.1, pp. 4–6, 43 — HEC model: independent Exp(λ_j) errors, choice probability Q_i, B_i, B_i^+, W_i^−, L_i, L_i^+, G_i (2), levels, B(x)
-- statement:
--   **The heteroscedastic exponomial choice (HEC) model.** Let $N=\{1,\dots,n\}$ be a set of $n\ge 2$ choices. A consumer derives the random utility
--   $$
--   U_i = u_i - z_i, \qquad i\in N,
--   $$
--   from choice $i$, where $u_i\in\mathbb R$ is the *ideal utility* of choice $i$ and $z_i$ is an exponential random variable with rate $\lambda_i>0$ (the *error rate*). The errors $z_1,\dots,z_n$ are independent but not identically distributed. Their densities and distribution functions are
--   $$
--   f_i(z)=\lambda_i e^{-\lambda_i z},\quad F_i(z)=1-e^{-\lambda_i z}\quad (z\ge 0),\qquad f_i(z)=F_i(z)=0\quad (z<0).
--   $$
--
--   This file defines the following objects.
--
--   1. The **error law**: the joint law of $(z_1,\dots,z_n)$ on $\mathbb R^n$, the product of the exponential laws $\mathrm{Exp}(\lambda_j)$.
--   2. The **choice probability** of choice $i$,
--   $$
--   Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \ \forall j\in N,\ j\ne i\},
--   $$
--   computed under the error law.
--   3. The functions $f_i$ and $F_i$ above.
--   4. The choice subsets $B(x)=\{j\in N: u_j\ge x\}$, $B_i=B(u_i)=\{j: u_j\ge u_i\}$, $B_i^+=\{j: u_j>u_i\}$ and $W_i^-=\{j: u_j<u_i\}$.
--   5. The rate sums $L_i=\sum_{j\in B_i}\lambda_j$ and $L_i^+=\sum_{j\in B_i^+}\lambda_j$.
--   6. The exponomial term, equation (2):
--   $$
--   G_i(\mathbf u,\boldsymbol\lambda)=\frac{\lambda_i}{L_i}\cdot\exp\Big[-\sum_{j\in B_i}\lambda_j(u_j-u_i)\Big].
--   $$
--   7. The distinct ideal utilities $a_1<a_2<\dots<a_l$, listed in increasing order.
--   8. The tail integrals $\int_c^\infty \exp\big[-\sum_{j\in B(x)}\lambda_j(u_j-u_i+z)\big]\,dz$ that appear in the proof of Theorem 1, display (16).
--
--   These are the objects of Theorem 1 of the paper, which expresses $Q_i$ in closed form through the $G_k$, and of the steps of its proof.
--
--   **Formalization Note** Choices are indexed by `Fin n`. The error law is `Measure.pi` of Mathlib's `expMeasure (lam j)`, and $Q_i$ is the real value of the measure of the closed event $\{z : u_j - z_j \le u_i - z_i\ \forall j\neq i\}$. The weak inequality is the one printed on the page. $L_i^+$ is defined for every $i$, with value $0$ at a choice of maximal ideal utility, where the paper leaves it undefined. The levels are indexed from $0$: the paper's $a_w$ is `level u ⟨w - 1, _⟩`. The tail integral is a Bochner integral over the open half-line $(c,\infty)$. Rates are not constrained in the definitions; every theorem assumes $\lambda_j>0$ and $n\ge 2$.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), pp. 4–6, §2, §2.1, (1)–(2); p. 43, proof of Theorem 1 (a_1 < … < a_l, B(x), (16))

import Mathlib

namespace HetExponomial.ChoiceProb

open MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-- Joint law of the independent errors `z_j ~ Exp(λ_j)`, `j ∈ N = Fin n` (p. 4):
the product of the exponential laws `expMeasure (lam j)`. -/
noncomputable def errorLaw (lam : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun j => expMeasure (lam j))

/-- The choice probability `Q_i(u, λ) = P{u_i − z_i ≥ u_j − z_j ∀ j ∈ N, j ≠ i}`,
the first line of (1), p. 6. -/
noncomputable def choiceProb (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  (errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}).toReal

/-- The paper's pdf `f_i(z) = λ_i e^{−λ_i z}` for `z ≥ 0`, `0` for `z < 0` (p. 4). -/
noncomputable def pdfExp (r z : ℝ) : ℝ := if 0 ≤ z then r * Real.exp (-(r * z)) else 0

/-- The paper's cdf `F_i(z) = 1 − e^{−λ_i z}` for `z ≥ 0`, `0` for `z < 0` (p. 4). -/
noncomputable def cdfExp (r z : ℝ) : ℝ := if 0 ≤ z then 1 - Real.exp (-(r * z)) else 0

/-- `B(x) = {j ∈ N : u_j ≥ x}` (proof of Theorem 1, p. 43). -/
noncomputable def betterThan (u : Fin n → ℝ) (x : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x ≤ u j)

/-- `B_i = {j ∈ N : u_j ≥ u_i}` (p. 6). -/
noncomputable def better (u : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  betterThan u (u i)

/-- `B_i^+ = {j ∈ N : u_j > u_i}` (p. 6). -/
noncomputable def strictlyBetter (u : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => u i < u j)

/-- `W_i^− = {j ∈ N : u_j < u_i}` (p. 6). -/
noncomputable def strictlyWorse (u : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => u j < u i)

/-- `L_i = ∑_{j ∈ B_i} λ_j` (p. 6). -/
noncomputable def Lsum (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ better u i, lam j

/-- `L_i^+ = ∑_{j ∈ B_i^+} λ_j` (p. 6). The paper defines it only for `u_i < u_max`; here it
is total and equals `0` at a choice of maximal ideal utility. -/
noncomputable def Lplus (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ strictlyBetter u i, lam j

/-- `G_i(u, λ) = (λ_i / L_i) · exp[−∑_{j ∈ B_i} λ_j (u_j − u_i)]`, equation (2), p. 6. -/
noncomputable def G (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  lam i / Lsum u lam i * Real.exp (-(∑ j ∈ better u i, lam j * (u j - u i)))

/-- The set of distinct ideal utilities `{a_1, …, a_l}` (proof of Theorem 1, p. 43). -/
noncomputable def levels (u : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image u

/-- The distinct ideal utilities in increasing order, `a_1 < a_2 < ⋯ < a_l`
(proof of Theorem 1, p. 43), indexed from `0`: the paper's `a_w` is `level u ⟨w - 1, _⟩`. -/
noncomputable def level (u : Fin n → ℝ) : Fin (levels u).card ↪o ℝ :=
  (levels u).orderEmbOfFin rfl

/-- The tail integral `∫_c^∞ exp[−∑_{j ∈ B(x)} λ_j (u_j − u_i + z)] dz` appearing in (16),
p. 43. -/
noncomputable def tailInt (u lam : Fin n → ℝ) (i : Fin n) (x c : ℝ) : ℝ :=
  ∫ z in Set.Ioi c, Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i + z)))

end HetExponomial.ChoiceProb


