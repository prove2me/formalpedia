-- Prove2me | Definitions.Def_WrightPDIPM_CentralPath_LP
-- name    : WrightPDIPM_CentralPath_LP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:14.556874+00:00
-- url     : https://prove2.me/theorems/6076719e-3c15-4748-b5c6-52086a904642
-- title:
--   Standard-form LP: feasible sets F, F°, solution sets Ω_P, Ω_D, Ω, index sets B, N, the set H°, the barrier f_τ and the central path conditions
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$ and $c \in \mathbb{R}^n$, with no assumption on the rank of $A$. The **primal** linear program (2.1) and its **dual** (2.2) are
--
--   $$\min_x\; c^{\mathsf T}x \ \text{ s.t. } Ax = b,\ x \ge 0, \qquad\qquad \max_{\lambda, s}\; b^{\mathsf T}\lambda \ \text{ s.t. } A^{\mathsf T}\lambda + s = c,\ s \ge 0 .$$
--
--   Vector inequalities are componentwise. This file defines the following objects.
--
--   1. Primal feasibility ($Ax = b$, $x \ge 0$), dual feasibility ($A^{\mathsf T}\lambda + s = c$, $s \ge 0$), and their strict versions with $x > 0$, resp. $s > 0$.
--   2. The **primal-dual feasible set** $\mathcal F = \{(x,\lambda,s) : Ax = b,\ A^{\mathsf T}\lambda + s = c,\ (x,s) \ge 0\}$ and the **strictly feasible set** $\mathcal F^\circ$, the same with $(x,s) > 0$.
--   3. The **solution sets** $\Omega_P = \{x^* : x^* \text{ solves (2.1)}\}$ — feasible points with $c^{\mathsf T}x^* \le c^{\mathsf T}x$ for every feasible $x$ — and $\Omega_D = \{(\lambda^*, s^*) : (\lambda^*, s^*) \text{ solves (2.2)}\}$ — feasible pairs with $b^{\mathsf T}\lambda \le b^{\mathsf T}\lambda^*$ for every feasible $(\lambda, s)$ — and $\Omega = \Omega_P \times \Omega_D$, written as triples $(x^*, \lambda^*, s^*)$.
--   4. The index sets $\mathcal B = \{j : x^*_j \neq 0 \text{ for some } x^* \in \Omega_P\}$ and $\mathcal N = \{j : s^*_j \ne 0 \text{ for some } (\lambda^*, s^*) \in \Omega_D\}$.
--   5. The **reduced strictly feasible set** $\mathcal H^\circ = \{(x,s) : (x,\lambda,s) \in \mathcal F^\circ \text{ for some } \lambda \in \mathbb{R}^m\}$ and, for $\tau > 0$, the **primal-dual log barrier**
--
--   $$f_\tau(x,s) = \frac{1}{\tau}\, x^{\mathsf T}s - \sum_{j=1}^n \log(x_j s_j).$$
--
--   6. The **central path conditions** (2.25) for $\tau$: $A^{\mathsf T}\lambda + s = c$, $Ax = b$, $XSe = \tau e$ (that is, $x_j s_j = \tau$ for every $j$, where $X = \operatorname{diag}(x)$, $S = \operatorname{diag}(s)$, $e = (1,\dots,1)^{\mathsf T}$), and $(x,s) > 0$.
--
--   These are the objects of Chapter 2 of Wright's book on which the existence of the central path rests.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, matrices `Matrix (Fin m) (Fin n) ℝ`, triples are `x, λ, s` in that order, and $\lambda$ is written `lam`. $f_\tau$ is defined on all pairs with Lean's `Real.log` (which returns junk values at non-positive arguments); it is meant, and only ever used, on $\mathcal H^\circ$, where every $x_j s_j > 0$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 5, Eqs. (1.7a)–(1.7b); p. 22, (2.1)–(2.2); p. 24 (Ω_P, Ω_D, Ω); p. 26 (strict feasibility); p. 27, Eqs. (2.11a)–(2.11b); p. 36, (2.25a)–(2.25d); p. 37 (H°, f_τ)

import Mathlib

/-!
# Wright, *Primal-Dual Interior-Point Methods* (SIAM 1997), Chapter 2: the standard-form LP

The primal (2.1) `min cᵀx s.t. Ax = b, x ≥ 0` and the dual (2.2) `max bᵀλ s.t. Aᵀλ + s = c, s ≥ 0`
(p. 22), with `A ∈ ℝ^{m×n}` arbitrary (no rank assumption). Vectors are `Fin n → ℝ`; vector
inequalities are componentwise. Primal-dual points are triples `(x, λ, s)`.

* `F`, `Fo` — the feasible and strictly feasible sets (1.7a), (1.7b) (p. 5).
* `OmegaP`, `OmegaD`, `Omega` — the primal, dual and primal-dual solution sets (p. 24).
* `indexB`, `indexN` — the index sets (2.11a), (2.11b) (p. 27).
* `Hcirc`, `ftau` — the reduced strictly feasible set `H°` and the barrier `f_τ` (p. 37).
* `CentralPathConditions` — the system (2.25a)–(2.25d) (p. 36).
-/

namespace WrightPDIPM.CentralPath

open Matrix

/-- Primal feasibility for (2.1): `Ax = b`, `x ≥ 0`. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 ≤ x j

/-- Dual feasibility for (2.2): `Aᵀλ + s = c`, `s ≥ 0`. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ ∀ j, 0 ≤ s j

/-- Strict primal feasibility (p. 26): `Ax = b`, `x > 0`. -/
def StrictlyPrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 < x j

/-- Strict dual feasibility (p. 26): `Aᵀλ + s = c`, `s > 0`. -/
def StrictlyDualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ ∀ j, 0 < s j

/-- The primal-dual feasible set `F` (1.7a): `(x, λ, s)` with `Ax = b`, `Aᵀλ + s = c`,
`(x, s) ≥ 0`. -/
def F {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | PrimalFeasible A b p.1 ∧ DualFeasible A c p.2.1 p.2.2}

/-- The strictly feasible set `F°` (1.7b): `(x, λ, s)` with `Ax = b`, `Aᵀλ + s = c`,
`(x, s) > 0`. -/
def Fo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | StrictlyPrimalFeasible A b p.1 ∧ StrictlyDualFeasible A c p.2.1 p.2.2}

/-- The primal solution set `Ω_P = {x* | x* solves (2.1)}` (p. 24): feasible points whose
objective `cᵀx*` is no larger than that of any feasible point. -/
def OmegaP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | PrimalFeasible A b x ∧ ∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'}

/-- The dual solution set `Ω_D = {(λ*, s*) | (λ*, s*) solves (2.2)}` (p. 24): feasible points
whose objective `bᵀλ*` is no smaller than that of any feasible point. -/
def OmegaD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | DualFeasible A c p.1 p.2 ∧
    ∀ lam' s', DualFeasible A c lam' s' → b ⬝ᵥ lam' ≤ b ⬝ᵥ p.1}

/-- The primal-dual solution set `Ω = Ω_P × Ω_D` (p. 24), as triples `(x*, λ*, s*)`. -/
def Omega {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ OmegaP A b c ∧ (p.2.1, p.2.2) ∈ OmegaD A b c}

/-- The index set `B` (2.11a): `j` with `x*_j ≠ 0` for some `x* ∈ Ω_P`. -/
def indexB {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ x ∈ OmegaP A b c, x j ≠ 0}

/-- The index set `N` (2.11b): `j` with `s*_j ≠ 0` for some `(λ*, s*) ∈ Ω_D`. -/
def indexN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ p ∈ OmegaD A b c, p.2 j ≠ 0}

/-- The reduced strictly feasible set `H° = {(x, s) | (x, λ, s) ∈ F° for some λ ∈ ℝᵐ}`
(p. 37). -/
def Hcirc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {q | ∃ lam : Fin m → ℝ, (q.1, lam, q.2) ∈ Fo A b c}

/-- The primal-dual barrier `f_τ(x, s) = (1/τ) xᵀs − ∑_{j=1}^n log(x_j s_j)` (p. 37). It is
meant on `H°`, where every `x_j s_j > 0`; off `H°` `Real.log` takes its junk values, so every
statement about `f_τ` restricts to `H°`. -/
noncomputable def ftau {n : ℕ} (τ : ℝ) (q : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (1 / τ) * (q.1 ⬝ᵥ q.2) - ∑ j, Real.log (q.1 j * q.2 j)

/-- The central path conditions (2.25a)–(2.25d) (p. 36) for the parameter `τ`:
`Aᵀλ + s = c`, `Ax = b`, `XSe = τe` (i.e. `x_j s_j = τ` for every `j`), `(x, s) > 0`. -/
def CentralPathConditions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ A *ᵥ x = b ∧ (∀ j, x j * s j = τ) ∧ (∀ j, 0 < x j) ∧ (∀ j, 0 < s j)

end WrightPDIPM.CentralPath


