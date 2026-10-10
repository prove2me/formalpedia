-- Prove2me | Definitions.Def_SDDiP_Envelope_ProofLP
-- name    : SDDiP_Envelope_ProofLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:45:02.960788+00:00
-- url     : https://prove2.me/theorems/e6f81765-41ec-455f-8054-ec7d5f344bca
-- title:
--   Proof of Theorem 1 — the polyhedron $\Pi$, the function $g(x)=\max_{(\alpha,\beta)\in\Pi}\{\alpha^\top x+\beta\}$ and the linear programs (P), (D)
-- statement:
--   Let $f$ be a real function on $\{0,1\}^n$. The proof of Theorem 1 of Zou, Ahmed and Sun works with the following objects.
--
--   1. The binary vectors $\hat x^1, \dots, \hat x^N$, $N = 2^n$, the columns of the matrix $\hat X$. Here they are indexed by the maps $b : \{1,\dots,n\} \to \{\text{false},\text{true}\}$, the vector $\hat x_b$ having coordinate $1$ exactly where $b$ is true.
--   2. The polyhedron of affine minorants of $f$ on the binary points,
--   $$\Pi = \{(\alpha, \beta) \in \mathbb R^n \times \mathbb R : \alpha^\top x + \beta \le f(x) \text{ for all } x \in \{0,1\}^n\},$$
--   equivalently $y \ge \alpha^\top x + \beta$ for every point $(x,y)$ of the graph $F$ of $f$.
--   3. The linear program $(P)$ at $x \in \mathbb R^n$: maximize $x^\top \alpha + \beta$ over $(\alpha,\beta) \in \Pi$; its set of objective values, and
--   $$g(x) = \max_{(\alpha,\beta)\in\Pi} \{\alpha^\top x + \beta\}.$$
--   4. The dual linear program $(D)$ at $x$:
--   $$\min \sum_{i=1}^N f(\hat x^i)\lambda_i \quad \text{s.t.} \quad \hat X \lambda = x,\ e^\top \lambda = 1,\ \lambda \ge 0,$$
--   with its feasible set and its set of objective values.
--
--   The function $g$ is the proof's candidate for the convex lower envelope; the milestones of the mission show that it is finite and convex piecewise linear on $[0,1]^n$, equals $f$ on $\{0,1\}^n$, and lies above every convex underestimator.
--
--   **Formalization Note** $g(x)$ is written as the real supremum (`sSup`) of the objective values of $(P)$; Lean returns $0$ for the supremum of an unbounded set. Every statement of the mission that uses $g$ first proves that the maximum is attained (`IsGreatest`), so this default value is never relied on. The dual weights are a function $\lambda : (\mathrm{Fin}\ n \to \mathrm{Bool}) \to \mathbb R$.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 496, proof of Theorem 1: F, Π, g, (P), (D)

import Mathlib
import Definitions.Def_SDDiP_Envelope_ConvexLowerEnvelope

namespace SDDiP.Envelope

/-- The binary vector `x̂ ∈ {0,1}ⁿ` encoded by `b : Fin n → Bool` (coordinate `1` where `b` is true).
As `b` ranges over the `N = 2ⁿ` elements of `Fin n → Bool`, `binVec b` lists every binary vector
exactly once: these are the columns `x̂¹, …, x̂ᴺ` of the matrix `X̂` of the proof of Theorem 1. -/
def binVec {n : ℕ} (b : Fin n → Bool) : Fin n → ℝ := fun i => if b i then 1 else 0

/-- The polyhedron `Π = {(α, β) ∈ ℝⁿ⁺¹ : y ≥ αᵀx + β for all (x, y) in the graph F of f}` of the proof
of Theorem 1 (p. 496): the affine functions lying below `f` at every binary point. -/
def PiPoly {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {p | ∀ x ∈ binaryPoints n, p.1 ⬝ᵥ x + p.2 ≤ f x}

/-- The objective values `xᵀα + β`, `(α, β) ∈ Π`, of the linear program (P) at `x` (p. 496). -/
def primalValues {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Set ℝ :=
  {v | ∃ p ∈ PiPoly f, v = p.1 ⬝ᵥ x + p.2}

/-- The function `g(x) = max_{(α,β) ∈ Π} {αᵀx + β}` of the proof of Theorem 1 (p. 496), written as the
real supremum of `primalValues f x`. (`sSup` returns `0` on an unbounded set; the milestones state the
maximum as attained, `IsGreatest`, before using the value.) -/
noncomputable def g {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (primalValues f x)

/-- Feasibility for the dual linear program (D) at `x` (p. 496): `λ ≥ 0`, `eᵀλ = 1`, `X̂λ = x`, the
weights `λ` being indexed by the binary vectors `binVec b`, `b : Fin n → Bool`. -/
def DualFeasible {n : ℕ} (x : Fin n → ℝ) (lam : (Fin n → Bool) → ℝ) : Prop :=
  (∀ b, 0 ≤ lam b) ∧ ∑ b, lam b = 1 ∧ ∑ b, lam b • binVec b = x

/-- The objective values `∑ᵢ ŷⁱ λᵢ = ∑ᵢ f(x̂ⁱ) λᵢ` of the dual program (D) at its feasible points. -/
def dualValues {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Set ℝ :=
  {v | ∃ lam, DualFeasible x lam ∧ v = ∑ b, lam b * f (binVec b)}

end SDDiP.Envelope


