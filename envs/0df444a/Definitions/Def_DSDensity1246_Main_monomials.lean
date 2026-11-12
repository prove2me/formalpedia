-- Prove2me | Definitions.Def_DSDensity1246_Main_monomials
-- name    : DSDensity1246_Main_monomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:10:25.277356+00:00
-- url     : https://prove2.me/theorems/dbc88f3c-0603-46e1-b06a-3e43e08ab431
-- title:
--   Full real function space and evaluated bounded-exponent monomials
-- statement:
--   For finite $k$ and $n$, let $[k]=\{1,\ldots,k\}$ and let $W\subseteq[k]^n$. Its real function space is $V_W=\{f:W\to\mathbb R\}$ with pointwise operations. Given exponents $\alpha=(\alpha_i)_{i=1}^n$, the evaluated monomial is $w\mapsto\prod_i w_i^{\alpha_i}$. For natural numbers $\ell,s$, define
--
--   $$M_s^\ell(W)=\left\{w\mapsto\prod_{i=1}^n w_i^{\alpha_i}:\forall i,\ 0\le\alpha_i<k,\quad |\{i:\alpha_i\ge\ell\}|\le s\right\}.$$
--
--   The set consists of functions on $W$. Different exponent witnesses may represent the same function. The ambient function space is defined independently of this set, so spanning is a mathematical assertion rather than a convention.
--
--   **Formalization Note** Labels are stored as $y\in\mathrm{Fin}\,k$ and evaluated as the real number $y.\mathrm{val}+1$. Coordinates use $\mathrm{Fin}\,n$, and exponents are natural numbers. Empty $W$ is permitted.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), §2.1, pp. 7–8, Eq. (7) and footnote 3; restated §4, p. 14

import Mathlib

namespace DSDensity1246.Main

/-- §2.1, pp. 7–8: the full real vector space of functions on W. -/
abbrev FunctionSpace {k n : ℕ} (W : Set (Fin n → Fin k)) := W → ℝ

/-- [k] = {1,…,k}: a zero-based index has real value index + 1. -/
def realLabel {k : ℕ} (y : Fin k) : ℝ := (y.val : ℝ) + 1

/-- Evaluation on W, not a formal polynomial or a chosen exponent witness. -/
def evaluatedMonomial {k n : ℕ} (W : Set (Fin n → Fin k))
    (α : Fin n → ℕ) : FunctionSpace W :=
  fun w => ∏ i : Fin n, realLabel (w.val i) ^ (α i)

/-- Equation (7), p. 8: exponents < k, with at most s exponents ≥ ℓ.
Different exponent vectors are permitted to have the same evaluation on W. -/
noncomputable def monomials {k n : ℕ} (ℓ s : ℕ)
    (W : Set (Fin n → Fin k)) : Set (FunctionSpace W) := by
  classical
  exact {f | ∃ α : Fin n → ℕ, (∀ i, α i < k) ∧
    (Finset.univ.filter (fun i => ℓ ≤ α i)).card ≤ s ∧ f = evaluatedMonomial W α}

end DSDensity1246.Main


