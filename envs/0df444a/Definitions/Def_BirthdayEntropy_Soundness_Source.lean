-- Prove2me | Definitions.Def_BirthdayEntropy_Soundness_Source
-- name    : BirthdayEntropy_Soundness_Source
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:49:12.572192+00:00
-- url     : https://prove2.me/theorems/2b77e22c-ba59-4673-b8eb-c6c6e88ff9c3
-- title:
--   Indexed Boolean ternary sources and quantitative scales
-- statement:
--   A Boolean ternary constraint satisfaction instance has variables $[n]$, indexed constraints $[m]$, three distinct variables in each constraint, and an arbitrary Boolean predicate on their three values. Repeated scopes, including scopes with different predicates, remain separate constraints. This specializes the published indexed CSP rather than reconstructing a CSP model.
--
--   The source condition requires every variable to occur and bounds its occurrence count by a real number $d$. The NO promise is
--   $$\forall g\in\{0,1\}^{[n]},\quad \#\{j:g\text{ violates constraint }j\}\ge\varepsilon m.$$
--   Satisfiability separately means that some assignment satisfies every indexed constraint. Write $x=\ell/n$, $A_0=\log(e/x)$, and set $\beta=\min\{1/4,\varepsilon/(48d)\}$. For $d\ge1,\varepsilon>0$, this satisfies the source requirement $2d\beta<(\varepsilon/3)/2$. Admitted scales mean $2\le\ell\le x_0n$ and $\ell A_0\ge C_0\log(n+1)$; repetitions are $\lceil C_*A_0/x\rceil$.
--
--   These definitions specify the source class and scalar parameters without including any desired soundness or entropy bound. Divisions and logarithms are used only on the positive domains stated by the theorems.
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, §2, PDF p3 / printed p2; §4, PDF pp6,8–10 / printed pp5,7–9, equations (4)–(5)

import Mathlib
import Definitions.Def_RandOrderCSP_CSP

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Popa, §2, PDF p3 (printed p2): indexed Boolean ternary CSP.
The imported hypergraph has injective rows and permits repeated scopes. -/
abbrev CSP (n m : ℕ) := RandOrderCSP.CSP 3 Bool (Fin n) (Fin m)

/-- Every variable occurs, with its integer incidence count bounded by the real d. -/
def Source {n m : ℕ} (φ : CSP n m) (d : ℝ) : Prop :=
  ∀ v, 0 < φ.H.deg v ∧ (φ.H.deg v : ℝ) ≤ d

/-- The fraction-of-all-indexed-constraints NO promise, §2. -/
def Gap {n m : ℕ} (φ : CSP n m) (ε : ℝ) : Prop :=
  ∀ g : Fin n → Bool,
    ε * (m : ℝ) ≤ ((Finset.univ.filter (fun j => φ.f j (g ∘ φ.H.M j) = false)).card : ℝ)

/-- Satisfaction of every indexed constraint; no gap is assumed. -/
def Satisfiable {n m : ℕ} (φ : CSP n m) : Prop :=
  ∃ g : Fin n → Bool, ∀ j, φ.f j (g ∘ φ.H.M j) = true

/-- §4: gamma=epsilon/3 follows from nonisolation. This fixed beta is
positive and satisfies 2*d*beta < gamma/2 for d≥1 and epsilon>0. -/
def beta (d ε : ℝ) : ℝ := min (1 / 4) (ε / (48 * d))

/-- The source sampling ratio and natural logarithmic factor. -/
def ratio (n ℓ : ℕ) : ℝ := (ℓ : ℝ) / n

def logScale (n ℓ : ℕ) : ℝ := Real.log (Real.exp 1 / ratio n ℓ)

/-- Both quantitative scale conditions in Theorem 2.1. -/
def Admitted (n ℓ : ℕ) (C₀ x₀ : ℝ) : Prop :=
  2 ≤ ℓ ∧ (ℓ : ℝ) ≤ x₀ * n ∧
    C₀ * Real.log ((n : ℝ) + 1) ≤ (ℓ : ℝ) * logScale n ℓ

/-- Equation (4), with the ceiling taken in the nonnegative integers. -/
def repetition (n ℓ : ℕ) (C : ℝ) : ℕ := ⌈C * logScale n ℓ / ratio n ℓ⌉₊

end BirthdayEntropy.Soundness


