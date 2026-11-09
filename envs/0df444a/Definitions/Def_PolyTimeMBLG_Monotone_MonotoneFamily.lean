-- Prove2me | Definitions.Def_PolyTimeMBLG_Monotone_MonotoneFamily
-- name    : PolyTimeMBLG_Monotone_MonotoneFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:13.747601+00:00
-- url     : https://prove2.me/theorems/e0597aee-a775-4f98-a2a3-9ccf09c968df
-- title:
--   §5 — monotone Boolean functions, maxterms, and the family with at most p(n) maxterms
-- statement:
--   The **inclusion order** on $\{0,1\}^n$ is $x\preceq y$ iff $x_j\le y_j$ for every coordinate $j=1,\dots,n$. A function $f:\{0,1\}^n\to\{0,1\}$ is **monotone** if $x\preceq y$ implies $f(x)\le f(y)$. A **maxterm** of $f$ is a maximal element of $f^{-1}(0)$: a word $x$ with $f(x)=0$ such that $f(y)=1$ for every $y\succ x$. The function $f$ is identified with its language $f^{-1}(1)=\{x: f(x)=1\}$.
--
--   For a polynomial $p$ with real coefficients, the family $F_n$ consists of the languages $f^{-1}(1)$ of all monotone $f:\{0,1\}^n\to\{0,1\}$ such that
--   $$\#\{\text{maxterms of } f\}\le p(n).$$
--
--   This is the family of Theorem 1 and Theorem 11. The constant-one function has no maxterm and the constant-zero function has the single maxterm $1^n$; both belong to $F_n$ whenever $p(n)$ allows. Disjunctions of variables are exactly the monotone functions with one maxterm.
--
--   **Formalization Note** The order is Mathlib's pointwise order on `Fin n → Bool` (with `false < true`), monotonicity is Mathlib's `Monotone`, and a maxterm is `Maximal (fun y => f y = false) x`. The number of maxterms is the cardinality (`Set.ncard`) of a subset of the finite cube. The cap compares this natural number, cast to $\mathbb R$, with $p(n)$ for $p\in\mathbb R[X]$, so every coefficient convention for "polynomial" is covered; where $p(n)<0$ the family is empty.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), §5, inclusion order, monotone function and maxterm, and the family in Theorem 11, p. 7 (Theorem 1, p. 4); identification of f with f⁻¹(1), §2.1 p. 3 and §3 p. 5. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_Generation

namespace PolyTimeMBLG.Monotone

/-- A maxterm of `f : {0,1}ⁿ → {0,1}` (§5, p. 7): a maximal element of `f⁻¹(0)` in the inclusion
order `x ⪯ y ↔ ∀ i, xᵢ ≤ yᵢ` (Mathlib's pointwise order on `Fin n → Bool`, `false < true`). -/
def IsMaxterm {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Prop :=
  Maximal (fun y => f y = false) x

/-- The number of maxterms of `f` (a subset of the finite cube, so `ncard` is its cardinality). -/
noncomputable def numMaxterms {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  {x | IsMaxterm f x}.ncard

/-- The language of `f`: the words on which `f` takes value 1. -/
def language {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => f x = true)

/-- For a polynomial `p` with real coefficients, `Fₙ` is the family of the languages `f⁻¹(1)`
of all monotone `f : {0,1}ⁿ → {0,1}` with at most `p(n)` maxterms. -/
def monotoneFamily (p : Polynomial ℝ) : FamilySeq := fun n =>
  {L | ∃ f : (Fin n → Bool) → Bool, Monotone f ∧
    (numMaxterms f : ℝ) ≤ p.eval (n : ℝ) ∧ L = language f}

end PolyTimeMBLG.Monotone


