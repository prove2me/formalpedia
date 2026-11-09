-- Prove2me | Definitions.Def_HolonomicPositivity_Robust_Comparison
-- name    : HolonomicPositivity_Robust_Comparison
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:12.9773+00:00
-- url     : https://prove2.me/theorems/65c1b8b8-6adb-4466-a99c-22a0623a1c3a
-- title:
--   Rational-function evaluation, no poles on $\mathbb N$, and the paper's asymptotic comparisons
-- statement:
--   For $U\in\mathbb R(x)$ and real $x$, $U(x)$ denotes evaluation through the reduced numerator and denominator of $U$. The function $U$ has no poles on $\mathbb N=\{0,1,2,\dots\}$ when its reduced denominator has no natural-number root.
--
--   Orders on functions refer to the real variable $x\to+\infty$: $U>V$ means $U(x)>V(x)$ for all sufficiently large real $x$, and $U\ge V$ means $U(x)\ge V(x)$ for all sufficiently large real $x$. For an integer $v$, the relation $U(x)=V(x)+O(x^v)$ means $U-V$ is bounded by a constant multiple of $x^v$ for all large $x$. The paper's two comparisons modulo an error term are
--
--   $$U(x)\ge V(x)+O(x^v)\iff U>V\ \text{ or }\ U(x)=V(x)+O(x^v),$$
--
--   $$U(x)<V(x)+O(x^v)\iff U\le V\ \text{ and }\ U(x)\ne V(x)+O(x^v).$$
--
--   These are defined relations, not inequalities against a chosen error function: the remainder in the Big-O alternative may have either sign. They carry every threshold of the mission.
--
--   **Formalization Note** Lean evaluates a rational function at a pole to the default value $0$. All order relations here are eventual, and each use at a specific natural number is guarded by a no-pole hypothesis or clause. The comparisons take arbitrary real functions, so that thresholds can be written as explicit formulas in $x$.
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2: no-pole convention PDF p.1 (lines 37-39); order on R(x) and comparison (lines 139, 153) PDF p.4; strict comparison (line 166) PDF p.5 (XX:5).

import Mathlib
open Filter Asymptotics

namespace HolonomicPositivity.Robust

/-- Evaluation of a real rational function at a real point. It uses the reduced numerator and
denominator; at a pole the value is Lean's default `num(x) / 0 = 0`, so every use at a specific
index is guarded by `NoPolesOnNat` or by an explicit no-pole clause. -/
noncomputable def ev (U : RatFunc ℝ) (x : ℝ) : ℝ :=
  RatFunc.eval (RingHom.id ℝ) x U

/-- `∞ ∉ U(ℕ)` (PDF p.1, line 38): the reduced denominator has no natural-number root. -/
def NoPolesOnNat (U : RatFunc ℝ) : Prop :=
  ∀ n : ℕ, U.denom.eval (n : ℝ) ≠ 0

/-- The paper's order `U > V` (PDF p.4, line 139): `U(x) > V(x)` for all sufficiently large
real `x`. -/
def EventuallyGT (U V : ℝ → ℝ) : Prop :=
  ∀ᶠ x in atTop, V x < U x

/-- `U ≥ V` in the eventual order: `U(x) ≥ V(x)` for all sufficiently large real `x`. -/
def EventuallyGE (U V : ℝ → ℝ) : Prop :=
  ∀ᶠ x in atTop, V x ≤ U x

/-- `U(x) = V(x) + O(x^v)` as `x → ∞`. -/
def EqMod (U V : ℝ → ℝ) (v : ℤ) : Prop :=
  (fun x => U x - V x) =O[atTop] fun x => x ^ v

/-- `U(x) ≥ V(x) + O(x^v)` (PDF p.4, line 153): `U > V` or `U(x) = V(x) + O(x^v)`. -/
def GeMod (U V : ℝ → ℝ) (v : ℤ) : Prop :=
  EventuallyGT U V ∨ EqMod U V v

/-- `U(x) < V(x) + O(x^v)` (PDF p.5, line 166): `U ≤ V` and `U(x) ≠ V(x) + O(x^v)`. -/
def LtMod (U V : ℝ → ℝ) (v : ℤ) : Prop :=
  EventuallyGE V U ∧ ¬ EqMod U V v

end HolonomicPositivity.Robust


