-- Prove2me | Definitions.Def_OptAbstention_TLA_Reweighting
-- name    : OptAbstention_TLA_Reweighting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:05.882848+00:00
-- url     : https://prove2.me/theorems/d2346eab-d90c-4975-8825-7c6389835cc3
-- title:
--   Reweightings, $(\tau,R)$-good reweightings and the linear program $\mathrm{LP}_{\mathrm{TLA}}$
-- statement:
--   For a finite multiset $S$, $\Delta(S)$ is the set of probability vectors $w\in[0,1]^S$ with $\sum_x w_x=1$, and $\Delta_R(S)=\{w\in\Delta(S):\|w\|_\infty\le R/|S|\}$. For nonempty multisets $S_{\mathrm{train}},S_{\mathrm{test}}\subseteq X$, a pair $(u,w)\in\Delta(S_{\mathrm{train}})\times\Delta(S_{\mathrm{test}})$ is a **reweighting**; it is **$(\tau,R)$-good** with respect to $(h,\ell)$, $h:X\to\{\pm1\}$, if for every $\alpha\in\mathbb N^d$ with $\|\alpha\|_1\le\ell$
--   $$\Big|\sum_{x\in S_{\mathrm{test}}}w_x x^\alpha-\sum_{x\in S_{\mathrm{train}}}u_x x^\alpha\Big|\le\tau,\qquad \Big|\sum_{x\in S_{\mathrm{test}}}w_x h(x)x^\alpha-\sum_{x\in S_{\mathrm{train}}}u_x h(x)x^\alpha\Big|\le\tau,$$
--   and $\|u\|_\infty\le R/|S_{\mathrm{train}}|$. $\mathrm{LP}_{\mathrm{TLA}}(S_{\mathrm{train}},S_{\mathrm{test}},h,\ell,\tau,R)$ maximizes $\sum_{x\in S_{\mathrm{test}}}z_x$ over $(u,w,z)$ with $(u,w)$ $(\tau,R)$-good, $z_x\le R^{-1}|S_{\mathrm{test}}|w_x$ and $z_x\le1$. A feasible point is optimal when its objective is at least that of every feasible point.
--
--   **Formalization Note.** Multisets are lists, weights are indexed by occurrences.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), pp. 12–13, §5 Probability; p. 13, Definition 6.3; p. 14, Definition 6.4; p. 15, Algorithm 1

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching

/-!
# Reweightings, good reweightings and the linear program LP_TLA

Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, *Achieving the Optimal Abstention Rate
for Learning with Distribution Shift*, STOC 2027 submission (manuscript sha256 0fb30af1…):
§5 "Probability" (`∆(S)`, `∆_R(S)`, pp. 12–13), Definition 6.3 (p. 13), Definition 6.4 (p. 14),
Algorithm 1 (p. 15).

Conventions. Multisets are lists `Fin m → X` (occurrences indexed); a weight vector on a multiset
is a function on its indices. `E_{x∼R^w_test}[g(x)] = ∑_j w_j g(S_test j)`.
-/

namespace OptAbstention.TLA

/-- `w ∈ ∆(S)`: a probability vector on the occurrences (`w ∈ [0,1]^S`, `‖w‖₁ = 1`). -/
def IsProbVec {m : ℕ} (w : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

/-- `w ∈ ∆_R(S)`: a probability vector with `‖w‖_∞ ≤ R/|S|`. -/
def IsCappedProbVec {m : ℕ} (R : ℝ) (w : Fin m → ℝ) : Prop :=
  IsProbVec w ∧ ∀ i, w i ≤ R / m

/-- Definitions 6.3–6.4: `(u, w) ∈ ∆(S_train) × ∆(S_test)` is a `(τ, R)`-good reweighting of
`(S_train, S_test)` with respect to `(h, ℓ)`: moment matching and Chow matching up to `τ` for
every `‖α‖₁ ≤ ℓ`, and the cap `‖u‖_∞ ≤ R/|S_train|`. -/
def IsGoodReweighting {d : ℕ} {X : Set (Pt d)} {m n : ℕ} (Strain : Fin m → X)
    (Stest : Fin n → X) (h : X → ℝ) (ℓ : ℕ) (τ R : ℝ) (u : Fin m → ℝ) (w : Fin n → ℝ) : Prop :=
  IsProbVec u ∧ IsProbVec w ∧
    (∀ α : Fin d → ℕ, degOf α ≤ ℓ →
      |∑ j, w j * mono α (Stest j : Pt d) - ∑ i, u i * mono α (Strain i : Pt d)| ≤ τ) ∧
    (∀ α : Fin d → ℕ, degOf α ≤ ℓ →
      |∑ j, w j * (h (Stest j) * mono α (Stest j : Pt d)) -
        ∑ i, u i * (h (Strain i) * mono α (Strain i : Pt d))| ≤ τ) ∧
    ∀ i, u i ≤ R / m

/-- Algorithm 1: `(u, w, z)` is a feasible point of `LP_TLA(S_train, S_test, h, ℓ, τ, R)`:
`(u, w)` is `(τ, R)`-good and `z_x ≤ R⁻¹ |S_test| w_x`, `z_x ≤ 1` for every `x ∈ S_test`. -/
def LPFeasible {d : ℕ} {X : Set (Pt d)} {m n : ℕ} (Strain : Fin m → X) (Stest : Fin n → X)
    (h : X → ℝ) (ℓ : ℕ) (τ R : ℝ) (u : Fin m → ℝ) (w z : Fin n → ℝ) : Prop :=
  IsGoodReweighting Strain Stest h ℓ τ R u w ∧ ∀ j, z j ≤ R⁻¹ * n * w j ∧ z j ≤ 1

/-- `LP_TLA(S_train, S_test, h, ℓ, τ, R)` is feasible. -/
def LPIsFeasible {d : ℕ} {X : Set (Pt d)} {m n : ℕ} (Strain : Fin m → X) (Stest : Fin n → X)
    (h : X → ℝ) (ℓ : ℕ) (τ R : ℝ) : Prop :=
  ∃ u w z, LPFeasible Strain Stest h ℓ τ R u w z

/-- `(u, w, z)` is an optimal solution of `LP_TLA(S_train, S_test, h, ℓ, τ, R)`: feasible, and
`∑_x z_x` is maximal among feasible points. -/
def LPOptimal {d : ℕ} {X : Set (Pt d)} {m n : ℕ} (Strain : Fin m → X) (Stest : Fin n → X)
    (h : X → ℝ) (ℓ : ℕ) (τ R : ℝ) (u : Fin m → ℝ) (w z : Fin n → ℝ) : Prop :=
  LPFeasible Strain Stest h ℓ τ R u w z ∧
    ∀ u' w' z', LPFeasible Strain Stest h ℓ τ R u' w' z' → ∑ j, z' j ≤ ∑ j, z j

end OptAbstention.TLA


