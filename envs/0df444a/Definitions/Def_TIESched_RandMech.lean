-- Prove2me | Definitions.Def_TIESched_RandMech
-- name    : TIESched_RandMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:52.371353+00:00
-- url     : https://prove2.me/theorems/2c1387bd-11b3-4364-95f5-bc1f71d9bcac
-- title:
--   Randomized mechanism families, truthfulness in expectation, induced fractional mechanism
-- statement:
--   A **randomized mechanism family** outputs, on a report $p$ for a job set $S$, a random integral allocation $X(p)$ (an assignment $S\to[m]$) and payments $\Pi(p)\in\mathbb R^m$ with finite expectations. Here it is given by the joint law of $(X(p),\Pi(p))$, a probability measure on $(S\to[m])\times\mathbb R^m$ for every job set and nonnegative report, under which each $\Pi_i$ is integrable. With $X_{ij}=\mathbf 1\{X\text{ assigns }j\text{ to }i\}$, the expected utility of machine $i$ with true row $c$ under report $p'$ is $\mathbb E[\Pi_i(p')-c\cdot X_i(p')]$.
--
--   The family is **truthful in expectation (TIE)** if for every job set, machine $i$, and nonnegative $p_i,\hat p_i,p_{-i}$,
--   $$\mathbb E\big[\Pi_i(p)-p_i\cdot X_i(p)\big]\ \ge\ \mathbb E\big[\Pi_i(\hat p_i,p_{-i})-p_i\cdot X_i(\hat p_i,p_{-i})\big].$$
--   It has a **$\Gamma$-approximation guarantee in expectation** if $\mathbb E[C(p,X(p))]\le\Gamma\,\mathrm{OPT}(p)$ for every nonempty $S$ and nonnegative $p$ with $\mathrm{OPT}(p)>0$. The **induced fractional mechanism** is $x_{ij}(p)=\mathbb E[X_{ij}(p)]$, $\pi_i(p)=\mathbb E[\Pi_i(p)]$.
--
--   **Formalization Note.** A mechanism with internal randomness on a common probability space pushes forward to this form, and every quantity above depends only on the law. No measurability in the report is required.
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), §2, From randomized mechanisms to fractional mechanisms, p.8

import Mathlib
import Definitions.Def_TIESched_FracMech

set_option autoImplicit false

open MeasureTheory

namespace TIESched

/-- A **randomized mechanism family** (arXiv:2611.05142, §2, *From randomized mechanisms to
fractional mechanisms*, p.8): on report `p` for job set `S`, the mechanism outputs a random integral
allocation `X(p)` (an assignment `S → [m]`) and payments `Π(p) ∈ ℝ^m`. Here the family is given by
the joint law of `(X(p), Π(p))`, one measure on `(S → Fin m) × ℝ^m` per job set and report.

**Formalization Note.** A mechanism described by a common probability space `Ω` and random
variables `X(p), Π(p)` on it induces this form by pushing forward its randomness; every notion the
paper uses (expected utility, expected makespan, the induced fractional mechanism) depends only on
this law. No measurability in the report is required. That each law is a probability measure with
finite expected payments is the predicate `IsRandMech`. -/
abbrev RandMech (m : ℕ) : Type :=
  (S : Finset ℕ) → (Fin m → S → ℝ) → Measure ((S → Fin m) × (Fin m → ℝ))

/-- The family is a randomized mechanism family in the sense of p.8: on every nonnegative report
the output law is a probability measure and the payments `Π_i(p)` have finite expectations. -/
def IsRandMech {m : ℕ} (R : RandMech m) : Prop :=
  ∀ (S : Finset ℕ) (p : Fin m → S → ℝ), IsNonneg p →
    IsProbabilityMeasure (R S p) ∧ ∀ i, Integrable (fun ω => ω.2 i) (R S p)

/-- **Expected utility** of machine `i` with true row `c` when the reported matrix is `p'`:
`E[Π_i(p') − c · X_i(p')]`, where `X_ij = 1{X(p') assigns j to i}` (arXiv:2611.05142, p.8). -/
noncomputable def expUtil {m : ℕ} (R : RandMech m) (S : Finset ℕ) (p' : Fin m → S → ℝ) (i : Fin m)
    (c : S → ℝ) : ℝ :=
  ∫ ω, (ω.2 i - ∑ j, c j * intAlloc ω.1 i j) ∂(R S p')

/-- **Truthful in expectation (TIE)** (arXiv:2611.05142, §2, p.8): "truthful reporting maximizes each
machine's expected utility for every fixed report of the other machines": for every finite job
set, machine `i`, true row `p_i ≥ 0`, deviation `p̂_i ≥ 0` and reports `p_{-i} ≥ 0`,
`E[Π_i(p) − p_i·X_i(p)] ≥ E[Π_i(p̂_i, p_{-i}) − p_i·X_i(p̂_i, p_{-i})]`. -/
def TruthfulInExpectation {m : ℕ} (R : RandMech m) : Prop :=
  ∀ (S : Finset ℕ) (i : Fin m) (p : Fin m → S → ℝ) (q : S → ℝ), IsNonneg p → (∀ j, 0 ≤ q j) →
    expUtil R S (Function.update p i q) i (p i) ≤ expUtil R S p i (p i)

/-- **Γ-approximation guarantee in expectation** (arXiv:2611.05142, §2, p.8, with the scope of the
Γ-approximation guarantee of p.8): `E[C(p, X(p))] ≤ Γ · OPT(p)` for every finite nonempty job set
`S` and every nonnegative report `p` with `OPT(p) > 0`, where `OPT` is the optimal integral
makespan. -/
def IsApproxInExpectation {m : ℕ} [NeZero m] (R : RandMech m) (Γ : ℝ) : Prop :=
  ∀ (S : Finset ℕ) (p : Fin m → S → ℝ), S.Nonempty → IsNonneg p → 0 < OPT p →
    ∫ ω, makespan p (intAlloc ω.1) ∂(R S p) ≤ Γ * OPT p

/-- The **induced fractional mechanism** of a randomized family (arXiv:2611.05142, §2, p.8):
`x_ij(p) = E[X_ij(p)]`, `π_i(p) = E[Π_i(p)]`. -/
noncomputable def inducedFrac {m : ℕ} (R : RandMech m) : FracMech m where
  alloc S p i j := ∫ ω, intAlloc ω.1 i j ∂(R S p)
  pay S p i := ∫ ω, ω.2 i ∂(R S p)

end TIESched


