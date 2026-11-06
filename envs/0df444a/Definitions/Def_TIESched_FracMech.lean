-- Prove2me | Definitions.Def_TIESched_FracMech
-- name    : TIESched_FracMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:44:48.874935+00:00
-- url     : https://prove2.me/theorems/e3a003b4-9898-4f7f-b0a4-f98cfcf7719b
-- title:
--   Fractional mechanism families, truthfulness, normalized utility, $\Gamma$-approximation
-- statement:
--   An **allocation family** $x=(x^S)_S$ assigns to every finite job set $S\subseteq\mathbb N$ and report $p$ a matrix $x^S(p)\in\mathbb R^{m\times S}$; it is **feasible** if on every nonnegative report $x^S(p)\ge 0$ and $\sum_{i=1}^m x^S_{ij}(p)=1$ for every job $j$ (a fractional allocation). A **fractional mechanism family** $M=(x^S,\pi^S)_S$ adds payment rules $\pi^S:\mathbb R^{m\times S}_{\ge0}\to\mathbb R^m$, the payment $\pi^S_i(p)$ going to machine $i$.
--
--   Utilities are quasilinear. $M$ is **truthful** if for every finite job set, every machine $i$ and all nonnegative $p_i,\hat p_i,p_{-i}$,
--   $$\pi_i(p)-p_i\cdot x_i(p)\ \ge\ \pi_i(\hat p_i,p_{-i})-p_i\cdot x_i(\hat p_i,p_{-i}).$$
--   The **normalized utility** is $u_i(p)=\pi_i(p)-p_i\cdot x_i(p)-\pi_i(0,p_{-i})$, so $u_i(0,p_{-i})=0$ and $u^\emptyset_i=0$. The family is **$\Gamma$-approximate** if
--   $$C\big(p,x^S(p)\big)\le\Gamma\,\mathrm{OPT}(p)$$
--   for every finite nonempty job set $S$ and every nonnegative $p$ with $\mathrm{OPT}(p)>0$.
--
--   These are the objects of the main theorem: the lower bound is about truthful, $\Gamma$-approximate feasible families on the full nonnegative domain.
--
--   **Formalization Note.** Rules are total functions; feasibility, truthfulness and the guarantee constrain nonnegative reports only. Payments are real, hence finite. $(\hat p_i,p_{-i})$ is `Function.update p i q`. $\Gamma$ is any real number.
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), §2, Mechanisms and truthfulness, Normalized utility, Approximation guarantee, pp.7–8

import Mathlib
import Definitions.Def_TIESched_OPT

set_option autoImplicit false

namespace TIESched

/-- An **allocation family** `x = (x^S)_S`: for every finite job set `S ⊆ ℕ`, a rule mapping a
report `p ∈ ℝ^{m×S}` to a matrix `x^S(p) ∈ ℝ^{m×S}` (arXiv:2611.05142, §2, p.7).

**Formalization Note.** The rule is a total function; only its values on nonnegative reports
matter, and feasibility (`Feasible`) is imposed on those only. -/
abbrev AllocFamily (m : ℕ) : Type :=
  (S : Finset ℕ) → (Fin m → S → ℝ) → (Fin m → S → ℝ)

/-- **Feasible allocation family**: on every nonnegative report the output is a fractional
allocation, `x ≥ 0` and `Σ_{i=1}^m x_ij = 1` for every job `j` (arXiv:2611.05142, §2, p.7: "A
fractional allocation is a matrix `x ∈ ℝ^{m×n}_{≥0}` satisfying `Σ_i x_ij = 1`", and the allocation
rule maps `ℝ^{m×S}_{≥0}` into `X(S)`). -/
def Feasible {m : ℕ} (x : AllocFamily m) : Prop :=
  ∀ (S : Finset ℕ) (p : Fin m → S → ℝ), IsNonneg p →
    (∀ i j, 0 ≤ x S p i j) ∧ ∀ j, ∑ i, x S p i j = 1

/-- A **fractional mechanism family** `M = (x^S, π^S)_S`: for every finite job set `S`, an
allocation rule `x^S` and a payment rule `π^S : ℝ^{m×S}_{≥0} → ℝ^m`, the payment `π^S_i(p)` being
made to machine `i` (arXiv:2611.05142, §2, *Mechanisms and truthfulness*, p.7).

**Formalization Note.** Payments are real numbers, hence finite at every report (p.7). Both rules
are total functions; every property below constrains nonnegative reports only. That the allocation
is a fractional allocation is the separate predicate `Feasible M.alloc`. -/
structure FracMech (m : ℕ) where
  /-- the allocation rules `x^S` -/
  alloc : AllocFamily m
  /-- the payment rules `π^S` -/
  pay : (S : Finset ℕ) → (Fin m → S → ℝ) → Fin m → ℝ

/-- **Truthfulness** (arXiv:2611.05142, §2, p.7): for every finite job set, every machine `i`, and
all `p_i, p̂_i, p_{-i}`,
`π_i(p) − p_i · x_i(p) ≥ π_i(p̂_i, p_{-i}) − p_i · x_i(p̂_i, p_{-i})`.

**Formalization Note.** All three of `p_i, p̂_i, p_{-i}` range over nonnegative vectors only (each
machine "may report any vector in `ℝ^n_{≥0}`", p.7); `(p̂_i, p_{-i})` is `Function.update p i q`. -/
def Truthful {m : ℕ} (M : FracMech m) : Prop :=
  ∀ (S : Finset ℕ) (i : Fin m) (p : Fin m → S → ℝ) (q : S → ℝ), IsNonneg p → (∀ j, 0 ≤ q j) →
    M.pay S (Function.update p i q) i - ∑ j, p i j * M.alloc S (Function.update p i q) i j ≤
      M.pay S p i - ∑ j, p i j * M.alloc S p i j

/-- **Normalized utility** under truthful reporting (arXiv:2611.05142, §2, p.7):
`u_i(p) = π_i(p) − p_i · x_i(p) − π_i(0, p_{-i})`, where `0` is the all-zero row on the current job
set. On the empty job set this is `0` automatically (the report is the unique empty matrix). -/
noncomputable def normalizedUtility {m : ℕ} (M : FracMech m) (S : Finset ℕ) (p : Fin m → S → ℝ)
    (i : Fin m) : ℝ :=
  M.pay S p i - ∑ j, p i j * M.alloc S p i j - M.pay S (Function.update p i 0) i

/-- **Γ-approximate** family (arXiv:2611.05142, §2, *Approximation guarantee*, p.8): one finite
constant `Γ` satisfies `C(p, x^S(p)) ≤ Γ · OPT(p)` for every finite nonempty job set `S` and every
(nonnegative) processing-time matrix `p` with `OPT(p) > 0`.

**Formalization Note.** `Γ` is any real number; `OPT` is the optimal *integral* makespan. -/
def IsApprox {m : ℕ} [NeZero m] (M : FracMech m) (Γ : ℝ) : Prop :=
  ∀ (S : Finset ℕ) (p : Fin m → S → ℝ), S.Nonempty → IsNonneg p → 0 < OPT p →
    makespan p (M.alloc S p) ≤ Γ * OPT p

end TIESched


