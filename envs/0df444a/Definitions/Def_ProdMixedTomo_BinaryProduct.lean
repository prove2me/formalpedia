-- Prove2me | Definitions.Def_ProdMixedTomo_BinaryProduct
-- name    : ProdMixedTomo_BinaryProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:19.523787+00:00
-- url     : https://prove2.me/theorems/518664c5-d00a-4f1d-b2dd-ca762e013ff6
-- title:
--   Distributions on $\{0,1\}^n$, total variation, $\mathrm{Bern}(\nu)$ and $\mathrm{opt}(\mathcal P_n)$
-- statement:
--   A distribution on a finite set is a nonnegative function summing to $1$, and the **total variation distance** is $d_{\mathrm{tv}}(p,q)=\tfrac12\sum_x|p(x)-q(x)|$. For a mean vector $\nu\in[0,1]^n$, the **binary product distribution** $\mathrm{Bern}(\nu)$ on $\{0,1\}^n$ is
--   $$
--   \mathrm{Bern}(\nu)(x)=\prod_{j=1}^n \nu_j^{x_j}(1-\nu_j)^{1-x_j},
--   $$
--   whose $j$-th coordinate equals $1$ with probability $\nu_j$; $\mathcal P_n=\{\mathrm{Bern}(\nu):\nu\in[0,1]^n\}$. For an arbitrary distribution $p$ on $\{0,1\}^n$,
--   $$
--   \mathrm{opt}(\mathcal P_n)(p)=\inf_{\nu\in[0,1]^n} d_{\mathrm{tv}}(\mathrm{Bern}(\nu),p).
--   $$
--   A point $x\in\{0,1\}^n$ is viewed as the $0/1$ vector in $\mathbb R^n$, and $\operatorname{clip}(t)=\max\{0,\min\{1,t\}\}$.
--
--   These are the classical objects of the robust-statistics half of the mission.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation, p.13 (PDF p.15); §2, p.14 (PDF p.16); Definition 1.7, p.5 (PDF p.7); proof of Theorem 3.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ProdMixedTomo_States

namespace ProdMixedTomo

/-!
# Distributions on the cube, total variation, binary product distributions, `opt(P_n)`

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation, p.13 (PDF p.15)
(`d_tv(p, q) = ½‖p − q‖₁`), p.14 (PDF p.16) (`P_n`, product distributions on `{0,1}ⁿ`, determined
by their mean vector), Definition 1.7, p.5 (PDF p.7) (`opt(P_n) = inf_{q ∈ P_n} d_tv(q, p)`),
proof of Theorem 3.1, p.18 (PDF p.20) (`Bern(λ)`).

**Formalization Note.** A distribution on a finite type is a nonnegative function summing to `1`.
`Bern(ν)` for `ν ∈ [0,1]ⁿ` is the product distribution whose `j`-th coordinate is `1` (`true`) with
probability `νⱼ`; its mean vector is `ν`. A point `x ∈ {0,1}ⁿ` is viewed in `ℝⁿ` by `bitVec`.
-/

/-- A probability distribution on a finite type. -/
def IsDist {X : Type*} [Fintype X] (p : X → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- Total variation distance `d_tv(p, q) = ½ Σₓ |p x − q x|`. -/
noncomputable def dtv {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ := (∑ x, |p x - q x|) / 2

/-- The binary product distribution `Bern(ν)` on `{0,1}ⁿ`. -/
noncomputable def bern {n : ℕ} (ν : Fin n → ℝ) (x : Cube n) : ℝ :=
  ∏ j, if x j then ν j else 1 - ν j

/-- The mean vectors of binary product distributions: `[0,1]ⁿ`. -/
def MeanBox (n : ℕ) : Set (Fin n → ℝ) := {ν | ∀ j, 0 ≤ ν j ∧ ν j ≤ 1}

/-- `opt(P_n)(p) = inf_{ν ∈ [0,1]ⁿ} d_tv(Bern ν, p)`. -/
noncomputable def optP {n : ℕ} (p : Cube n → ℝ) : ℝ :=
  sInf ((fun ν => dtv (bern ν) p) '' MeanBox n)

/-- A cube point as a real 0/1 vector. -/
def bitVec {n : ℕ} (x : Cube n) : Fin n → ℝ := fun j => if x j then 1 else 0

/-- The clip of a real to `[0,1]`. -/
noncomputable def clip01 (t : ℝ) : ℝ := max 0 (min 1 t)

end ProdMixedTomo


