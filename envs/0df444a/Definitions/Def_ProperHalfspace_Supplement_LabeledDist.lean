-- Prove2me | Definitions.Def_ProperHalfspace_Supplement_LabeledDist
-- name    : ProperHalfspace_Supplement_LabeledDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:49:20.056644+00:00
-- url     : https://prove2.me/theorems/cd73bc89-211a-4253-b08a-2dafd4345220
-- title:
--   Labeled distributions on $\{\pm1\}^n\times\{\pm1\}$ with uniform marginal, $\mathrm{err}_D$ and $\mathrm{OPT}_D$
-- statement:
--   A **labeled distribution** is a probability distribution $D$ on $\{\pm1\}^n\times\{\pm1\}$. It has **uniform marginal** if its marginal on $\{\pm1\}^n$ is uniform:
--   $$D(x,1)+D(x,-1)=2^{-n}\qquad\text{for every }x\in\{\pm1\}^n,$$
--   with $D\ge0$. The conditional law of the label $y$ given $x$ is arbitrary, so labels may be randomized even after conditioning on $x$. For $h:\{\pm1\}^n\to\mathbb R$,
--   $$\mathrm{err}_D(h)=\Pr_{(x,y)\sim D}[h(x)\ne y],\qquad \mathrm{OPT}_D=\min_{h\in\mathcal H_n}\mathrm{err}_D(h),$$
--   where $\mathcal H_n$ is the class of halfspaces $\operatorname{sign}(w\cdot x-\theta)$, constants included.
--
--   These are the objects in which the sample-based learning guarantee (Theorem 2) is stated.
--
--   **Formalization Note** $D$ is a probability mass function on the finite set `Cube n × ℤˣ`, and $\mathrm{err}_D$ is a finite sum. $\mathrm{OPT}_D$ is an infimum over all parameters $(w,\theta)$ of the mission's published halfspaces; only finitely many functions on the cube arise, so it is attained.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), §1.1, p.2 (definitions of err_D and OPT_D before Theorem 2)

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace

namespace ProperHalfspace

/-!
# Labeled distributions with uniform marginal, their error and OPT

De, Mossel, Nadimpalli, Neeman, *Efficient Proper Agnostic Learning of Halfspaces*, arXiv:2611.02344 (Nov. 1, 2026),
§1.1, p.2 (PDF p.4): "let D be a distribution on {±1}ⁿ × {±1} whose marginal on x is uniform, and write
errD(h) := Pr_{(x,y)∼D}[h(x) ≠ y], OPTD := min_{h∈Hn} errD(h). Here the labels may be randomized even after conditioning on x."

**Formalization Note.** A labeled example is a pair `(x, y) : Cube n × ℤˣ`. A distribution is a probability mass function
`D : Cube n × ℤˣ → ℝ`; `IsUniformMarginal D` asks `D ≥ 0` and `D (x, 1) + D (x, −1) = 2⁻ⁿ` for every `x`, which forces total
mass `1` and is exactly "the marginal on `x` is uniform"; the conditional law of `y` given `x` is arbitrary. `errD` is a
finite sum, so there is no measure and no junk integral. `optD` is the page's minimum, written as an infimum over all
parameters `(w, θ)` of the published `ltf` (constant halfspaces included, as for the published `opt`); only finitely many
functions on the cube arise, so the infimum is attained.
-/

namespace Supplement

/-- A labeled example `(x, y) ∈ {±1}ⁿ × {±1}`. -/
abbrev Example (n : ℕ) := Cube n × ℤˣ

/-- `D` is a probability distribution on `{±1}ⁿ × {±1}` whose marginal on `{±1}ⁿ` is uniform (p.2). -/
def IsUniformMarginal {n : ℕ} (D : Example n → ℝ) : Prop :=
  (∀ z, 0 ≤ D z) ∧ ∀ x : Cube n, D (x, 1) + D (x, -1) = ((2 : ℝ) ^ n)⁻¹

open Classical in
/-- `err_D(h) = Pr_{(x,y)∼D}[h(x) ≠ y]` (p.2). -/
noncomputable def errD {n : ℕ} (D : Example n → ℝ) (h : Cube n → ℝ) : ℝ :=
  ∑ z : Example n, D z * if h z.1 ≠ ((z.2 : ℤ) : ℝ) then 1 else 0

/-- `OPT_D = min_{h ∈ H_n} err_D(h)` (p.2), the infimum over all parameters `(w, θ)`. -/
noncomputable def optD {n : ℕ} (D : Example n → ℝ) : ℝ :=
  ⨅ p : (Fin n → ℝ) × ℝ, errD D (ltf p.1 p.2)

end Supplement

end ProperHalfspace


