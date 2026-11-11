-- Prove2me | Definitions.Def_OneTrap_Core_Model
-- name    : OneTrap_Core_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:44:20.195777+00:00
-- url     : https://prove2.me/theorems/434ea5d2-e697-4335-bffd-37884193e3e6
-- title:
--   Boxes, technologies, contracts $W$ and $W_{\mathrm{eff}}$, traps $\mathrm{trap}(y,t)$, the residual floor $D_w$ and extended-real expectations
-- statement:
--   A **box** (action) $i$ has an output $Y_i$ whose law $F_i$ is a probability measure on $[0,\infty)$ with $\mathbb E[Y_i]<\infty$ (Assumption 2.1; no finite support, boundedness or density is assumed) and a deterministic **cost** $c_i\ge 0$ (zero allowed). A **technology** is a finite family of boxes; its outputs are independent. A **contract** is a Borel function $w$ with $w(y)\ge 0$ for $y\ge 0$; the class
--   $$W_{\mathrm{eff}}=\{w\in W:\ w(0)=0,\ \exists L<\infty\ \forall y\ge 0,\ w(y)\le L(1+y)\}.$$
--   For $y\ge 0$ and $t\le w(y)$, $\mathrm{trap}(y,t)$ is a fresh box that returns $y$ with probability one and costs $w(y)-t$ (Definition 3.1, which also requires $t\ge 0$). The **residual floor** is $D_w(t)=\inf\{y-w(y): y\ge 0,\ w(y)\ge t\}$ with $\inf\emptyset=+\infty$ (eq. (19)); it may be $-\infty$. The **extended-real expectation** of an $[-\infty,\infty]$-valued $f$ is $\mathbb E[f^+]-\mathbb E[f^-]$, both parts in $[0,\infty]$.
--
--   **Formalization Note** `OutputLaw` is a `ProbabilityMeasure ℝ` with `0 ≤ y` almost surely and `Integrable (fun y => y)`; `Box` adds `cost` with `0 ≤ cost`. `Box.ofCost F c` has cost `max c 0` (the box with cost `c` on the nonnegative orthant; used only for cost vectors in Lemma B.11). `IsContract w` is `Measurable w ∧ ∀ y ≥ 0, 0 ≤ w y` on `w : ℝ → ℝ` (values on negative arguments never matter); `IsEffContract` adds `w 0 = 0` and one `L` with `w y ≤ L * (1 + y)` for all `y ≥ 0`. `trap w y t hy ht` needs `hy : 0 ≤ y` and `ht : t ≤ w y`; the condition `0 ≤ t` of Definition 3.1 is imposed where traps are quantified. `residualFloor` is an `EReal` `sInf` (`⊤` on the empty set, `⊥` when unbounded below). `eexp μ f` subtracts the lower integrals of `f.toENNReal` and `(-f).toENNReal` in `EReal`; if both were infinite the value would be `⊥`, which the model's payoffs never meet (Appendix A).
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), §2.1–§2.2, pp. 4–5 (PDF 5–6), Assumption 2.1; Definition 3.1, p. 6 (PDF 7); eq. (19), p. 27 (PDF 28); Appendix A, p. 19 (PDF 20)

import Mathlib

/-!
# Boxes, technologies, contracts and traps

Feldman, Fu, Peng, Tang, *One Trap Is Enough: The Structure and Complexity of Robust Contracts
for Sequential Search* (2026), held STOC 2027 submission, §2.1–§2.2 (pp. 4–5), Definition 3.1
(p. 6), eq. (19) (p. 27).

A box (action) has an output law on `[0, ∞)` that is a probability measure with finite mean
(Assumption 2.1: no finite support, boundedness or density is assumed) and a deterministic
cost `c ≥ 0` (zero allowed). A technology is a finite family of boxes `T : ι → Box` indexed by a
finite type; the outputs are independent (the joint law is the product measure, see
`Def_OneTrap_Core_Search`). A contract is a Borel function `w` with `w ≥ 0` on `[0, ∞)`.
-/

noncomputable section

open MeasureTheory

namespace OneTrap.Core

/-- An admissible output law (Assumption 2.1): a probability measure on `ℝ`, concentrated on
`[0, ∞)`, with finite mean. -/
structure OutputLaw where
  /-- The law `F_i` of the output `Y_i`. -/
  law : ProbabilityMeasure ℝ
  /-- Outputs are nonnegative almost surely. -/
  nonneg : ∀ᵐ y ∂(law : Measure ℝ), 0 ≤ y
  /-- Outputs are integrable. -/
  integrable : Integrable (fun y : ℝ => y) (law : Measure ℝ)

/-- A box (action): an admissible output law and a deterministic cost `c ≥ 0` (zero allowed). -/
structure Box where
  /-- The output law. -/
  out : OutputLaw
  /-- The opening cost `c_i`. -/
  cost : ℝ
  /-- Costs are nonnegative; `c_i = 0` is allowed. -/
  cost_nonneg : 0 ≤ cost

/-- The box with output law `F` and cost `max c 0`; on the nonnegative cost orthant this is
the box with cost `c` (used for cost vectors, Lemma B.11). -/
def Box.ofCost (F : OutputLaw) (c : ℝ) : Box :=
  ⟨F, max c 0, le_max_right _ _⟩

/-- A contract `w ∈ W` (§2.1, p. 5): a Borel function, nonnegative on outputs `y ≥ 0`.
Values at negative arguments are never used (outputs are nonnegative almost surely). -/
def IsContract (w : ℝ → ℝ) : Prop :=
  Measurable w ∧ ∀ y : ℝ, 0 ≤ y → 0 ≤ w y

/-- The effective contract class `W_eff` (§2.2, p. 5): contracts with `w(0) = 0` and one
constant `L < ∞` with `w(y) ≤ L (1 + y)` for every `y ≥ 0`. -/
def IsEffContract (w : ℝ → ℝ) : Prop :=
  IsContract w ∧ w 0 = 0 ∧ ∃ L : ℝ, ∀ y : ℝ, 0 ≤ y → w y ≤ L * (1 + y)

/-- The deterministic output law `δ_y` for an output `y ≥ 0`. -/
def diracLaw (y : ℝ) (hy : 0 ≤ y) : OutputLaw where
  law := ⟨Measure.dirac y, inferInstance⟩
  nonneg := by
    show ∀ᵐ z ∂(Measure.dirac y), 0 ≤ z
    rw [ae_dirac_eq]
    exact hy
  integrable := by
    show Integrable (fun z : ℝ => z) (Measure.dirac y)
    exact integrable_dirac (by simp)

/-- `trap(y, t)` (Definition 3.1, p. 6; also `trap_w(y, t)`, p. 27): a fresh box that returns
the output `y ≥ 0` with probability one and costs `w(y) − t ≥ 0`. Definition 3.1 also
requires `0 ≤ t`; the statements that use traps quantify over `0 ≤ t ≤ w(y)` themselves. -/
def trap (w : ℝ → ℝ) (y t : ℝ) (hy : 0 ≤ y) (ht : t ≤ w y) : Box where
  out := diracLaw y hy
  cost := w y - t
  cost_nonneg := sub_nonneg.mpr ht

/-- The residual floor `D_w(t) = inf {y − w(y) : y ≥ 0, w(y) ≥ t}` (eq. (19), p. 27; p. 6),
an extended real with `inf ∅ = +∞`; it may be `−∞`. -/
def residualFloor (w : ℝ → ℝ) (t : ℝ) : EReal :=
  sInf {r : EReal | ∃ y : ℝ, 0 ≤ y ∧ t ≤ w y ∧ r = ((y - w y : ℝ) : EReal)}

/-- Extended-real expectation `E[f] = E[f⁺] − E[f⁻]`, both parts as lower Lebesgue integrals
in `[0, ∞]` (Appendix A, p. 19). It is never the Bochner integral. If both parts are infinite
the value is `⊤ - ⊤ = ⊥`; the payoffs of the model never meet that case (Appendix A). -/
def eexp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → EReal) : EReal :=
  ((∫⁻ ω, (f ω).toENNReal ∂μ : ENNReal) : EReal) - ((∫⁻ ω, (-f ω).toENNReal ∂μ : ENNReal) : EReal)

end OneTrap.Core


