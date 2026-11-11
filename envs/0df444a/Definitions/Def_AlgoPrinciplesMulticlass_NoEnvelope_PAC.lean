-- Prove2me | Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC
-- name    : AlgoPrinciplesMulticlass_NoEnvelope_PAC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:27:35.979784+00:00
-- url     : https://prove2.me/theorems/fc084f02-35cf-47fa-ac03-387243850f7d
-- title:
--   Learners, population loss, and realizable multiclass (proper) PAC learnability (§2)
-- statement:
--   Let $X$ be an arbitrary domain and $Y$ an arbitrary label set, possibly infinite. A **hypothesis class** is a set $\mathcal H\subseteq Y^X$. A **sample** of size $m$ is a sequence $S=((x_1,y_1),\dots,(x_m,y_m))$ of labeled examples in $X\times Y$, and a **learner** is a function $A:(X\times Y)^{<\omega}\to Y^X$, defined on every finite sample (of every size, realizable or not, including the empty one). Given a target $h^\star:X\to Y$ and points $x_1,\dots,x_m$, the sample **labeled by** $h^\star$ is $((x_1,h^\star(x_1)),\dots,(x_m,h^\star(x_m)))$.
--
--   For a probability distribution $D$ on $X$ (every subset of $X$ measurable), the **population loss** of $h$ against $h^\star$ is
--   $$L_D(h,h^\star)=\Pr_{x\sim D}[h(x)\ne h^\star(x)].$$
--   The **failure probability** of $A$ at sample size $m$ and accuracy $\varepsilon$ is $\Pr_{S\sim D^m}[L_D(A(S),h^\star)>\varepsilon]$, where the $m$ points are drawn i.i.d. from $D$ and labeled by $h^\star$.
--
--   $A$ **PAC learns** $\mathcal H$ if for every $\varepsilon,\delta\in(0,1)$ there is $n_A(\varepsilon,\delta)\in\mathbb N$ such that for all $m\ge n_A(\varepsilon,\delta)$, every $h^\star\in\mathcal H$ and every probability distribution $D$ on $X$,
--   $$\Pr_{S\sim D^m}\big[L_D(A(S),h^\star)>\varepsilon\big]\le\delta .$$
--   $A$ is **proper** for $\mathcal H$ if $A(S)\in\mathcal H$ for every finite sample $S$. The class $\mathcal H$ is **learnable** if some learner PAC learns it, and **properly learnable** if some proper learner for $\mathcal H$ PAC learns it. The **image** of a learner is $\operatorname{im}(A)=\{A(S): S\in(X\times Y)^{<\omega}\}$.
--
--   These are the notions of §2 used by every statement of the mission; the sample size $n_A(\varepsilon,\delta)$ is one function, uniform over all targets in the class and all distributions.
--
--   **Formalization Note.** `Learner X Y = (m : ℕ) → (Fin m → X × Y) → X → Y`. Distributions are measures `D : @Measure X ⊤` with `IsProbabilityMeasure` for the σ-algebra `⊤` (every subset measurable), fixed inside the definitions; the prover never chooses the σ-algebra. `popLoss D h h⋆ = D {x | h x ≠ h⋆ x}` in `ℝ≥0∞`; `failProb A h⋆ D m ε` is the `Measure.pi` product measure $D^m$ on `Fin m → X` of the set of point tuples `xs` with `ENNReal.ofReal ε < popLoss D (A m (labelSample h⋆ xs)) h⋆`, and PAC learning asks `failProb … ≤ ENNReal.ofReal δ`. For countable $X$ every subset of `Fin m → X` is product-measurable; for an uncountable $X$ a non-measurable bad set is measured by its outer measure.
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 13, §2 Preliminaries; p. 6 and p. 18 (im(A))

import Mathlib

open MeasureTheory

namespace AlgoPrinciplesMulticlass.NoEnvelope

/-!
# Realizable multiclass PAC learning (§2, p. 13)

Asilis, Dughmi, Sharan, Sun, Teng, Wang, *Algorithmic Principles For Multiclass Learning Are
Hard To Come By*, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 13, §2.

`X` is an arbitrary domain and `Y` an arbitrary (possibly infinite) label set; a hypothesis class
is a set `H : Set (X → Y)`. Distributions on `X` are probability measures for the σ-algebra `⊤`
(every subset of `X` is measurable), fixed here once and for all, so "every marginal `D`" ranges
over every probability measure on `X`. A sample of size `m` is a function `Fin m → X × Y`; a
learner is defined on every finite sample, of every size, realizable or not.
-/

/-- A learner `(X × Y)^{<ω} → Y^X`: for every sample size `m` and every sample
`S = ((x₁, y₁), …, (x_m, y_m))` (encoded as `Fin m → X × Y`) a hypothesis `X → Y`. -/
abbrev Learner (X Y : Type*) := (m : ℕ) → (Fin m → X × Y) → X → Y

/-- The sample `((x₁, h⋆ x₁), …, (x_m, h⋆ x_m))` obtained by labeling the points `xs` with the
target `h⋆`. -/
def labelSample {X Y : Type*} {m : ℕ} (hstar : X → Y) (xs : Fin m → X) : Fin m → X × Y :=
  fun i => (xs i, hstar (xs i))

/-- Population loss `L_D(h, h⋆) = P_{x∼D}[h(x) ≠ h⋆(x)]`, for a measure `D` on `X` with the
σ-algebra `⊤` (valued in `ℝ≥0∞`; it is a number in `[0, 1]` when `D` is a probability measure). -/
noncomputable def popLoss {X Y : Type*} (D : @Measure X ⊤) (h hstar : X → Y) : ENNReal :=
  D {x | h x ≠ hstar x}

/-- The failure probability `P_{S∼D^m}[L_D(A(S), h⋆) > ε]`, where `S` is `m` i.i.d. draws from
`D` labeled by `h⋆` (the product measure `D^m` on `Fin m → X`). -/
noncomputable def failProb {X Y : Type*} (A : Learner X Y) (hstar : X → Y) (D : @Measure X ⊤)
    (m : ℕ) (ε : ℝ) : ENNReal :=
  letI : MeasurableSpace X := ⊤
  Measure.pi (fun _ : Fin m => D)
    {xs : Fin m → X | ENNReal.ofReal ε < popLoss D (A m (labelSample hstar xs)) hstar}

/-- `A` PAC learns `H` (§2, p. 13): for every `ε, δ ∈ (0, 1)` there is `n_A(ε, δ)` such that for
all `m ≥ n_A(ε, δ)`, every target `h⋆ ∈ H` and every probability measure `D` on `X`,
`P_{S∼D^m}[L_D(A(S), h⋆) > ε] ≤ δ`, the sample being labeled by `h⋆`. -/
def PACLearns {X Y : Type*} (A : Learner X Y) (H : Set (X → Y)) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∀ hstar ∈ H, ∀ D : @Measure X ⊤, @IsProbabilityMeasure X ⊤ D →
      failProb A hstar D m ε ≤ ENNReal.ofReal δ

/-- `A` is proper for `H`: its output lies in `H` on every sample. -/
def IsProper {X Y : Type*} (A : Learner X Y) (H : Set (X → Y)) : Prop :=
  ∀ (m : ℕ) (S : Fin m → X × Y), A m S ∈ H

/-- `H` is (PAC) learnable: some learner PAC learns `H`. -/
def PACLearnable {X Y : Type*} (H : Set (X → Y)) : Prop :=
  ∃ A : Learner X Y, PACLearns A H

/-- `H` is properly (PAC) learnable: some proper learner for `H` PAC learns `H`. -/
def ProperlyPACLearnable {X Y : Type*} (H : Set (X → Y)) : Prop :=
  ∃ A : Learner X Y, IsProper A H ∧ PACLearns A H

/-- The image `im(A)` of a learner: every hypothesis it outputs on some finite sample. -/
def Learner.image {X Y : Type*} (A : Learner X Y) : Set (X → Y) :=
  {f | ∃ (m : ℕ) (S : Fin m → X × Y), A m S = f}

end AlgoPrinciplesMulticlass.NoEnvelope


