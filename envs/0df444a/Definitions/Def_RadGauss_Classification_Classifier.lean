-- Prove2me | Definitions.Def_RadGauss_Classification_Classifier
-- name    : RadGauss_Classification_Classifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:24:50.625708+00:00
-- url     : https://prove2.me/theorems/76f4932e-84c2-4277-8c55-285fca0d80a9
-- title:
--   Theorem 5 / Appendix B — misclassification probability P(Y ≠ f(X)), training error P̂_n(Y ≠ f(X)), and the 0–1 loss suprema
-- statement:
--   Let $\mathcal X$ be a measurable space, $P$ a probability distribution on $\mathcal X \times \{\pm 1\}$ and $F$ a set of $\{\pm1\}$-valued functions on $\mathcal X$. For $f \in F$ and a sample $S = ((X_1, Y_1), \dots, (X_n, Y_n))$:
--
--   1. the **misclassification probability** is $P(Y \ne f(X))$;
--   2. the **training error** is $\hat P_n(Y \ne f(X)) = \frac1n\,\#\{i : Y_i \ne f(X_i)\}$, where $\hat P_n$ is the empirical measure of the sample;
--   3. the real class associated with $F$ is $\{x \mapsto f(x) \in \{-1, 1\} \subseteq \mathbb R : f \in F\}$, whose Rademacher complexity appears in Theorem 5;
--   4. with the 0–1 loss $\mathcal L(Y, f(X)) = \mathbf 1(Y \ne f(X))$ and $h = \mathcal L \circ f$, the largest generalization gap on $S$ is
--   $$\sup_{h \in \mathcal L \circ F}\big(\mathbb E h - \hat{\mathbb E}_n h\big) = \sup_{f \in F}\big(P(Y \ne f(X)) - \hat P_n(Y \ne f(X))\big);$$
--   5. for a second (ghost) sample $S'$ with training error $\hat P'_n$, the double-sample supremum is $\sup_{f \in F}\big(\hat P'_n(Y \ne f(X)) - \hat P_n(Y \ne f(X))\big)$.
--
--   These are the quantities Theorem 5 and its proof in Appendix B are written in.
--
--   **Formalization Note** Labels $\{\pm1\}$ are the units $\mathbb Z^\times = \{1, -1\}$ of $\mathbb Z$, coerced to $\mathbb R$ where a real value is needed, so $Y f(X) \in \{\pm 1\}$ and $\mathbf 1(Y \ne f(X)) = (1 - Y f(X))/2$ hold. The probability is a real number ($P$ is finite). The two suprema in items 4 and 5 are real suprema over $f \in F$; every gap lies in $[-1, 1]$, so for nonempty $F$ they are genuine suprema, and for empty $F$ Lean returns $0$ (the theorems that use them either assume $F$ nonempty or are unaffected).
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 463 (PDF p. 1), notation P̂_n; p. 465 (PDF p. 3), Theorem 5; p. 480 (PDF p. 18), Appendix B

import Mathlib

open MeasureTheory

namespace RadGauss.Classification

/-- The real-valued class `{x ↦ f(x) ∈ {−1, 1} ⊆ ℝ : f ∈ F}` of a class `F` of `{±1}`-valued
functions; labels `{±1}` are encoded as the units `ℤˣ = {1, -1}` of `ℤ`, coerced to `ℝ`. -/
def realClass {X : Type*} (F : Set (X → ℤˣ)) : Set (X → ℝ) :=
  (fun f x => ((f x : ℤ) : ℝ)) '' F

/-- The **misclassification probability** `P(Y ≠ f(X))` of a `{±1}`-valued function `f` under a
probability distribution `P` on `X × {±1}` (Bartlett–Mendelson 2002, Theorem 5, p. 465). -/
noncomputable def classError {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    (f : X → ℤˣ) : ℝ :=
  P.real {z | z.2 ≠ f z.1}

/-- The **training error** `P̂_n(Y ≠ f(X)) = (1/n) #{i : Y_i ≠ f(X_i)}` of `f` on the sample
`S = ((X_1, Y_1), …, (X_n, Y_n))`, where `P̂_n` is the empirical measure of the sample
(p. 463). Sample indices are 0-based (`Fin n`). -/
noncomputable def trainError {X : Type*} {n : ℕ} (S : Fin n → X × ℤˣ) (f : X → ℤˣ) : ℝ :=
  ((Finset.univ.filter fun i => (S i).2 ≠ f (S i).1).card : ℝ) / n

/-- `sup_{h ∈ L∘F} (E h − Ê_n h)` for the 0–1 loss `L(Y, f(X)) = 1(Y ≠ f(X))`
(Appendix B, p. 480): the largest gap, over `f ∈ F`, between the misclassification
probability and the training error on the sample `S`. A real supremum; the gaps lie in
`[−1, 1]`, so it is a genuine supremum for nonempty `F` (and `0` for empty `F`). -/
noncomputable def gapSup {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    (F : Set (X → ℤˣ)) {n : ℕ} (S : Fin n → X × ℤˣ) : ℝ :=
  ⨆ f : F, (classError P f - trainError S f)

/-- The double-sample supremum `sup_{f ∈ F} (P̂'_n(Y ≠ f(X)) − P̂_n(Y ≠ f(X)))` of the
training-error differences on a ghost sample `S'` and the sample `S` (Appendix B, p. 480,
the symmetrization that follows the proof of Theorem 8, p. 468). -/
noncomputable def ghostGapSup {X : Type*} (F : Set (X → ℤˣ)) {n : ℕ}
    (S S' : Fin n → X × ℤˣ) : ℝ :=
  ⨆ f : F, (trainError S' f - trainError S f)

end RadGauss.Classification


