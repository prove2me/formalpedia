-- Prove2me | Definitions.Def_UnderstandingML_Covering
-- name    : UnderstandingML_Covering
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:47:58.279666+00:00
-- url     : https://prove2.me/theorems/60211c3a-034f-4ee3-b5ee-0992dade80b7
-- title:
--   Chapter 27: the Euclidean norm on ℝ^m, r-covers and the covering number N(r, A) (Definition 27.1)
-- statement:
--   Chapter 27 of Shalev-Shwartz and Ben-David. `eucNorm v` $= \|v\|_2 = \sqrt{\sum_i v_i^2}$ on $\mathbb{R}^m$. **Definition 27.1 (Covering).** `IsCover r A A'` says that $A \subseteq \mathbb{R}^m$ is $r$-covered by the finite set $A'$ with respect to the Euclidean metric: for all $a \in A$ there exists $a' \in A'$ with $\|a - a'\| \le r$. `coveringNumber r A` is $N(r, A)$, the cardinality of the smallest $A'$ that $r$-covers $A$, as an infimum in $\mathbb{N} \cup \{\infty\}$ ($\infty$ if no finite cover exists).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §27.1 p. 388, Definition 27.1

import Definitions.Def_UnderstandingML_Rademacher
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 27: covering numbers

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §27.1–§27.2.

**Covering (Definition 27.1, p. 388).** `A ⊆ ℝ^m` is `r`-covered by `A'`, with respect to the
Euclidean metric, if for all `a ∈ A` there is `a' ∈ A'` with `‖a − a'‖ ≤ r`; `N(r, A)` is the
cardinality of the smallest `A'` that `r`-covers `A`.

**Chaining (§27.2, p. 389).** With `c = min_ā max_{a ∈ A} ‖a − ā‖`, Dudley's chaining bounds the
Rademacher complexity by `R(A) ≤ c 2^{−M}/√m + (6c/m) ∑_{k=1}^M 2^{−k} √(log N(c 2^{−k}, A))`.

**Conventions.** Vectors are `Fin m → ℝ` with the explicit Euclidean norm `eucNorm` (Mathlib's
`‖·‖` on this type is the sup norm). A cover is a finset of arbitrary vectors of `ℝ^m`, and
`N(r, A)` is an `ℕ∞`-valued infimum, `⊤` when no finite cover exists; for bounded `A` it is
finite, and the chaining bounds read it through `ENat.toNat`. The chaining lemma is stated for
any enclosing radius `c` about any center `ā`, of which the book's minimal `c` is a special
case; `R(A)` is Chapter 26's `rademacher`.
-/

open MeasureTheory

namespace UnderstandingML

section Covering

variable {m : ℕ}

/-- The Euclidean norm `‖v‖ = √(∑ᵢ vᵢ²)` on `ℝ^m`. -/
noncomputable def eucNorm (v : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- **Definition 27.1.** `A'` is an `r`-cover of `A` with respect to the Euclidean metric: every
`a ∈ A` is within distance `r` of some `a' ∈ A'`. -/
def IsCover (r : ℝ) (A : Set (Fin m → ℝ)) (A' : Finset (Fin m → ℝ)) : Prop :=
  ∀ a ∈ A, ∃ a' ∈ A', eucNorm (a - a') ≤ r

/-- **Definition 27.1.** The **covering number** `N(r, A)`: the cardinality of the smallest finite
`r`-cover of `A` (`⊤` if there is none). -/
noncomputable def coveringNumber (r : ℝ) (A : Set (Fin m → ℝ)) : ℕ∞ :=
  ⨅ (A' : Finset (Fin m → ℝ)) (_ : IsCover r A A'), (A'.card : ℕ∞)

end Covering

end UnderstandingML


