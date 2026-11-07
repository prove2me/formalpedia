-- Prove2me | Definitions.Def_LowErrExt_H2
-- name    : LowErrExt_H2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:28.498204+00:00
-- url     : https://prove2.me/theorems/430da05a-f2bf-4066-b95e-a931532ffff4
-- title:
--   Collision entropy $H_2$ and max-entropy $H_0[S]=\log|S|$
-- statement:
--   For a source $\mathbf X$ the **collision entropy** is
--   $$H_2[\mathbf X]=\log\frac{1}{\sum_{x}\Pr[\mathbf X=x]^2},$$
--   and for a finite nonempty set $S$ the **max-entropy** is $H_0[S]=\log|S|$. All logarithms are base $2$. The min-entropy $H_\infty[\mathbf X]=\log(1/\max_x\Pr[\mathbf X=x])$ is the published `FuzzyExtractors.Hamming.minEntropy`.
--
--   **Formalization Note** $H_0$ of the empty set evaluates to $\log 0=0$ in Lean; it is only applied to nonempty sets.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 2.3, p.11

import Mathlib

namespace LowErrExt

/-- **Collision entropy `H₂`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 2.3, p.11: "H2[X] := log(1/∑_{x∈supp(X)} Pr[X=x]²) is called the collision entropy
(or Rényi entropy) of X." All logs are base 2 (p.10).

**Formalization Note.** The sum over the support equals the sum over the whole type (terms off
the support vanish). Every source in this mission lives on a finite type, where the `tsum` is a
finite sum; the min-entropy `H∞` is the published `FuzzyExtractors.Hamming.minEntropy`. -/
noncomputable def H2 {α : Type*} (X : PMF α) : ℝ :=
  -Real.logb 2 (∑' a, (X a).toReal ^ 2)

/-- **Max-entropy of a finite set.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), p.11:
"for a finite nonempty set S, we define H0[S] := H0[U_S] = log |S|."

**Formalization Note.** `Nat.card` of a set; on the empty set the value is `log 0 = 0` in Lean,
a junk value. Every use in this mission applies `H0` to a nonempty set (a coset, the image of a
coset, or a nonempty alphabet). -/
noncomputable def H0 {α : Type*} (S : Set α) : ℝ :=
  Real.logb 2 (Nat.card S)

end LowErrExt


