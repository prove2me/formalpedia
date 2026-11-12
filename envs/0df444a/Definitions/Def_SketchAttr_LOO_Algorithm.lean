-- Prove2me | Definitions.Def_SketchAttr_LOO_Algorithm
-- name    : SketchAttr_LOO_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:29:16.007208+00:00
-- url     : https://prove2.me/theorems/90966379-1acb-4d3a-a7a1-deeff1c73780
-- title:
--   Algorithm 1 — LOO estimates with all allowed tie choices
-- statement:
--   For a scalar arithmetic circuit $f$, parameters $N,m,K,\delta$, and independent directions $g_1,\ldots,g_m$, Algorithm 1 forms its degree-wise observations
--   $$\overline Z^{(j)}_{i,r}=\operatorname{Re}\left(\frac{e_i^\top c_r(g_j)(g_j^\dagger e_i)^{r-1}}{(r-1)!}\right),\qquad 2\le r\le N.$$
--   It trims these to obtain $\widehat Z_{i,r}$ and trims squared coefficients with the factor $\binom{2r-2}{r-1}/(r-1)!$ to obtain $\widehat v_{i,r}$. Estimated scores are $\widehat s_i=\sum_{r=2}^N\sqrt{\widehat v_{i,r}}$. The supplied set $F$ has exactly $K$ indices and every selected score is at least every unselected score, allowing arbitrary tie breaking. If $n\le m+K$, the set restriction is unnecessary and every answer is exact. Otherwise the returned answer is
--   $$\widehat L_i=\begin{cases}f(e_i),&i\in F,\\ f(0)+\partial_i f(0)+\sum_{r=2}^N\widehat Z_{i,r},&i\notin F.\end{cases}$$
--   The function's set-domain condition is explicit in its arguments. It supplies a pure mathematical specification of the estimator, not an instruction or an assumed implementation used to prove the goal. **Formalization Note** The trimming count is $k=\lfloor\log(32nN/\delta)\rfloor$, and the goal uses the rounded parameters specified separately in Execution.
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), pp. 15–16, Algorithm 1 and preceding exact-evaluation branch; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Sampling
import Definitions.Def_SketchAttr_LOO_Trim

namespace SketchAttr.LOO

noncomputable def observation {n : ℕ} (f : Vec n → ℂ) (i : Fin n) (r : ℕ)
    (g : Vec n) : ℝ :=
  ((sketchCoeff f r g i) * (starRingEnd ℂ (g i)) ^ (r-1) /
    (Nat.factorial (r-1) : ℂ)).re

noncomputable def estimatedTerm {n m : ℕ} (f : Vec n → ℂ) (k r : ℕ)
    (g : Fin m → Vec n) (i : Fin n) : ℝ :=
  trim k fun j => observation f i r (g j)

noncomputable def estimatedVariance {n m : ℕ} (f : Vec n → ℂ) (k r : ℕ)
    (g : Fin m → Vec n) (i : Fin n) : ℝ :=
  ((Nat.choose (2*r-2) (r-1) : ℝ) / (Nat.factorial (r-1) : ℝ)) *
    trim k (fun j => ‖sketchCoeff f r (g j) i‖ ^ 2)

noncomputable def estimatedScore {n m : ℕ} (f : Vec n → ℂ) (N k : ℕ)
    (g : Fin m → Vec n) (i : Fin n) : ℝ :=
  ∑ r ∈ Finset.Icc 2 N, Real.sqrt (estimatedVariance f k r g i)

/-- All ways of breaking ties are permitted. -/
def IsSelected {n : ℕ} (K : ℕ) (s : Fin n → ℝ) (F : Finset (Fin n)) : Prop :=
  F.card = K ∧ ∀ i ∈ F, ∀ j ∉ F, s j ≤ s i

noncomputable def algorithm1 {n m : ℕ} (c : Circuit n 1) (N K : ℕ) (δ : ℝ)
    (g : Fin m → Vec n) (F : Finset (Fin n))
    (_hF : n ≤ m+K ∨ IsSelected K
      (estimatedScore (circuitFunction c) N ⌊Real.log (32*n*N/δ)⌋₊ g) F)
    (i : Fin n) : ℂ := by
  classical
  let f := circuitFunction c
  let k := ⌊Real.log (32*n*N/δ)⌋₊
  exact if n ≤ m+K ∨ i ∈ F then f (basis i) else
    f 0 + gradient f 0 i + (∑ r ∈ Finset.Icc 2 N, estimatedTerm f k r g i : ℝ)

end SketchAttr.LOO


