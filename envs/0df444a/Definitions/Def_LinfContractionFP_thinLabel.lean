-- Prove2me | Definitions.Def_LinfContractionFP_thinLabel
-- name    : LinfContractionFP_thinLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:17:23.571306+00:00
-- url     : https://prove2.me/theorems/cf155a94-e891-4b0f-90bd-b7ce75a96603
-- title:
--   ThinLabel (Algorithm 2)
-- statement:
--   ThinLabel$(L,U;\eta)$ computes the candidate point $x$ of Part I and $h=f(x)$ ($f$ the clipped extension). If $\|x-h\|_\infty\le\eta$ it returns the $\eta$-approximate fixed point $\mathrm{clip}_{[0,1]^d}(x)$. Otherwise it returns the face labels
--   $$\ell_{i,-}=\mathsf{hi}\ \text{if } h_i-L_i\ge t,\ \text{else } \mathsf{lo};\qquad \ell_{i,+}=\mathsf{hi}\ \text{if } U_i-h_i\ge t,\ \text{else } \mathsf{lo},$$
--   with $t$ the median half side length. Lemma 2 shows these labels are $\gamma\eta/8$-accurate.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 2, p.9

import Mathlib
import Definitions.Def_LinfContractionFP_thinPoint
import Definitions.Def_LinfContractionFP_Lbl

open scoped Classical

namespace LinfContractionFP

/-- ThinLabel(L, U; η) (Algorithm 2): either an `η`-approximate fixed point (`Sum.inl p`) or a
labeling of the `2d` faces of `[L, U]` (`Sum.inr ℓ`).

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Algorithm 2, p.9
(lines 1–8: `thinPoint`):
```
// Part II: Inspect x
9  h ← f(x);
10 if ‖x − h‖∞ ≤ η then
11   return η-approximate fixed-point clip[0,1]^d(x);
12 else
13   foreach i = 1, ..., d do
14     ℓ_{i,−} ← hi if h_i − L_i ≥ t, else lo;
15     ℓ_{i,+} ← hi if U_i − h_i ≥ t, else lo;
16   return labels (ℓ−, ℓ+);
```

**Formalization Note.** `f` on line 9 is the clipped extension `clipExt f` (Section 3; `x` may
lie outside the cube). Faces are `ι × Bool` (`false` = `−`, `true` = `+`). `t` is the lower
median of the half side lengths, as in `thinPoint`. -/
noncomputable def thinLabel {ι : Type} [Fintype ι] (γ : ℝ) (f : (ι → ℝ) → (ι → ℝ))
    (solveSub : (S : Finset ι) → ((↥S → ℝ) → (↥S → ℝ)) → ℝ → (↥S → ℝ))
    (L U : ι → ℝ) (η : ℝ) : (ι → ℝ) ⊕ (ι × Bool → Lbl) :=
  let x := thinPoint γ f solveSub L U η
  let t := lowerMedian fun i => (U i - L i) / 2
  let h := clipExt f x
  if ‖x - h‖ ≤ η then Sum.inl (clipCube x)
  else Sum.inr fun j =>
    match j with
    | (i, false) => if h i - L i ≥ t then Lbl.hi else Lbl.lo
    | (i, true) => if U i - h i ≥ t then Lbl.hi else Lbl.lo

end LinfContractionFP


