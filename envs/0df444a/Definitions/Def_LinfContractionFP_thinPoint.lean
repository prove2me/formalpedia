-- Prove2me | Definitions.Def_LinfContractionFP_thinPoint
-- name    : LinfContractionFP_thinPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:07.307065+00:00
-- url     : https://prove2.me/theorems/7979749a-3dcf-4583-a69e-de2926d0c450
-- title:
--   ThinLabel, Part I: the candidate point $x$ (Algorithm 2, lines 1–8)
-- statement:
--   For a possibly degenerate box $[L,U]$ and $\eta>0$: let $w=(U-L)/2$ be the half side lengths, $t$ their median, $N=\{i:w_i<t\}$ and $W=\{i:w_i>t\}$ the narrow and wide coordinates, and $q=(L+U)/2$ the centre. Solve $y\mapsto f_N(y,q_{-N})$ and $y\mapsto f_W(q_{-W},y)$ at precision $\gamma\eta/2$, obtaining $y^{\mathrm{narr}}$ and $y^{\mathrm{wide}}$, and set
--   $$x_i=\begin{cases}\mathrm{clip}_{[U_i-t,\,L_i+t]}(y^{\mathrm{narr}}_i) & i\in N,\\ \mathrm{clip}_{[L_i+t,\,U_i-t]}(y^{\mathrm{wide}}_i) & i\in W,\\ q_i & \text{otherwise.}\end{cases}$$
--
--   **Formalization Note** The recursive Solve calls are a parameter $\mathrm{solveSub}$; the median is the lower median; $N$ and $W$ use strict inequalities, so coordinates with $w_i=t$ keep $q_i$.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 2, lines 1–8, p.9

import Mathlib
import Definitions.Def_LinfContractionFP_lowerMedian
import Definitions.Def_LinfContractionFP_restrictMap

open scoped Classical

namespace LinfContractionFP

/-- Part I of ThinLabel (Algorithm 2, lines 1–8): the candidate point `x` built from the box
`[L, U]` and the two recursive solves.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Algorithm 2, p.9:
```
1 w ← (U − L)/2;                       // Half side lengths
2 t ← median of the {w_i}_{i=1}^d;
3 N ← {i ∈ {1, ..., d} : w_i < t};      // "Narrow" dimensions
4 W ← {i ∈ {1, ..., d} : w_i > t};      // "Wide" dimensions
5 q ← (L + U)/2;                        // Center of box
6 y^narr ∈ R^N ← Solve(y ↦ f_N(y, q_{−N}), γη/2);
7 y^wide ∈ R^W ← Solve(y ↦ f_W(q_{−W}, y), γη/2);
8 Define x as  clip[U_i−t, L_i+t](y^narr_i)  for i ∈ N,
               clip[L_i+t, U_i−t](y^wide_i)  for i ∈ W,
               q_i                           otherwise;
```

**Formalization Note.** `Solve` on lines 6–7 is the parameter `solveSub` (see
`SubSolverSpec`). The median is the lower median (`lowerMedian`). `N` and `W` use strict
inequalities; coordinates with `w_i = t` are in neither and keep `q_i`. The clips are
`clipInterval` with the printed endpoints (for `i ∈ N` the interval `[U_i − t, L_i + t]` is
nonempty, for `i ∈ W` so is `[L_i + t, U_i − t]`). The box may be degenerate. -/
noncomputable def thinPoint {ι : Type} [Fintype ι] (γ : ℝ) (f : (ι → ℝ) → (ι → ℝ))
    (solveSub : (S : Finset ι) → ((↥S → ℝ) → (↥S → ℝ)) → ℝ → (↥S → ℝ))
    (L U : ι → ℝ) (η : ℝ) : ι → ℝ :=
  let w : ι → ℝ := fun i => (U i - L i) / 2
  let t := lowerMedian w
  let N := Finset.univ.filter fun i => w i < t
  let W := Finset.univ.filter fun i => w i > t
  let q : ι → ℝ := fun i => (L i + U i) / 2
  let ynarr := solveSub N (restrictMap f N q) (γ * η / 2)
  let ywide := solveSub W (restrictMap f W q) (γ * η / 2)
  fun i =>
    if h : i ∈ N then clipInterval (U i - t) (L i + t) (ynarr ⟨i, h⟩)
    else if h' : i ∈ W then clipInterval (L i + t) (U i - t) (ywide ⟨i, h'⟩)
    else q i

end LinfContractionFP


