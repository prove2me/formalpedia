-- Prove2me | Definitions.Def_LinfContractionFP_solveLoop
-- name    : LinfContractionFP_solveLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:24.344174+00:00
-- url     : https://prove2.me/theorems/9a0c508d-9cc5-4d56-b1e6-d5c60d1e1875
-- title:
--   Solve for $d\ge2$ (Algorithm 1), with Label as a parameter
-- statement:
--   Algorithm 1: start from $D=1$ and the cube $L=0$, $U=1$. While $D>\varepsilon$, call Label$(L,U;D/8,\varepsilon)$; if it returns a point $x$, return $x$; otherwise, for every coordinate $i$, set $U_i\gets U_i-D/8$ if $\ell_{i,-}=\mathsf{lo}$ and $L_i\gets L_i+D/8$ if $\ell_{i,-}=\mathsf{hi}$, and set $D\gets7D/8$. At the end return the centre $(L+U)/2$.
--
--   **Formalization Note** Label is a parameter. The loop runs its exact number of iterations, the least $j$ with $(7/8)^j\le\varepsilon$.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 1, p.6

import Mathlib
import Definitions.Def_LinfContractionFP_Lbl
import Definitions.Def_LinfContractionFP_firstIndex

open scoped Classical

namespace LinfContractionFP

/-- The exact number of iterations of the loop `while D > ε` of Algorithm 1: `D = (7/8)^j` at
the start of iteration `j`, so the loop stops at the least `j` with `(7/8)^j ≤ ε`. -/
noncomputable def solveIterations (ε : ℝ) : ℕ := firstIndex fun j => (7 / 8 : ℝ) ^ j ≤ ε

/-- Algorithm 1, Solve(f, ε) for `d ≥ 2`, with the calls to Label (Algorithm 4) replaced by the
parameter `lab`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Algorithm 1, p.6:
```
1  D ← 1;
2  L_i ← 0, U_i ← 1 for every i = 1, ..., d;
3  while D > ε do
4    if Label(L, U; D/8, ε) returns an ε-near fixed point x then  // Algorithm 4
5      return x
6    else
7      receive labels ℓ_{i,−} from the call
8      foreach i = 1, ..., d do
9        if ℓ_{i,−} = lo then U_i ← U_i − D/8;
10       if ℓ_{i,−} = hi then L_i ← L_i + D/8;
11     D ← 7D/8;
12 return (L + U)/2;
```

**Formalization Note.** `lab L U τ ε` returns `Sum.inl x` (a point) or `Sum.inr ℓ` (labels of
the faces `ι × Bool`; `ℓ (i, false)` is `ℓ_{i,−}`). The loop runs `solveIterations ε` times, its
exact iteration count; the condition `D > ε` is also re-tested in every iteration. -/
noncomputable def solveLoop {ι : Type} (lab : (ι → ℝ) → (ι → ℝ) → ℝ → ℝ → (ι → ℝ) ⊕ (ι × Bool → Lbl))
    (ε : ℝ) : ι → ℝ := Id.run do
  let mut D : ℝ := 1
  let mut L : ι → ℝ := fun _ => 0
  let mut U : ι → ℝ := fun _ => 1
  for _ in List.range (solveIterations ε) do
    if ε < D then
      match lab L U (D / 8) ε with
      | Sum.inl x => return x
      | Sum.inr ℓ =>
        let L₀ := L
        let U₀ := U
        U := fun i => if ℓ (i, false) = Lbl.lo then U₀ i - D / 8 else U₀ i
        L := fun i => if ℓ (i, false) = Lbl.hi then L₀ i + D / 8 else L₀ i
        D := 7 * D / 8
  return fun i => (L i + U i) / 2

end LinfContractionFP


