-- Prove2me | Definitions.Def_GenCountSampleLLL_estLaw
-- name    : GenCountSampleLLL_estLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:50:39.785753+00:00
-- url     : https://prove2.me/theorems/bcf5282f-65fe-40b8-a770-7f3ae93549f7
-- title:
--   Algorithm 1, $\mathrm{EstimateMarginal}(\mathcal D,a)$, as the law of $(\hat r_{\mathcal D,a},\text{number of calls})$
-- statement:
--   Algorithm 1 draws $\sigma_b\sim\nu_{\mathrm{vbl}(b)}$ for every $b\in\mathcal D$, returns $0$ if $a$ is inactive, and otherwise, for every rooted 2-tree $\mathcal T\in\mathfrak T_{\mathcal D,a}$ all of whose constraints are active, completes $\sigma_{\mathcal T}$ with fresh samples and, if $\sigma_{\mathcal T}\in E_{\mathcal T}$, adds $(-1)^{|\mathcal T|-1}\prod_{i=1}^{\ell(\mathcal T)}\widehat R_i$, where $\widehat R_i=\mathrm{Recip}(\hat r_{\mathcal D_{\mathcal T,i},b_{\mathcal T,i}})=\sum_{k=0}^{\mathbf N}4^k\prod_{j=1}^kY_j$ with $\mathbf N\sim\mathrm{Geom}(3/4)$ and independent recursive calls $Y_j$.
--
--   `estLaw D a` is the joint law of the returned value $\hat r_{\mathcal D,a}$ (an integer) and the total number of calls of the estimator, the initial call included. It is the estimator of Proposition 3.1 and the object of Lemma 3.5.
--
--   **Formalization Note** $\mathrm{Geom}(3/4)$ has mass $(3/4)(1/4)^k$ at $k$. Every reciprocal estimate and recursive call uses fresh independent randomness; the active trees are enumerated in a fixed order, which changes neither law. The recursion is on $|\mathcal D|$, since every $\mathcal D_{\mathcal T,i}$ lies in $\mathcal D^-$.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Algorithm 1, p.12; Lemma 3.2, p.11

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

noncomputable section

open Classical

/-!
# Algorithm 1, `EstimateMarginal(D, a)`, as a law

Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671
(held file sha256 cd449f83…), Algorithm 1, p.12, and Lemma 3.2, p.11.

```
1 Independently draw σb ∼ νvbl(b) for every b ∈ D
2 A ← {b ∈ D : σb violates b}
3 if a ∉ A then return 0
4 r̂ ← 0
5 foreach rooted 2-tree T ∈ TD,a with T ⊆ A do
6   Combine the assignments σt, t ∈ T, and complete them to σT ∈ ΩUT with fresh product samples
7   if σT ∈ ET then
8     W ← 1
9     for i = 1, . . . , ℓ(T) do
10      Independently draw N ∼ Geom(3/4)
11      P ← 1; R̂i ← 1
12      for k = 1, . . . , N do
13        Y ← EstimateMarginal(DT,i, bT,i), using fresh randomness
14        P ← (4Y) · P; R̂i ← R̂i + P
15      W ← W R̂i
16    r̂ ← r̂ + (−1)^{|T|−1} W
17 return r̂
```

`estLaw D a` is the joint law of the returned value `r̂_{D,a}` (an integer: it is built from
`0`, `1`, signs and factors `4Y`) and of the total number of calls of `EstimateMarginal`,
the initial call included.

**Formalization Note.** `Geom(3/4)` has mass `(3/4)(1/4)^k` at `k` (p.11), Mathlib's
`geometricPMF` with success probability `3/4`. Line 1 and the completions of line 6 are the draws
of the list experiment `expLaw` (all drawn up front; only the ones the listing reads matter, so
the laws are those of the page). The active trees of line 5 are enumerated in the fixed order
`Finset.toList`; neither the law of the value nor that of the call count depends on the order.
Every reciprocal estimate and every recursive call uses fresh, independent randomness (monadic
`bind`). The recursion is on `|D|` (fuel `D.card`), since every `D_{T,i}` lies in `D ∖ {a}`.
-/

namespace Inst

variable (I : Inst)

/-- Lines 12–14 run `k` times: the state is `(P, R̂, calls)`; each pass draws a fresh
`(Y, c) ∼ sub`, sets `P ← 4Y·P`, `R̂ ← R̂ + P`, and adds `c` calls. -/
def recipLoop (sub : PMF (ℤ × ℕ)) : ℕ → ℤ × ℤ × ℕ → PMF (ℤ × ℤ × ℕ)
  | 0, s => PMF.pure s
  | k + 1, s => (recipLoop sub k s).bind fun s' =>
      sub.map fun y => (4 * y.1 * s'.1, s'.2.1 + 4 * y.1 * s'.1, s'.2.2 + y.2)

set_option linter.deprecated false in
/-- Lines 10–14: the reciprocal estimate `R̂ = Recip(Y) = Σ_{k=0}^{N} 4^k ∏_{j≤k} Y_j` with
`N ∼ Geom(3/4)` and `Y_j` independent draws of `sub`, together with the calls made. -/
def recipLaw (sub : PMF (ℤ × ℕ)) : PMF (ℤ × ℕ) :=
  (ProbabilityTheory.geometricPMF (p := (3 / 4 : ℝ)) (by norm_num) (by norm_num)).bind fun N =>
    (recipLoop sub N (1, 1, 0)).map fun s => (s.2.1, s.2.2)

/-- Lines 8–15: `W = ∏_i R̂_i` over the listed indices, with independent reciprocal estimates
built from `est i`, together with the calls made. -/
def prodRecips (est : ℕ → PMF (ℤ × ℕ)) : List ℕ → PMF (ℤ × ℕ)
  | [] => PMF.pure (1, 0)
  | i :: is => (recipLaw (est i)).bind fun r1 =>
      (prodRecips est is).map fun r2 => (r1.1 * r2.1, r1.2 + r2.2)

/-- Lines 5–16 over a list of active trees, given the sub-estimator `est E b` for the recursive
calls and the draws `ω` of line 1 and line 6. -/
def treeSum (est : Finset (Fin I.m) → Fin I.m → PMF (ℤ × ℕ)) (D : Finset (Fin I.m))
    (a : Fin I.m) (ω : I.ExpSpace) : List (Finset (Fin I.m)) → PMF (ℤ × ℕ)
  | [] => PMF.pure (0, 0)
  | T :: Ts =>
    if I.inET D a T (I.sigT D T ω) then
      (prodRecips (fun i => est (I.DTi D a T i) (I.bT D a T i))
          (List.range' 1 (I.ell D a T))).bind fun W =>
        (treeSum est D a ω Ts).map fun s => ((-1) ^ (T.card - 1) * W.1 + s.1, W.2 + s.2)
    else treeSum est D a ω Ts

/-- Algorithm 1 with recursion fuel `k`. -/
def estLawF : ℕ → Finset (Fin I.m) → Fin I.m → PMF (ℤ × ℕ)
  | 0, _, _ => PMF.pure (0, 1)
  | k + 1, D, a => I.expLaw.bind fun ω =>
      if a ∉ I.active D ω then PMF.pure (0, 1)
      else (I.treeSum (estLawF k) D a ω
          ((I.twoTrees D a).filter fun T => T ⊆ I.active D ω).toList).map
        fun s => (s.1, s.2 + 1)

/-- The law of `(r̂_{D,a}, number of calls)` of `EstimateMarginal(D, a)`, Algorithm 1, p.12. -/
def estLaw (D : Finset (Fin I.m)) (a : Fin I.m) : PMF (ℤ × ℕ) := I.estLawF D.card D a

end Inst

end

end GenCountSampleLLL


