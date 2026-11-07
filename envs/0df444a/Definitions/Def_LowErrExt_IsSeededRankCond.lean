-- Prove2me | Definitions.Def_LowErrExt_IsSeededRankCond
-- name    : LowErrExt_IsSeededRankCond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:24.044808+00:00
-- url     : https://prove2.me/theorems/bbd325e4-bc81-411b-876f-762281a43bbf
-- title:
--   Seeded and somewhere rank condensers; linear seeded functions
-- statement:
--   Let $f:\mathbb F_2^n\times[D]\to\mathbb F_2^m$.
--
--   1. $f$ is a **$k\to_\delta k'$ seeded rank condenser** if for every set $X\subseteq\mathbb F_2^n$ with $H_0[X]\ge k$,
--   $$\Pr_{y\sim[D]}\big[f(X,y)\text{ has dimension at least }k'\big]\ge 1-\delta .$$
--   2. $f$ is a **$k\to k'$ somewhere rank condenser** if it is a $k\to_\delta k'$ seeded rank condenser for some $\delta<1$.
--   3. $f$ is **linear** if each $f(\cdot,y)$ is a homomorphism.
--
--   **Formalization Note** The probability over a uniform seed is the fraction of good seeds, $\#\{y\}/D$; sets are nonempty and finite.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definitions 3.1–3.2, Remark 3.3, p.22

import Mathlib
import Definitions.Def_LowErrExt_dimSet

namespace LowErrExt

/-- **Seeded rank condenser `k →δ k′`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 3.1, p.22: "A function sCond : Fn2 × [D] → Fm2 is called a k →δ k′ seeded rank condenser
if for any set X ⊆ Fn2 with H0[X] ≥ k, it holds that Pr_{y∼[D]}[sCond(X, y) has dimension at least
k′] ≥ 1 − δ."

`IsSeededRankCond k δ k' f`: for every nonempty finite `S ⊆ 𝔽₂ⁿ` with `log₂|S| ≥ k`, the fraction of
seeds `y ∈ [D]` for which `f(S, y)` has dimension at least `k′` is at least `1 − δ`.

**Formalization Note.** The fraction is `#{good y}/D`; at `D = 0` Lean reads it as `0`, so the
condition then forces `δ ≥ 1` whenever some set qualifies. -/
def IsSeededRankCond {n m D : ℕ} (k δ k' : ℝ) (f : (Fin n → ZMod 2) → Fin D → (Fin m → ZMod 2)) :
    Prop :=
  ∀ S : Finset (Fin n → ZMod 2), S.Nonempty → k ≤ Real.logb 2 S.card →
    1 - δ ≤ ((Finset.univ.filter fun y : Fin D =>
        k' ≤ (dimSet ((fun x => f x y) '' (S : Set (Fin n → ZMod 2))) : ℝ)).card : ℝ) / D

/-- **Somewhere rank condenser `k → k′`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 3.2, p.22: "A function swCond : Fn2 × [D] → Fm2 is called a k → k′ somewhere rank
condenser if it is a k →δ k′ seeded rank condenser for some δ < 1." -/
def IsSomewhereRankCond {n m D : ℕ} (k k' : ℝ) (f : (Fin n → ZMod 2) → Fin D → (Fin m → ZMod 2)) :
    Prop :=
  ∃ δ : ℝ, δ < 1 ∧ IsSeededRankCond k δ k' f

/-- **Linear seeded function.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Remark 3.3, p.22: "We say that a function of the form f : Fn2 × [D] → Fm2 is linear if, for every
y ∈ [D], the function fy : Fn2 → Fm2 defined as fy(x) := f(x, y) is a homomorphism." -/
def IsLinearSeeded {n m D : ℕ} (f : (Fin n → ZMod 2) → Fin D → (Fin m → ZMod 2)) : Prop :=
  ∀ y x x', f (x + x') y = f x y + f x' y

end LowErrExt


