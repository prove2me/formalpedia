-- Prove2me | Definitions.Def_LowErrExt_IsTwoSourceRankExt
-- name    : LowErrExt_IsTwoSourceRankExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:34.812243+00:00
-- url     : https://prove2.me/theorems/731f98e5-41bb-49c3-9ece-51d3fc9ab0fc
-- title:
--   Two-source rank extractors and bilinear maps
-- statement:
--   A function $E:\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2^m$ is a **$k$-two-source rank extractor** if for all nonempty $X,Y\subseteq\mathbb F_2^n$ with $H_0[X]\ge k$ and $H_0[Y]\ge k$, the set $E(X,Y)=\{E(x,y):x\in X,y\in Y\}$ has dimension $m$. $E$ is **bilinear** if it is a homomorphism in each argument when the other is fixed.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 3.21, Remark 3.22, p.26

import Mathlib
import Definitions.Def_LowErrExt_dimSet

namespace LowErrExt

/-- **Two-source rank extractor.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 3.21, p.26: "A function 2Ext : Fn2 × Fn2 → Fm2 is a k-two-source rank extractor if, for
any subsets X, Y ⊆ Fn2 with H0[X] ≥ k and H0[Y] ≥ k, it holds that 2Ext(X, Y) has dimension m",
where 2Ext(X, Y) = {2Ext(x, y) : x ∈ X, y ∈ Y} (footnote 12).

**Formalization Note.** `X, Y` are nonempty finite sets (`H0` is defined for nonempty sets). -/
def IsTwoSourceRankExt {n m : ℕ} (k : ℝ) (E : (Fin n → ZMod 2) → (Fin n → ZMod 2) → (Fin m → ZMod 2)) :
    Prop :=
  ∀ S T : Finset (Fin n → ZMod 2), S.Nonempty → T.Nonempty →
    k ≤ Real.logb 2 S.card → k ≤ Real.logb 2 T.card →
      dimSet (Set.image2 E (S : Set (Fin n → ZMod 2)) (T : Set (Fin n → ZMod 2))) = m

/-- **Bilinear function.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Remark 3.22, p.26: f is bilinear if every `f(·, y)` and every `f(x, ·)` is a homomorphism. -/
def IsBilinear {n₁ n₂ m : ℕ} (E : (Fin n₁ → ZMod 2) → (Fin n₂ → ZMod 2) → (Fin m → ZMod 2)) : Prop :=
  (∀ x x' y, E (x + x') y = E x y + E x' y) ∧ ∀ x y y', E x (y + y') = E x y + E x y'

end LowErrExt


