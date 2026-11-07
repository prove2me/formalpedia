-- Prove2me | Definitions.Def_LowErrExt_IsBlockSpread
-- name    : LowErrExt_IsBlockSpread
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:43.547346+00:00
-- url     : https://prove2.me/theorems/dd5ff3e0-4b08-4e6a-a4c4-f66dd9aae570
-- title:
--   $(k)_\infty$-block-spreadness on $G^n$
-- statement:
--   Let $G$ be a finite abelian group. A source $\mathbf X=(\mathbf X_1,\dots,\mathbf X_n)$ on $G^n$ is **$(k)_\infty$-block-spread** if for every homomorphism $L$ out of $G$ such that $\mathbf Y=(L(\mathbf X_1),\dots,L(\mathbf X_n))$ is not constant,
--   $$H_\infty[\mathbf Y]\ge k .$$
--
--   **Formalization Note** As for spreadness, homomorphisms are represented by quotient maps $G\to G/K$ applied in every coordinate. "Not constant" means that $\mathbf Y$ takes at least two values with positive probability.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 7.8, p.53

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace LowErrExt

/-- **Block-spreadness `(k)∞`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 7.8, p.53: "A random variable X ∼ Gⁿ is called (k)α-block-spread if for any
homomorphism L out of G such that Y := (L(X1), . . . , L(Xn)) is not constant, it holds that
Hα[Y] ≥ k."

`IsBlockSpreadInf k X`: for every subgroup `K ≤ G`, if `Y = (π_K(X_1), …, π_K(X_n))` is not
almost surely constant, then `H∞[Y] ≥ k`.

**Formalization Note.** As for spreadness, a homomorphism `L` out of `G` with kernel `K` is an
injective map after `π_K`, applied coordinatewise; so `(L(X_i))_i` is constant iff `(π_K(X_i))_i`
is, with the same entropy. Only `α = ∞` occurs in the mission. "Not constant" means the support of
`Y` has at least two points. -/
def IsBlockSpreadInf {G : Type*} [AddCommGroup G] {n : ℕ} (k : ℝ) (X : PMF (Fin n → G)) : Prop :=
  ∀ K : AddSubgroup G,
    (¬ ∃ c : Fin n → G ⧸ K,
        ∀ y ∈ (X.map fun x i => (QuotientAddGroup.mk (x i) : G ⧸ K)).support, y = c) →
      k ≤ FuzzyExtractors.Hamming.minEntropy (X.map fun x i => (QuotientAddGroup.mk (x i) : G ⧸ K))

end LowErrExt


