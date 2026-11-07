-- Prove2me | Definitions.Def_QuasiStrictNE_OracleComputesLocalFormula
-- name    : QuasiStrictNE_OracleComputesLocalFormula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:14.687888+00:00
-- url     : https://prove2.me/theorems/ba758e35-534b-4de0-a45d-b1e9d732e5d5
-- title:
--   Polynomial-time linear-comparison oracle algorithm for the local affine formula
-- statement:
--   For a family of maps $f_i:\mathbb R^{d_1(i)}\to\mathbb R^{d_2(i)}$ with domains $D_i$, indexed by instances $i$ with input codes, this predicate states: there is **one** algorithm, computable in polynomial time, and a polynomial $q$ such that for every instance $i$ and every point $x$, after at most $q(|i|)$ rounds of linear-comparison queries about $x$ the algorithm outputs
--
--   1. **No** if $x\notin D_i$;
--   2. otherwise a rational matrix $C$ and a rational vector $c$ with $f_i(x)=Cx+c$.
--
--   This is condition 3 of Definition 6 ("If $x\notin D_I$, the algorithm outputs No; otherwise, it outputs a rational matrix $C$ and a rational vector $c$ specifying the local affine formula applicable at $x$, so that $F_I(x)=Cx+c$").
--
--   **Formalization Note** Each step of the algorithm is polynomial-time on Cook's Turing machines in the length of (instance, answers so far), and the number of rounds is polynomial in the instance length, so the whole run is polynomial-time.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 6.3, p.9

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_PacingComplexity_encRatRect
import Definitions.Def_QuasiStrictNE_oracleBits

namespace QuasiStrictNE

/-- **A polynomial-time linear-comparison oracle algorithm for the local affine formula** (Hansen &
Nie, *On Existence and Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350,
Definition 6.3, p.9: "There is a polynomial-time algorithm that interacts with a linear-comparison
oracle for the point x. … If x ∉ DI, the algorithm outputs No; otherwise, it outputs a rational
matrix C and a rational vector c specifying the local affine formula applicable at x, so that
FI(x) = Cx + c").

The instances are indexed by `i : ι`, with input code `code i`, a domain `D i ⊆ ℝ^{d₁ i}` and a map
`f i : ℝ^{d₁ i} → ℝ^{d₂ i}`. The predicate holds iff there are one oracle algorithm `step` for all
instances, computable in polynomial time, and a polynomial `q` such that for every instance `i` and
every point `x`, after `q(|code i|)` rounds (`oracleBits`) the algorithm has stopped and its output is

1. `No` (the string `[false, false]`) if `x ∉ D i`;
2. if `x ∈ D i`, the tagged code `false :: true :: (C, c)` of a rational `d₂ × d₁` matrix `C` and a
   rational vector `c` with `f i x = C x + c`.

**Formalization Note** "Polynomial-time" is: `step` is `CookPvsNP.PolyTimeComputable` on the pair
code `code i # answers`, and the number of rounds is at most `q(|code i|)`, so every step, and the
whole run, takes time polynomial in `|code i|`. The matrix and vector are written with the public
`encRatRect` and `encRatVec`. -/
def OracleComputesLocalFormula {ι : Type} (code : ι → List Bool) (d₁ d₂ : ι → ℕ)
    (D : ∀ i, Set (Fin (d₁ i) → ℝ)) (f : ∀ i, (Fin (d₁ i) → ℝ) → (Fin (d₂ i) → ℝ)) : Prop :=
  ∃ step : List (Option (Bool ⊕ Bool)) → List Bool, CookPvsNP.PolyTimeComputable step ∧
    ∃ q : Polynomial ℕ, ∀ (i : ι) (x : Fin (d₁ i) → ℝ),
      (x ∉ D i →
        step ((code i).map (some ∘ Sum.inl) ++ none ::
          (oracleBits step (code i) x (q.eval (code i).length)).map (some ∘ Sum.inr)) =
          [false, false]) ∧
      (x ∈ D i → ∃ (C : Fin (d₂ i) → Fin (d₁ i) → ℚ) (c : Fin (d₂ i) → ℚ),
        step ((code i).map (some ∘ Sum.inl) ++ none ::
          (oracleBits step (code i) x (q.eval (code i).length)).map (some ∘ Sum.inr)) =
          false :: true :: (PacingComplexity.encRatRect (d₂ i) (d₁ i) C ++
            CardinalMatching.encRatVec (d₂ i) c) ∧
        f i x = fun a => ∑ b, (C a b : ℝ) * x b + (c a : ℝ))

end QuasiStrictNE


