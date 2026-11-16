-- Prove2me | Definitions.Def_PolyTimeMBLG_Monotone_Supplement_OneWay
-- name    : PolyTimeMBLG_Monotone_Supplement_OneWay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:33:17.017282+00:00
-- url     : https://prove2.me/theorems/f6be4e6d-238d-4b68-aa08-738fd8df3dc6
-- title:
--   Definition 21 — one-way functions
-- statement:
--   A function $f:\{0,1\}^*\to\{0,1\}^*$ computable in polynomial time is **one-way** if there is no polynomial-time randomized algorithm $A$ such that, for infinitely many $n$, with probability at least $1/\mathrm{poly}(n)$, given $1^n$ and $f(x)$ for a uniformly random $x\in\{0,1\}^n$, $A$ returns some $\hat x\in\{0,1\}^n$ with $f(\hat x)=f(x)$.
--
--   Precisely: $f$ is computed by a Turing machine in time polynomial in the input length, and there are no polynomial-time machine $A$ and polynomials $c,q$ such that the set of $n$ with
--   $$q(n)\cdot\Pr_{x\in_R\{0,1\}^n,\ r\in_R\{0,1\}^{c(n)}}\Bigl[\,A(1^n,f(x);r)\in\{0,1\}^n\ \text{and}\ f\bigl(A(1^n,f(x);r)\bigr)=f(x)\Bigr]\ \ge\ 1$$
--   is infinite. The inverter may return any preimage of length $n$, not necessarily $x$.
--
--   "One-way functions exist" means that some $f$ is one-way; it is the hypothesis of Theorem 3 and the conclusion negated by Lemma 15.
--
--   **Formalization Note** Both $f$ and the inverter are Mathlib `Turing.TM2ComputableInPolyTime` machines; $f$ works over the alphabet `Bool`. A randomized algorithm is a deterministic machine reading $1^n$, a separator, $f(x)$, a separator and the coin string $r$ (alphabet `Option Bool`), with $c(n)$ coins for a polynomial $c$; the probability is the exact fraction of pairs $(x,r)$. Since $|f(x)|$ is polynomial in $n$, polynomially many coins in $n$ and time polynomial in the input length are the usual notions. The bound "probability $1/\mathrm{poly}(n)$" is $1\le q(n)\Pr[\cdot]$ with $q$ a polynomial with natural coefficients.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), Definition 21, p. 13; used in Theorem 3, p. 4 and Lemma 15, p. 9. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib

namespace PolyTimeMBLG.Monotone.Supplement

/-- `f : {0,1}* → {0,1}*` is polynomial-time computable: one finite TM2 machine outputs `f(w)` on
input `w` within `P(|w|)` steps, for one polynomial `P`. -/
def IsPolyTimeComputable (f : List Bool → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id f)

/-- The input of a randomized inverter over the alphabet `Option Bool`: `1ⁿ`, a separator `none`,
the bits of `y = f(x)`, a separator `none`, and the coin bits `r`. -/
def inverterInput (n : ℕ) (y r : List Bool) : List (Option Bool) :=
  List.replicate n (some true) ++ none :: (y.map some ++ none :: r.map some)

/-- The number of pairs `(x, r) ∈ {0,1}ⁿ × {0,1}^c` on which the deterministic machine `A`, run on
`(1ⁿ, f(x))` with coins `r`, returns some `x̂ ∈ {0,1}ⁿ` with `f(x̂) = f(x)`. -/
def invertCount (f : List Bool → List Bool) (A : List (Option Bool) → List Bool)
    (c n : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin n → Bool) × (Fin c → Bool))).filter (fun p =>
    (A (inverterInput n (f (List.ofFn p.1)) (List.ofFn p.2))).length = n ∧
      f (A (inverterInput n (f (List.ofFn p.1)) (List.ofFn p.2))) = f (List.ofFn p.1))).card

/-- The success probability of the randomized inverter `A` with `c` coins at length `n`:
`Pr_{x ∈R {0,1}ⁿ, r ∈R {0,1}^c}[A(1ⁿ, f(x); r) ∈ {0,1}ⁿ ∩ f⁻¹(f(x))]`. -/
noncomputable def invertProb (f : List Bool → List Bool) (A : List (Option Bool) → List Bool)
    (c n : ℕ) : ℝ :=
  (invertCount f A c n : ℝ) / (2 : ℝ) ^ (n + c)

/-- Definition 21, p. 13: a polynomial-time computable `f : {0,1}* → {0,1}*` is **one-way** if no
polynomial-time randomized algorithm (a polynomial-time machine `A` with `c(n)` uniform coin bits,
`c` a polynomial) satisfies, for infinitely many `n`, with probability at least `1/q(n)` for a
polynomial `q`: given `1ⁿ` and `f(x)` with `x ∈R {0,1}ⁿ`, it returns some `x̂ ∈ {0,1}ⁿ` with
`f(x) = f(x̂)`. -/
def IsOneWay (f : List Bool → List Bool) : Prop :=
  IsPolyTimeComputable f ∧
    ¬ ∃ A : List (Option Bool) → List Bool,
        Nonempty (Turing.TM2ComputableInPolyTime (id : List (Option Bool) → List (Option Bool))
          id A) ∧
        ∃ c q : Polynomial ℕ,
          Set.Infinite {n : ℕ | 1 ≤ ((q.eval n : ℕ) : ℝ) * invertProb f A (c.eval n) n}

end PolyTimeMBLG.Monotone.Supplement


