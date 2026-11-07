-- Prove2me | Definitions.Def_AlgoPFR_Families
-- name    : AlgoPFR_Families
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:31.929985+00:00
-- url     : https://prove2.me/theorems/f732098d-baed-4253-8078-f1a78cf95e26
-- title:
--   The five GGMT operations and the potential $\Phi$
-- statement:
--   For laws $X,Y$ on $\mathbb F_2^n$, let $X_0,X_1$ and $Y_0,Y_1$ be independent copies, all four mutually independent. The five operations produce, from a label drawn from a natural law, a new pair $(X',Y')$.
--
--   1. **Self-sum:** $(X_0+X_1,\;Y_0+Y_1)$.
--   2. **Cross-sum:** $(X_0+Y_0,\;X_1+Y_1)$.
--   3. **Self-fiber:** with $x\sim X_0+X_1$, $y\sim Y_0+Y_1$ independent: $((X_0\mid X_0+X_1=x),\;(Y_0\mid Y_0+Y_1=y))$.
--   4. **Cross-fiber:** with $z_0\sim X_0+Y_0$, $z_1\sim X_1+Y_1$ independent: $((X_0\mid X_0+Y_0=z_0),\;(Y_1\mid Y_1+X_1=z_1))$.
--   5. **Endgame:** with $Z=X_1+Y_0$, $W=X_0+X_1+Y_0+Y_1$ and $(z,w)\sim(Z,W)$: both coordinates are $U_{z,w}=(X_1+Y_1\mid Z=z,W=w)$.
--
--   The **potential** is
--   $$\Phi_{X,Y}(X',Y')=d[X';Y']+\eta\bigl(d[X;X']+d[Y;Y']\bigr).$$
--   A number $\eta$ is a **decrement constant** when for all $n$ and all $X,Y$ at least one family satisfies $\mathbb E[d[X';Y']+\eta\,d[X;X']+\eta\,d[Y;Y']]\le(1-\eta)\,d[X;Y]$.
--
--   These raw laws are defined by literal conditioning, with no reference to access procedures.
--
--   **Formalization Note** The two sum families have a trivial label. Labels are pairs of vectors. Conditioning happens only at labels of positive probability, since expectations weight each label by its probability.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), §4.1, p.19; Theorem 4.3, p.19; potential, p.29

import Mathlib
import Definitions.Def_AlgoPFR_condLaw

set_option autoImplicit false

open scoped ENNReal

namespace AlgoPFR

noncomputable section

variable {n : ℕ}

/-- The five GGMT operations of §4.1, p.19 of arXiv:2609.20771 (sha256 60e45066…). -/
inductive Family
  | selfSum
  | crossSum
  | selfFiber
  | crossFiber
  | endgame
  deriving DecidableEq

instance : Fintype Family :=
  ⟨{.selfSum, .crossSum, .selfFiber, .crossFiber, .endgame}, by intro f; cases f <;> simp⟩

instance : Nonempty Family := ⟨Family.selfSum⟩

/-- The law of `(X | X + Y = z)` for independent `X ∼ p`, `Y ∼ q`, Eq. (15), p.21: literal
conditioning of the product law on the event `{x + y = z}`. -/
def fiberLaw (p q : PMF (Vec n)) (z : Vec n) : PMF (Vec n) :=
  (condLaw (pairLaw p q) {ω | ω.1 + ω.2 = z}).map Prod.fst

/-- The joint law of `(X₀, X₁, Y₀, Y₁)`, four mutually independent variables with `X₀, X₁ ∼ p` and
`Y₀, Y₁ ∼ q` (§4.1, p.19). -/
def quadLaw (p q : PMF (Vec n)) : PMF (Vec n × Vec n × Vec n × Vec n) :=
  pairLaw p (pairLaw p (pairLaw q q))

/-- The joint law of `(Z, W)`, `Z := X₁ + Y₀`, `W := X₀ + X₁ + Y₀ + Y₁`, item 5 of §4.1, p.19. -/
def endgameLabel (p q : PMF (Vec n)) : PMF (Vec n × Vec n) :=
  (quadLaw p q).map fun ω => (ω.2.1 + ω.2.2.1, ω.1 + ω.2.1 + ω.2.2.1 + ω.2.2.2)

/-- The law of `U_{z,w} := (X₁ + Y₁ | Z = z, W = w)`, item 5 of §4.1, p.19, by literal
conditioning. -/
def endgameLaw (p q : PMF (Vec n)) (z w : Vec n) : PMF (Vec n) :=
  (condLaw (quadLaw p q)
    {ω | ω.2.1 + ω.2.2.1 = z ∧ ω.1 + ω.2.1 + ω.2.2.1 + ω.2.2.2 = w}).map
      fun ω => ω.2.1 + ω.2.2.2

/-- The natural law of the labels of a family, §4.1, p.19: the sum families have one trivial label;
self-fiber labels are `(x, y) ∼ (X₀ + X₁) ⊗ (Y₀ + Y₁)`; cross-fiber labels are
`(z₀, z₁) ∼ (X₀ + Y₀) ⊗ (X₁ + Y₁)`; endgame labels are `(z, w) ∼ (Z, W)`. -/
def familyLabel (f : Family) (p q : PMF (Vec n)) : PMF (Vec n × Vec n) :=
  match f with
  | .selfSum => PMF.pure (0, 0)
  | .crossSum => PMF.pure (0, 0)
  | .selfFiber => pairLaw (sumLaw p p) (sumLaw q q)
  | .crossFiber => pairLaw (sumLaw p q) (sumLaw p q)
  | .endgame => endgameLabel p q

/-- The raw output pair `(X′, Y′)` of a family at the label `ℓ`, the five items of §4.1, p.19. -/
def familyLaws (f : Family) (p q : PMF (Vec n)) (ℓ : Vec n × Vec n) : PMF (Vec n) × PMF (Vec n) :=
  match f with
  | .selfSum => (sumLaw p p, sumLaw q q)
  | .crossSum => (sumLaw p q, sumLaw p q)
  | .selfFiber => (fiberLaw p p ℓ.1, fiberLaw q q ℓ.2)
  | .crossFiber => (fiberLaw p q ℓ.1, fiberLaw q p ℓ.2)
  | .endgame => (endgameLaw p q ℓ.1 ℓ.2, endgameLaw p q ℓ.1 ℓ.2)

/-- The potential `Φ_{X,Y}(X′, Y′) = d[X′;Y′] + η (d[X;X′] + d[Y;Y′])`, p.29 (parentheses read on the
rendered page; the text layer drops them). -/
def potential (η : ℝ) (p q p' q' : PMF (Vec n)) : ℝ :=
  rd p' q' + η * (rd p p' + rd q q')

/-- `η` has the property promised by Theorem 4.3, p.19: for every `n` and every pair of laws on `F₂ⁿ`
at least one of the five families satisfies
`E[d[X′;Y′] + η d[X;X′] + η d[Y;Y′]] ≤ (1 − η) d[X;Y]`. -/
def IsDecrementConstant (η : ℝ) : Prop :=
  ∀ (n : ℕ) (p q : PMF (Vec n)), ∃ f : Family,
    expect (familyLabel f p q) (fun ℓ =>
      rd (familyLaws f p q ℓ).1 (familyLaws f p q ℓ).2 +
        η * rd p (familyLaws f p q ℓ).1 + η * rd q (familyLaws f p q ℓ).2) ≤
      ENNReal.ofReal ((1 - η) * rd p q)

end

end AlgoPFR


