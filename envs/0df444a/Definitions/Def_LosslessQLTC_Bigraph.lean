-- Prove2me | Definitions.Def_LosslessQLTC_Bigraph
-- name    : LosslessQLTC_Bigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:06.34794+00:00
-- url     : https://prove2.me/theorems/e18fe5ca-edb6-4b08-8d77-1e641ee78bc8
-- title:
--   One-sided $(c,\varepsilon)$-lossless biregular bigraphs
-- statement:
--   Let $H=(L,R,E)$ be a bigraph. For $A\subseteq L$, write $\Gamma(A)$ for the set of neighbours of $A$, write $\deg_S(v)=|\Gamma(v)\cap S|$ for a vertex $v$ and a vertex set $S$, and write $e(A,B)$ for the number of edges between $A\subseteq L$ and $B\subseteq R$. The bigraph is **$(D,D')$-biregular** if left vertices have degree $D$ and right vertices have degree $D'$. For $c,\varepsilon\in(0,1)$ it is **one-sided $(c,\varepsilon)$-lossless from $L$ to $R$** if every $A\subseteq L$ with $|A|\le c|L|$ satisfies
--
--   $$|\Gamma(A)|\ge(1-\varepsilon)D|A|.$$
--
--   These are the direction graphs of a lossless cubical complex.
--
--   **Formalization Note.** Biregularity is a separate predicate. The range $c,\varepsilon\in(0,1)$ is part of the lossless predicate.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Definition 2.17 and §2.5, p.19

import Mathlib

namespace LosslessQLTC

/-- The neighbourhood `Γ(A)` of `A ⊆ L` in a bigraph `H = (L, R, E)`.
Source: Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless
Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), §2.5, p.19. -/
def nbhd {L R : Type} [DecidableEq R] [Fintype R] (E : L → R → Prop) [DecidableRel E]
    (A : Finset L) : Finset R :=
  Finset.univ.filter fun y => ∃ x ∈ A, E x y

/-- `deg_S(y) = |Γ(y) ∩ S|` for a right vertex `y` and `S ⊆ L` (arXiv:2610.00525, p.19). -/
def degLeft {L R : Type} (E : L → R → Prop) [DecidableRel E] (S : Finset L) (y : R) : ℕ :=
  (S.filter fun x => E x y).card

/-- `deg_S(x) = |Γ(x) ∩ S|` for a left vertex `x` and `S ⊆ R` (arXiv:2610.00525, p.19). -/
def degRight {L R : Type} (E : L → R → Prop) [DecidableRel E] (S : Finset R) (x : L) : ℕ :=
  (S.filter fun y => E x y).card

/-- `e(A, B)`: the number of edges between `A ⊆ L` and `B ⊆ R` (arXiv:2610.00525, p.19). -/
def edgeCount {L R : Type} (E : L → R → Prop) [DecidableRel E] (A : Finset L) (B : Finset R) : ℕ :=
  ((A ×ˢ B).filter fun p => E p.1 p.2).card

/-- `H = (L, R, E)` is `(D, D′)`-biregular: left vertices have degree `D`, right vertices `D′`
(arXiv:2610.00525, p.17 and Definition 2.17, p.19). -/
def IsBiregular {L R : Type} [Fintype L] [Fintype R] (E : L → R → Prop) [DecidableRel E]
    (D D' : ℕ) : Prop :=
  (∀ x, degRight E Finset.univ x = D) ∧ (∀ y, degLeft E Finset.univ y = D')

/-- Definition 2.17 (arXiv:2610.00525, p.19): for `c, ε ∈ (0, 1)`, `H` is one-sided
`(c, ε)`-lossless from `L` to `R` if every `A ⊆ L` with `|A| ≤ c|L|` has `|Γ(A)| ≥ (1 − ε)D|A|`.

**Formalization Note.** The biregularity of Definition 2.17 is a separate predicate,
`IsBiregular`; the range `c, ε ∈ (0, 1)` is part of this predicate. -/
def IsOneSidedLossless {L R : Type} [Fintype L] [Fintype R] [DecidableEq R]
    (E : L → R → Prop) [DecidableRel E] (D : ℕ) (c ε : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧ 0 < ε ∧ ε < 1 ∧
    ∀ A : Finset L, (A.card : ℝ) ≤ c * Fintype.card L →
      (1 - ε) * D * A.card ≤ (nbhd E A).card

end LosslessQLTC


