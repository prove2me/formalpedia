-- Prove2me | Definitions.Def_LowErrExt_IsSpread
-- name    : LowErrExt_IsSpread
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:30.352458+00:00
-- url     : https://prove2.me/theorems/6be65126-ec08-4b6e-a9f5-b84552e420eb
-- title:
--   $(r,k)_\alpha$-spreadness in a coset ($\alpha\in\{2,\infty\}$)
-- statement:
--   Let $G$ be a finite abelian group and $V\subseteq G$. A source $\mathbf X$ supported in $V$ is **$(r,k)_\alpha$-spread in $V$** if for every homomorphism $L$ out of $G$,
--   $$H_0[L(V)]\ge r\ \Longrightarrow\ H_\alpha[L(\mathbf X)]\ge k .$$
--   Spreadness is vacuous when $r>H_0[V]$ and trivial when $k\le 0$. Only $\alpha=2$ (collision entropy) and $\alpha=\infty$ (min-entropy) occur in the mission.
--
--   **Formalization Note** A homomorphism with kernel $K$ is an injective map composed with the quotient map $\pi_K:G\to G/K$, so $L(V)$, $\pi_K(V)$ have the same size and $L(\mathbf X)$, $\pi_K(\mathbf X)$ the same entropy. The definition therefore quantifies over subgroups $K\le G$ and the quotient maps, which is the same condition (the argument of Observation 6.5). The support condition $\mathbf X\sim V$ is part of the definition.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definitions 6.2 and 6.4, Observation 6.5, pp.37–38

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_H2

universe u

namespace LowErrExt

/-- **Spreadness with respect to an entropy `H`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 6.2, p.37: "A random variable X ∼ V is (r, k)α-spread in V if for any homomorphism L
out of G such that H0[L(V)] ≥ r, Hα[L(X)] ≥ k."

`IsSpreadBy H r k V X` says that `supp(X) ⊆ V` and, for every subgroup `K ≤ G`, if the image of `V`
in `G/K` has `log₂`-size at least `r`, then `H(π_K(X)) ≥ k`, where `π_K : G → G/K` is the quotient map.

**Formalization Note.** A homomorphism `L` out of `G` with kernel `K` factors as an injective map
after `π_K`, so `L(V)` and `π_K(V)` have the same size and `L(X)`, `π_K(X)` the same entropy
(the argument of Observation 6.5, p.38); quantifying over subgroups `K` is therefore the same
condition, and avoids quantifying over all target groups. `V` is not required to be a coset here;
every statement says so separately. -/
def IsSpreadBy {G : Type u} [AddCommGroup G] (H : ∀ Q : Type u, PMF Q → ℝ) (r k : ℝ)
    (V : Set G) (X : PMF G) : Prop :=
  X.support ⊆ V ∧ ∀ K : AddSubgroup G,
    r ≤ H0 ((QuotientAddGroup.mk : G → G ⧸ K) '' V) →
      k ≤ H (G ⧸ K) (X.map (QuotientAddGroup.mk : G → G ⧸ K))

/-- **`(r, k)₂`-spreadness** (Definition 6.2, p.37, with `α = 2`): spreadness for the collision
entropy `H₂`. -/
def IsSpread2 {G : Type u} [AddCommGroup G] (r k : ℝ) (V : Set G) (X : PMF G) : Prop :=
  IsSpreadBy (fun _ Y => H2 Y) r k V X

/-- **`(r, k)∞`-spreadness** (Definition 6.2, p.37, with `α = ∞`): spreadness for the min-entropy
`H∞` (`FuzzyExtractors.Hamming.minEntropy`). -/
def IsSpreadInf {G : Type u} [AddCommGroup G] (r k : ℝ) (V : Set G) (X : PMF G) : Prop :=
  IsSpreadBy (fun _ Y => FuzzyExtractors.Hamming.minEntropy Y) r k V X

end LowErrExt


