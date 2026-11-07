-- Prove2me | Definitions.Def_UniqueOptScores_IsPrefixOf
-- name    : UniqueOptScores_IsPrefixOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:49.959733+00:00
-- url     : https://prove2.me/theorems/df875868-7a02-4662-a089-9f22c0b89d8a
-- title:
--   Finite initial segments of an oracle
-- statement:
--   A finite bit string $\sigma = \sigma_0\cdots\sigma_{\ell-1}$ is an **initial segment** of an oracle $\chi$ (a point of oracle Cantor space $\{0,1\}^{\{0,1\}^*}$) if it lists the first $\ell$ answers of $\chi$ in length-lexicographic order: $\sigma_i = \chi(w_i)$ for $i < \ell$. The oracles with initial segment $\sigma$ form the **prefix cylinder** of $\sigma$, a basic open set.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 8, p.30 (prefix cylinders; length-lexicographic identification)

import Mathlib
import Definitions.Def_UniqueOptScores_str

namespace UniqueOptScores

/-- **A finite initial segment of an oracle.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §8, p.30: oracle bits identified with a binary sequence in length-lexicographic order;
"prefix cylinders".

`IsPrefixOf σ χ` holds when the finite bit string `σ` lists the first `|σ|` answers of the oracle
`χ` in length-lexicographic order: `σᵢ = χ(str i)` for `i < |σ|`.

**Formalization Note.** An oracle is a point `χ : List Bool → Bool` of oracle Cantor space. -/
def IsPrefixOf (σ : List Bool) (χ : List Bool → Bool) : Prop :=
  ∀ i : Fin σ.length, σ.get i = χ (str i)

end UniqueOptScores


