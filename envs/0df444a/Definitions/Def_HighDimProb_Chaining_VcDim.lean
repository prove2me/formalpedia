-- Prove2me | Definitions.Def_HighDimProb_Chaining_VcDim
-- name    : HighDimProb_Chaining_VcDim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:37.807301+00:00
-- url     : https://prove2.me/theorems/8de5884b-cca9-4996-bde1-6b3f163b6f86
-- title:
--   The VC dimension $\mathrm{vc}(F)$ of a class of Boolean functions
-- statement:
--   This is the **VC (Vapnik-Chervonenkis) dimension** of a class $F$ of Boolean functions on a
--   domain $\Omega$: the largest cardinality of a subset $\Lambda \subseteq \Omega$ shattered by
--   $F$ (`Shatters`), or $\infty$ if the largest cardinality does not exist. It is the
--   combinatorial complexity measure the Sauer-Shelah Lemma (Theorem 8.3.16) bounds $|F|$ by.
--
--   **Formalization Note** Valued in `ℕ∞ = WithTop ℕ`, as a supremum (over the subtype of
--   shattered subsets $\Lambda$) of `Set.encard Λ`, which is already `⊤` for an infinite $\Lambda$;
--   the supremum of an unbounded or empty family in the complete lattice `ℕ∞` reproduces the
--   book's own footnote ("if the largest cardinality does not exist, we set $\mathrm{vc}(F) =
--   \infty$") with no case split — no separate finiteness hypothesis is needed anywhere this
--   definition is used.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 200, Definition 8.3.1 (part 2) and footnote 1

import Mathlib
import Definitions.Def_HighDimProb_Chaining_Shatters

namespace HighDimProb.Chaining

/-- The **VC dimension** `vc(F)` of a class `F` of Boolean functions on `Ω`: the largest
cardinality of a subset `Λ ⊆ Ω` shattered by `F`. Vershynin, *High-Dimensional Probability*
(2018), Definition 8.3.1, p. 200 (PDF p. 208): "The VC dimension of `F`, denoted `vc(F)`, is the
largest cardinality of a subset `Λ ⊆ Ω` shattered by `F`," with the book's own footnote 1: "If
the largest cardinality does not exist, we set `vc(F) = ∞`." Valued in `ℕ∞ = WithTop ℕ` via
`Set.encard` (which is already `⊤` on an infinite `Λ`) and a supremum over the subtype of
shattered subsets: the supremum of an unbounded or empty family in the complete lattice `ℕ∞`
reproduces the book's footnote exactly (`vc(F) = 0` when only `Λ = ∅`, vacuously shattered by
every `F`, achieves the supremum; `vc(F) = ⊤` when arbitrarily large finite, or some infinite,
`Λ` is shattered), with no case split needed. -/
noncomputable def vcDim {Ω : Type} (F : Set (Ω → Bool)) : ℕ∞ :=
  ⨆ (Λ : {Λ : Set Ω // Shatters F Λ}), Λ.1.encard

end HighDimProb.Chaining


