-- Prove2me | Definitions.Def_LinfContractionFP_SubSolverSpec
-- name    : LinfContractionFP_SubSolverSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:11.4441+00:00
-- url     : https://prove2.me/theorems/cacc7344-d26e-4fce-8e4a-4b0782ccfe98
-- title:
--   Specification of the recursive Solve calls inside ThinLabel
-- statement:
--   A procedure $\mathrm{solveSub}$ meets the **sub-solver specification** for gap $\gamma$ if, for every set $S$ of at most $d/2$ of the $d$ coordinates, every $(1-\gamma)$-contraction $g$ of $[0,1]^S$ and every $\eta'>0$, $\mathrm{solveSub}(S,g,\eta')$ is an $\eta'$-near fixed point of $g$.
--
--   This is what Algorithm 2 needs from its two recursive calls of Solve (lines 6–7), i.e. the paper's inductive hypothesis on lower dimensions.
--
--   **Formalization Note** The specification is satisfiable: a procedure that returns the exact fixed point meets it. "At most $d/2$" is $2|S|\le d$.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 2, lines 6–7, p.9; Section 5, p.8

import Mathlib
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_IsNearFixed

namespace LinfContractionFP

/-- The specification of the recursive calls of `Solve` inside ThinLabel (Algorithm 2,
lines 6–7): a procedure `solveSub` that, given a set `S` of at most `d/2` of the `d` coordinates,
a `(1 − γ)`-contraction `g` of `[0,1]^S` and a tolerance `η' > 0`, returns an `η'`-near fixed
point of `g`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Algorithm 2, lines 6–7,
p.9 ("y^narr ∈ R^N ← Solve(y ↦ f_N(y, q_{−N}), γη/2)"), and Section 5, p.8 ("Each recursive
problem has dimension at most d/2").

**Formalization Note.** ThinLabel's milestones (Eq. (4), Lemma 2, Corollary 2) are stated for
any `solveSub` with this specification, in place of `Solve` itself: that is the paper's
inductive hypothesis on lower dimensions. The specification is satisfiable for `0 < γ ≤ 1` (a
procedure returning the exact fixed point meets it; see the mission's sanity file). "At most
d/2" is `2 |S| ≤ d`. -/
def SubSolverSpec {ι : Type} [Fintype ι] (γ : ℝ)
    (solveSub : (S : Finset ι) → ((↥S → ℝ) → (↥S → ℝ)) → ℝ → (↥S → ℝ)) : Prop :=
  ∀ (S : Finset ι) (g : (↥S → ℝ) → (↥S → ℝ)) (η' : ℝ), 2 * S.card ≤ Fintype.card ι →
    IsContraction γ g → 0 < η' → IsNearFixed g η' (solveSub S g η')

end LinfContractionFP


