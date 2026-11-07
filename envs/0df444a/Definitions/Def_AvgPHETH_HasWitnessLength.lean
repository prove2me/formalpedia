-- Prove2me | Definitions.Def_AvgPHETH_HasWitnessLength
-- name    : AvgPHETH_HasWitnessLength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:25.162418+00:00
-- url     : https://prove2.me/theorems/383a12b4-3313-4ff3-97f6-5f9c35d82c6a
-- title:
--   Witness length of a language in $\Sigma_d^{p,O}$
-- statement:
--   A language $L$ has **witness length** $w$ as a $\Sigma_d^{p,O}$ language if
--
--   $$x\in L\iff\exists y_1\,\forall y_2\cdots Q_dy_d\;V(x,y_1,\dots,y_d)$$
--
--   for a verifier $V$, polynomial-time with oracle $O$, with moves of lengths $|y_i|=\ell_i(|x|)$ such that $w=\ell_1+\dots+\ell_d$, where $w$ is at most polynomial.
--
--   **Formalization Note** Each $\ell_i$ is required to be polynomial-time computable. The page does not say so, but Lemma 6.1 and the padding step in the proof of Theorem 1.2 (i) use it, and without it a language of this form can be undecidable. Moves of length $0$ are allowed.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4); footnote 1, p.3 (PDF 5)

import Mathlib
import Definitions.Def_AvgPHETH_AltLen
import Definitions.Def_AvgPHETH_IsPolyLen
import Definitions.Def_AvgPHETH_PolyPredO

namespace AvgPHETH

/-- `L ∈ Σ_d^{p,O}` has **witness length** `w` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4), and footnote 1, p.3 (PDF 5)):
`x ∈ L ⟺ ∃y₁ ∀y₂ ⋯ Q_d y_d V(x, y₁, …, y_d)` for a polynomial-time verifier `V` with oracle `O`,
moves of lengths `|y_i| = ℓ_i(|x|)` with `w = ∑ ℓ_i`, and `w` at most polynomial.

**Formalization Note** The move lengths are polynomial-time computable functions of the input length. The
page does not say so; Lemma 6.1 and the padding step on p.29 (PDF 31) use it, and with an uncomputable
length the language can be undecidable. Moves of length `0` are allowed. -/
def HasWitnessLength (O : Set (List Bool)) (d : ℕ) (L : Set (List Bool)) (w : ℕ → ℕ) : Prop :=
  (∃ p : Polynomial ℕ, ∀ n, w n ≤ p.eval n) ∧
  ∃ (ℓ : Fin d → ℕ → ℕ) (V : List (List Bool) → Prop),
    (∀ i, IsPolyLen (ℓ i)) ∧ (∀ n, ∑ i, ℓ i n = w n) ∧ PolyPredO O (d + 1) V ∧
    ∀ x : List Bool, x ∈ L ↔
      AltLen (List.ofFn (fun i => ℓ i x.length)) true (fun ys => V (x :: ys))

end AvgPHETH


