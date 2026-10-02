-- Prove2me | Definitions.Def_opg37364_lps13_trace
-- name    : opg37364_lps13_trace
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-12T05:40:37.988563+00:00
-- url     : https://prove2.me/theorems/34e7392f-4a75-4871-a02e-92f4167d843b
-- title:
--   Fixed-13 LPS polynomial, reduced-word matrices and closed-word counts
-- statement:
--   Structural definitions for the existing LPS13 graph: the polynomials P₀=1, P₁=X, Pₙ₊₂=X Pₙ₊₁−13 Pₙ; the right-ordered projective generator product; real right-translation matrices; the sum Bₘ over all adjacent-reduced words of length m; and the finite count Cₘ of those words with projective product 1. Words are encoded by Fin m → Fin 14. No recurrence theorem, trace identity, counting estimate or LPS existence assertion is included in this definition bundle.
-- source:
--   OPG37364 Stage 16, fixed-p=13 nonbacktracking polynomial/closed-word trace derivation. Uses the existing LPS13 graph definition 5913399a-8c29-444e-8f1f-7e7ec09704f1 and the actual proved construction helpers from theorem a1b44539-4a01-4515-b3fe-7e0b60624a02, accepted submission 5cd7397d-42aa-4aad-b8ce-29d615dffe60 (arexychen). A formalization of classical finite-word and polynomial identities; no mathematical novelty or unproved LPS spectral assertion is claimed.

import Definitions.Def_opg37364_lps13_words
import Definitions.Def_opg37364_lps13_eigenspaces
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.List.OfFn

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace OPG37364

/-- The fixed continuation-factor-13 polynomials; in particular P₂=X²−13. -/
def lps13NonbacktrackingPolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 => Polynomial.X * lps13NonbacktrackingPolynomial (n+1) -
      13 * lps13NonbacktrackingPolynomial n

/-- Right-ordered projective product, the same formula as the existing Girth13.eval.
This definition does not use a closed-word bound or any girth result. -/
def lps13ProjectiveWordProduct {q : ℕ} [Fact q.Prime]
    (hq : 13 < q) (i : LPS13Root q) (w : List (Fin 14)) : LPS13Vertex q :=
  (w.map (lps13Generator hq i)).prod

/-- The matrix of right translation; row x and column y records y=x*s. -/
def lps13TranslationMatrix {q : ℕ} [Fact q.Prime] (s : LPS13Vertex q) :
    Matrix (LPS13Vertex q) (LPS13Vertex q) ℝ :=
  fun x y => if x*s = y then 1 else 0

/-- Sum of translations over the reduced words of exactly m letters.
The finite encoding is a function Fin m → Fin 14. -/
def lps13ReducedWordMatrix {q : ℕ} [Fact q.Prime]
    (hq : 13 < q) (i : LPS13Root q) (m : ℕ) :
    Matrix (LPS13Vertex q) (LPS13Vertex q) ℝ :=
  ∑ w : Fin m → Fin 14,
    if lps13WordReduced (List.ofFn w) then
      lps13TranslationMatrix (lps13ProjectiveWordProduct hq i (List.ofFn w)) else 0

/-- Number of reduced length-m words whose projective product is one. -/
def lps13ClosedReducedWordCount {q : ℕ} [Fact q.Prime]
    (hq : 13 < q) (i : LPS13Root q) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin m → Fin 14 =>
    lps13WordReduced (List.ofFn w) ∧ lps13ProjectiveWordProduct hq i (List.ofFn w) = 1)).card

end OPG37364


