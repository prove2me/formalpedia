-- Prove2me | Definitions.Def_HGASUndecidable_Main_PaddingCodes
-- name    : HGASUndecidable_Main_PaddingCodes
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:31.37405+00:00
-- url     : https://prove2.me/theorems/7dfcc23a-cee4-4e19-abb4-904affbfddee
-- title:
--   Explicit polynomial padding codes and guarded decoder composition
-- statement:
--   For $m\le n$, `paddingPolys h j H` is the coordinate polynomial list of Lemma 6.1: each old coordinate is renamed under $x\mapsto(x,0)$, new coordinates receive $-x_i^3$, and all coordinates are multiplied by $(\sum_{k<n}x_k^2)^j$. `paddingCode` serializes these finitely many rational coordinates at declared degree $3+2j$. `guardedPaddingMap` decodes a source code, requires a valid source of dimension $n_0$ and degree $2k_0+1`, applies the supplied lift $f$ to its canonical encoding, requires a valid lifted code of the exact expected dimension and degree $3$, and applies `paddingCode`. Every other branch returns the invalid dimension-zero fallback $(0,1,[])$. Thus all failure behavior is explicit and total.
-- source:
--   Paper #1477, Lemma 6.1 (printed p. 15/PDF 17) for the padding polynomials, and Theorem 2.1 (printed pp. 11–12/PDF 13–14) for composing lift and padding codes. The guards and dimension-zero fallback are the finite encoding needed for the paper's implicit totality of code transformations.

import Definitions.Def_HGASUndecidable_Main_SphereCodes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

noncomputable section

/-- The polynomial coordinates of Lemma 6.1, before serialization. -/
def paddingPolys {m n : ℕ} (h : m ≤ n) (j : ℕ)
    (H : Fin m → QPoly m) : Fin n → QPoly n := fun i =>
  (∑ k : Fin n, MvPolynomial.X k ^ 2) ^ j *
    if hi : i.val < m then
      MvPolynomial.rename (Fin.castLE h) (H ⟨i.val, hi⟩)
    else -(MvPolynomial.X i ^ 3)

/-- The encoded finite rational coefficient list for the explicit polynomial padding. -/
def paddingCode {m n : ℕ} (h : m ≤ n) (j : ℕ)
    (terms : List (ℕ × List ℕ × ℚ)) : ℕ :=
  encodePolys (3+2*j) (paddingPolys h j (codePolys (m,3,terms)))

/-- Guarded code map: malformed input, wrong formats, and failed lifts use a dimension-zero
invalid fallback. The decidable validity instance is the finite code checker. -/
def guardedPaddingMap (n₀ k₀ n j : ℕ) [DecidablePred ValidCode]
    (hn : Nat.choose (n₀+k₀-1) k₀ ≤ n) (f : ℕ → ℕ) (e : ℕ) : ℕ :=
  (((decodeField e).bind fun c =>
    if ValidCode c ∧ c.1 = n₀ ∧ c.2.1 = 2*k₀+1 then
      (decodeField (f (Encodable.encode c))).bind fun q =>
        if ValidCode q ∧ q.1 = Nat.choose (n₀+k₀-1) k₀ ∧ q.2.1 = 3 then
          some (paddingCode hn j q.2.2)
        else none
    else none).getD
    (Encodable.encode ((0, 1, []) : RawFieldCode)))

end
end HGASUndecidable.Main


