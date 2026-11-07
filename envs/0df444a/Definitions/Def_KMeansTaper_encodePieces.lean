-- Prove2me | Definitions.Def_KMeansTaper_encodePieces
-- name    : KMeansTaper_encodePieces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:26.5822+00:00
-- url     : https://prove2.me/theorems/57f03a67-9a86-4ec8-9ba7-9386b7fccd37
-- title:
--   Binary encodings of pieces, openings, grid inputs and lists of facility sets
-- statement:
--   To speak of polynomial time, inputs and outputs are bit strings. All numbers use the published self-delimiting binary code `encodeNat` (the bit length in unary, a separator, then the binary digits), rationals the published `encodeRat` (sign, numerator, denominator), and instances the published `encodeInstance`. A list of pieces $(\ell_p,Y_p)$ is the concatenation of the codes of $\ell_p$ and $Y_p$; an instance with openings $y$ is the instance code followed by $y_0,\dots,y_{n-1}$; an instance with grid openings is the instance code followed by the pieces; a list of facility sets is the concatenation of their indicator lists; an instance with such a list is the instance code followed by it.
--
--   Every one of these codes is injective, so a machine computing a function of the code computes the function of the object.
--
--   **Formalization Note** The encodings are the mission's choice; the paper measures time "in the input length".
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem A.1, p.20 (PDF p.23); Theorem D.17, p.40 (PDF p.43); Theorem F.1, p.43 (PDF p.46); encodings chosen by the mission

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2

namespace KMeansTaper

open OAI.MetricKMedian (Instance encodeNat encodeRat encodeInstance)

/-- **Encoding of a list of pieces** `(loc, Y)`: each number in the published self-delimiting
binary code `OAI.MetricKMedian.encodeNat`, concatenated (Theorems A.1 and D.17).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3). Encoding chosen by the mission (the paper speaks
of "polynomial time in the input length"). -/
def encodePieces (L : List (ℕ × ℕ)) : List Bool :=
  (L.map (fun p => encodeNat p.1 ++ encodeNat p.2)).flatten

/-- **Input of Theorem A.1**: an instance and rational openings `y`, encoded as the published
`encodeInstance` followed by `y_0, …, y_{n-1}` in the published rational code `encodeRat`. -/
def encodeOpenings (z : Σ I : Instance, (Fin I.n → ℚ)) : List Bool :=
  encodeInstance z.1 ++ (List.ofFn (fun i => encodeRat (z.2 i))).flatten

/-- **Input of Theorem D.17**: an instance and grid openings on pieces. -/
def encodeGridInput (z : Σ _ : Instance, List (ℕ × ℕ)) : List Bool :=
  encodeInstance z.1 ++ encodePieces z.2

/-- **A list of facility sets** of an instance as concatenated indicator bit-lists (each of
length `n`), used by the oracle reduction of Theorem F.1. -/
def encodeSetList (I : Instance) (l : List (Finset (Fin I.n))) : List Bool :=
  (l.map (mask I)).flatten

/-- **Input of the post-processing step of Theorem F.1**: an instance and the oracle's answers. -/
def encodeAnswers (z : Σ I : Instance, List (Finset (Fin I.n))) : List Bool :=
  encodeInstance z.1 ++ encodeSetList z.1 z.2

end KMeansTaper


