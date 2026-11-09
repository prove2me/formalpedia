-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Spectrum
-- name    : DeletionHash_MixedEdit_Spectrum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:49.0464+00:00
-- url     : https://prove2.me/theorems/10303eee-5c4d-4b1b-bc70-1dc440819ad2
-- title:
--   Integer substring-occurrence spectra
-- statement:
--   A length-$L$ gram is a word in $\alpha^L$. The spectrum $R_L(y)$ is the integer vector indexed by all such grams, with
--   $$R_L(y)_g=\#\{i:0\le i,\ i+L\le |y|,\ y[i:i+L)=g\}.$$
--   Repeated and overlapping occurrences contribute separately. A short word has the zero spectrum for positive $L$. Differences stay integer-valued; the reduction $\overline p$ casts each coordinate into $\mathbb F_2$. These definitions keep the occurrence information needed for both local geometry and random binary hashing.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §2.1, integer occurrence spectrum R_L, printed p. 5 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Words

namespace DeletionHash.MixedEdit

universe u

abbrev Gram (α : Type u) (L : ℕ) := Fin L → α
abbrev Spectrum (α : Type u) (L : ℕ) := Gram α L → ℤ

/-- Counts every valid start, including overlapping occurrences. -/
def spectrum {α : Type u} [DecidableEq α] (L : ℕ) (y : List α) : Spectrum α L :=
  fun g => ((windows L y).count (List.ofFn g) : ℤ)

def parity {α : Type u} {L : ℕ} (p : Spectrum α L) : Gram α L → ZMod 2 :=
  fun g => (p g : ZMod 2)

end DeletionHash.MixedEdit


