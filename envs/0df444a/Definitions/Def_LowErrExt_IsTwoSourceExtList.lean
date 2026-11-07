-- Prove2me | Definitions.Def_LowErrExt_IsTwoSourceExtList
-- name    : LowErrExt_IsTwoSourceExtList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:50.026208+00:00
-- url     : https://prove2.me/theorems/ae5e1611-26bc-4b7e-a0ea-83267a38f81d
-- title:
--   A string function as a two-source extractor $\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$
-- statement:
--   A function $E$ on pairs of bit strings is a **$(k,\varepsilon)$ two-source extractor $\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$** if
--
--   1. on every pair of $n$-bit inputs it outputs exactly $m$ bits, and
--   2. for all independent sources $\mathbf X,\mathbf Y$ on $\{0,1\}^n$ with min-entropy at least $k$, $E(\mathbf X,\mathbf Y)$ is $\varepsilon$-close to $U_m$ in statistical distance.
--
--   **Formalization Note** $U_m$ is the uniform distribution on $\{0,1\}^m$ (`FuzzyExtractors.Hamming.uniformBits m`). The value of $E$ on inputs of other lengths is free.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), p.4; Definition 2.24, p.19

import Mathlib
import Definitions.Def_LowErrExt_IsTwoSourceExtractor
import Definitions.Def_LowErrExt_IsPolyTime

namespace LowErrExt

/-- **A string function as a two-source extractor on `{0,1}ⁿ × {0,1}ⁿ → {0,1}ᵐ`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
p.4 and Definition 2.24, p.19: "a two-source extractor is a single deterministic function
2Ext : {0, 1}n × {0, 1}n → {0, 1}m … We say that it works for min-entropy k and error ε if for any
independent sources X, Y ∼ {0, 1}n with min-entropy at least k, the output 2Ext(X, Y) is ε-close to
Um".

`IsTwoSourceExtList n k m ε E`: on any two inputs of length `n`, `E` outputs exactly `m` bits, and,
read as an element of `{0,1}ᵐ`, `E` restricted to `{0,1}ⁿ × {0,1}ⁿ` is a `(k, ε)` two-source
extractor.

**Formalization Note.** `E` acts on lists of bits; on pairs of other lengths its value is free.
`{0,1}ᵐ` is `Fin m → Bool`, whose uniform law is `FuzzyExtractors.Hamming.uniformBits m`
(`= PMF.uniformOfFintype`). -/
def IsTwoSourceExtList (n : ℕ) (k : ℝ) (m : ℕ) (ε : ℝ) (E : List Bool → List Bool → List Bool) :
    Prop :=
  (∀ x y : Fin n → Bool, (E (List.ofFn x) (List.ofFn y)).length = m) ∧
    IsTwoSourceExtractor k ε fun x y : Fin n → Bool => listOut m (E (List.ofFn x) (List.ofFn y))

end LowErrExt


