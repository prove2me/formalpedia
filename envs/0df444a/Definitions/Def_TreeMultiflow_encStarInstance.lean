-- Prove2me | Definitions.Def_TreeMultiflow_encStarInstance
-- name    : TreeMultiflow_encStarInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:29.52821+00:00
-- url     : https://prove2.me/theorems/cd992c69-35cd-4f26-a87f-2a9c9c5ea30d
-- title:
--   Binary encoding of a star instance
-- statement:
--   The encoding of a star instance is the sequence of words: the number of local paths, then $(\beta_1,\beta_2)$ for each local path, then $(\beta,i)$ for each crossing path, separated by a separator symbol, with all numbers in binary, over the alphabet $\{0,1,2,3\}$.
--
--   **Formalization Note** As for rational instances, polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`; the encoding is injective.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Lemma 5.1, p.9 and Appendix B, p.12 (Running time)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_TreeMultiflow_StarInstance

namespace TreeMultiflow

/-- **Binary encoding of an instance of Lemma 5.1.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Lemma 5.1,
p.9 ("We can do this in polynomial time"), with Appendix B, p.12 ("Running time").

`encStarInstance S` is the list of words `|locals|`, then `β₁, β₂` for each local path, then
`β, i` for each crossing path, joined by the separator `3`; numbers are binary
(`OnlineCRS.Combine.encNat`).

**Formalization Note.** Same conventions as `encRatInstance`: Mathlib's
`Turing.TM2ComputableInPolyTime` over `OnlineCRS.Combine.Sym = Fin 4`; the encoding is injective
(decoded in `Solutions/verification/TreeMultiflow_encodings.lean`). -/
def encStarInstance (S : StarInstance) : List OnlineCRS.Combine.Sym :=
  [3].intercalate
    ([OnlineCRS.Combine.encNat S.locals.length] ++
      S.locals.flatMap (fun p => [OnlineCRS.Combine.encNat p.1, OnlineCRS.Combine.encNat p.2]) ++
      S.crossing.flatMap (fun p => [OnlineCRS.Combine.encNat p.1, OnlineCRS.Combine.encNat p.2]))

end TreeMultiflow


