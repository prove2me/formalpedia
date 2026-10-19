-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
-- name    : OAI_Combinatorics_FiniteCircle_Lower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:11:57.781862+00:00
-- url     : https://prove2.me/theorems/21df2284-c1fd-415e-a764-815f301b4d38
-- title:
--   The length cap $(n^4)^{32 n^8}$ for the explicit lower-bound instances
-- statement:
--   For $n\in\mathbb{N}$ define the length cap
--   $$
--   \operatorname{cap}(n)=\bigl(n^4\bigr)^{32\,(n^4)^2},\qquad\text{that is,}\qquad \operatorname{cap}(n)=h^{32h^2}\ \text{ with } h=n^4 .
--   $$
--   It is a natural number with $\log\operatorname{cap}(n)=128\,n^8\log n$ for $n\ge1$, and $\operatorname{cap}(0)=0^0=1$.
--
--   The cap measures how long the explicit hard instances of the lower bound become. In the constructions with parameter $h=n^4$ (and $h\ge10^8$), the binary encodings of the mask words and of the excluded-translation words are shown to have length at most $h^{32h^2}=\operatorname{cap}(n)$. For a sufficiently large target length $d$ one picks the integer $q$ with $\operatorname{cap}(2q)\le d<\operatorname{cap}(2q+2)$: the left inequality guarantees that the witness families built with $n=2q$ fit within length $d$, and the right inequality is inverted to show $\exp\bigl(\tfrac{1}{8192}\sqrt{\log d\,\log\log d}\bigr)\le(2q)^{4q^4}$, which compares the target bound with the distortion lower bound obtained for these families.
--
--   **Formalization Note** `lowerCap n` is `(n^4)^(32*(n^4)^2)`, computed in natural-number arithmetic.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Lower.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Lower.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

def lowerCap (n : ℕ) : ℕ := (n^4)^(32*(n^4)^2)

end FiniteCircle

end OAI


