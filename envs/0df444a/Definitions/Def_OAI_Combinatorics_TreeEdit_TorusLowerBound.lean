-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_TorusLowerBound
-- name    : OAI_Combinatorics_TreeEdit_TorusLowerBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:41:17.406765+00:00
-- url     : https://prove2.me/theorems/c90ebdde-4fad-4d1b-b994-4e4f55cc1b2b
-- title:
--   The one-bit identity code on binary words
-- statement:
--   This file defines the trivial block code on the binary alphabet,
--
--   $$\iota:\{0,1\}\to\{0,1\}^1,\qquad \iota(b)=b,$$
--
--   sending each bit to the one-letter word consisting of that bit. Its concatenation extension $\operatorname{enc}_\iota(x_1\cdots x_\ell)=\iota(x_1)\cdots\iota(x_\ell)$ is the identity on binary words.
--
--   The general distortion-transfer theorem is formulated for a family of words followed by a block code $c:\Gamma\to\{0,1\}^P$ satisfying a lower bound on edit distances of encoded words. In the circle-tree lower bound for the $\ell_1$ distortion of binary edit distance the words are already binary after the delimiter encoding, so the transfer is applied with $\Gamma=\{0,1\}$, $P=1$ and this identity code, for which the required lower bound holds trivially.
--
--   **Formalization Note** The Lean name is `singletonCode : Bool → Word Bool 1`, defined by `singletonCode a = ⟨[a], rfl⟩`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/TorusLowerBound.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/TorusLowerBound.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
import Definitions.Def_OAI_Combinatorics_TreeEdit_DistortionTransfer

namespace OAI

namespace TreeEdit

def singletonCode (a : Bool) : Word Bool 1 := ⟨[a], rfl⟩

namespace TorusTree
open scoped BigOperators
open Classical Filter

end TorusTree

end TreeEdit

end OAI


