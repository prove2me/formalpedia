-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
-- name    : OAI_Combinatorics_TreeEdit_CircleParameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:33:42.907503+00:00
-- url     : https://prove2.me/theorems/06b58d9b-945e-483e-8e07-c8f846b966fc
-- title:
--   Length, alphabet size and binary width of the circle-tree witness
-- statement:
--   With branching $m(k)=16k^3$, repetitions $T(k)=k^{52k}$ and resolution $R(k)=k^{8k}$ as in the circle-tree obstruction, this file names four derived quantities for $k\in\mathbb{N}$.
--
--   1. **Word length** $N(k)=\bigl(m(k)\,T(k)\bigr)^k$.
--   2. **Alphabet size** $A(k)=m(k)^k\,R(k)$.
--   3. **Binary width** $B(k)=2\lceil\log_2 A(k)\rceil+3$, where $\lceil\log_2 n\rceil$ denotes the least $e\in\mathbb{N}$ with $n\le 2^e$.
--   4. **Binary length** $N(k)\,B(k)$.
--
--   The root of the circle-phase tree has height $k$, so its word has length $(mT)^k=N(k)$ over an alphabet of $m^kR=A(k)$ symbols, each a root-to-leaf path with a bin index. Encoding each symbol by a synchronizing binary codeword of width $B(k)$ produces binary words of the single length $N(k)B(k)$. These are the witness words for the lower bound $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$ on the $\ell_1$ distortion of binary edit distance, where for each large length cap $d$ the parameter $k$ is chosen with $N(k)B(k)\le d$.
--
--   **Formalization Note** The Lean names are `wordLength`, `alphabetSize`, `binaryWidth` and `binaryLength`; the ceiling logarithm is `Nat.clog 2`, so `binaryWidth k` agrees with the delimiter-code width `Delimiter.width (alphabetSize k)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleParameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleParameters.lean by skeleton subtraction
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

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

def wordLength (k : ℕ) : ℕ := (branching k * repetitions k)^k
def alphabetSize (k : ℕ) : ℕ := branching k^k * resolution k
def binaryWidth (k : ℕ) : ℕ := 2*Nat.clog 2 (alphabetSize k)+3
def binaryLength (k : ℕ) : ℕ := wordLength k*binaryWidth k

end TreeEdit.TorusTree

end OAI


