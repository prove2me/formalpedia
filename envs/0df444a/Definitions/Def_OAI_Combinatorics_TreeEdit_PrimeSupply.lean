-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
-- name    : OAI_Combinatorics_TreeEdit_PrimeSupply
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:31:42.42499+00:00
-- url     : https://prove2.me/theorems/d9df51e1-a305-4607-ae6c-538c13e0f57a
-- title:
--   Primes in the band $(k^a,k^{a+1}]$
-- statement:
--   For natural numbers $k$ and $a$, the prime band is the finite set
--
--   $$\mathcal{B}(k,a)=\{\,p\le k^{a+1} : p \text{ prime}\,\}\setminus\{\,p\le k^{a} : p\text{ prime}\,\}.$$
--
--   Its membership criterion is recorded explicitly: $p\in\mathcal{B}(k,a)$ implies that $p$ is prime and $k^a<p\le k^{a+1}$.
--
--   The band $\mathcal{B}(k,2)$, the primes in $(k^2,k^3]$, is the pool from which the circle-phase tree construction for binary edit distance draws its periods, each node selecting $16k$ distinct primes from it. Since all pool primes exceed $k^2$, a product of many of them is large; since they are at most $k^3$, a product of $16k$ of them is at most $k^{48k}$. A Chebyshev-type lower bound on the size of the band, proved separately, guarantees that the pool is large enough.
--
--   **Formalization Note** The Lean definition is `PrimeSupply.band k a = (k ^ (a + 1)).primesLE \ (k ^ a).primesLE`, where `Nat.primesLE n` is the finset of primes at most `n`; the lemma `mem_band` gives the membership criterion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/PrimeSupply.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/PrimeSupply.lean by skeleton subtraction
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

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace PrimeSupply
open Filter

noncomputable def band (k a : ℕ) := (k ^ (a + 1)).primesLE \ (k ^ a).primesLE

lemma mem_band {k a p : ℕ} (hp : p ∈ band k a) : Nat.Prime p ∧ k ^ a < p ∧ p ≤ k ^ (a + 1) := by
  obtain ⟨hp, hlo⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hup, hprime⟩ := Nat.mem_primesLE.mp hp
  refine ⟨hprime, ?_, hup⟩
  by_contra hn
  exact hlo (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hprime⟩)

end PrimeSupply

end TreeEdit

end OAI


