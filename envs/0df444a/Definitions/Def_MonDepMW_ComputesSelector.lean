-- Prove2me | Definitions.Def_MonDepMW_ComputesSelector
-- name    : MonDepMW_ComputesSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:03.128195+00:00
-- url     : https://prove2.me/theorems/cc257711-3840-4cfa-a600-f0c6260212d5
-- title:
--   $t(n)$-time computable partition selectors
-- statement:
--   A partition selector $\mathcal P$ is **$t(n)$-time computable** if there is a $t(n)$-time algorithm computing $\mathcal P(G,A)$ given $G$ and $A$, where $n$ is the number of vertices of $G$. This predicate says that a given word-RAM program does this, at every word size above $b_{\mathrm{sel}}(\lfloor\log_2(n+2)\rfloor+1)$, outputting labels of the partition.
--
--   It is the hypothesis of the algorithmic clauses of Lemma 6.1 and Corollary 7.8.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.19

import Mathlib
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_PartitionSelector

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **"𝒫 is t(n)-time computable".** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.19: "𝒫 is t(n)-time computable if there is a t(n)-time algorithm
computing 𝒫(G, A) given G and A, where n is the number of vertices of G." The program `Psel`, on `G` and `A`, outputs
labels of `𝒫(G, A)` within `t n` steps, at every word size above `bsel · (⌊log₂ (n + 2)⌋ + 1)`. -/
def ComputesSelector (𝔓 : PartitionSelector) (Psel : List Instr) (bsel : ℕ) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (W : ℕ), bsel * (Nat.log2 (n + 2) + 1) ≤ W →
    RunsWithin Psel W (t n) (graphInput G ++ setBits A) fun out => decodePartition n out 0 = 𝔓 n G A

end MonDepMW


