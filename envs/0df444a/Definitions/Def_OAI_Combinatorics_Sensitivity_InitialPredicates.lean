-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
-- name    : OAI_Combinatorics_Sensitivity_InitialPredicates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:21:43.125396+00:00
-- url     : https://prove2.me/theorems/d1db3872-4963-4416-b896-84cadb72fe34
-- title:
--   Separated row-indicator Hamming balls forming the initial nested family
-- statement:
--   Fix natural numbers $M$ and $L$ and consider the coordinate grid $[M] \times [L]$, where $[n] = \{0, 1, \dots, n-1\}$; think of it as $M$ rows of length $L$. Boolean values are identified with $\{0,1\}$, $d_H$ is the Hamming distance, and $\mathbf{0}^{B}$ is the all-zero input with the coordinates in $B$ flipped.
--
--   1. **Row centers.** For $j \in [M]$, the center $z_j \in \{0,1\}^{[M] \times [L]}$ is the indicator vector of row $j$: $z_j(p) = 1$ exactly when the row of $p$ is $j$.
--
--   2. **Base blocks.** For $j \in [M]$, the base block $B_j = \{ (j, \ell) : \ell \in [L] \}$ is row $j$ viewed as a set of coordinates; a coordinate belongs to $B_j$ exactly when its row is $j$. Note that $\mathbf{0}^{B_j} = z_j$.
--
--   3. **Initial family.** For $d \in \mathbb{N}$ take $L = d+2$. The initial family consists of the $d+1$ predicates $G_0, \dots, G_d$ on $\{0,1\}^{[M] \times [d+2]}$ given by unions of Hamming balls of decreasing radius around the row centers:
--   $$
--   G_q(x) = 1 \iff \exists\, j \in [M]:\ d_H(x, z_j) \le d - q, \qquad q = 0, 1, \dots, d .
--   $$
--
--   Because the radius decreases with $q$, the family is nested. The all-zero input is at distance $d+2$ from every center and is rejected by every $G_q$, while flipping a base block produces a center, which every $G_q$ accepts; two distinct centers are at distance $2(d+2)$. These properties provide the initial sensitivity profiles and the initial sensitive blocks of the recursive construction.
--
--   **Formalization Note** The definitions are `blockCenter`, `baseBlock` (with the membership lemma `mem_baseBlock`) and `initialFamily d M : Fin (d + 1) → (Fin M × Fin (d + 2) → Bool) → Bool`, which is `ballPredicate blockCenter (d - q)`. The radius uses natural-number subtraction, but $q \le d$, so no truncation occurs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/InitialPredicates.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/InitialPredicates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic

namespace OAI

/-! The separated Hamming-ball predicates and their explicit sensitive blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

def blockCenter {M L : ℕ} (j : Fin M) : Fin M × Fin L → Bool :=
  fun p => decide (p.1 = j)

def baseBlock {M L : ℕ} (j : Fin M) : Finset (Fin M × Fin L) :=
  Finset.univ.filter fun p => p.1 = j

@[simp] theorem mem_baseBlock {M L : ℕ} (j : Fin M) (p : Fin M × Fin L) :
    p ∈ baseBlock j ↔ p.1 = j := by
  simp [baseBlock]

def initialFamily (d M : ℕ) : Fin (d + 1) → (Fin M × Fin (d + 2) → Bool) → Bool :=
  fun q => ballPredicate blockCenter (d - q.val)

end Paper320

end

end OAI


