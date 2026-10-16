-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
-- name    : OAI_Probability_ThorpShuffle_ExtensionBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:02:03.284343+00:00
-- url     : https://prove2.me/theorems/9dc0b70e-af83-434f-85a1-42271b7fb1af
-- title:
--   Cells below the first row and initial segments of the first row of a Young diagram
-- statement:
--   This module introduces two sets of cells of a Young diagram that organize lower bounds on its number of linear extensions.
--
--   Let $D$ be a Young diagram, a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) such that $(i,j)\in D$, $i'\le i$ and $j'\le j$ imply $(i',j')\in D$. Row $0$ is the first (top) row; write $\lambda_1$ for its length. Cells are ordered componentwise: $(i',j')\le(i,j)$ iff $i'\le i$ and $j'\le j$.
--
--   1. *Cells below the first row.*
--   $$
--   \mathrm{Lower}(D)=\{(i,j)\in D:\ i\ne 0\},
--   $$
--   the cells outside the first row; it has $|D|-\lambda_1$ elements.
--   2. *Initial segment of the first row.* For $u\in\mathbb{N}$,
--   $$
--   \mathrm{Top}_u(D)=\{(i,j)\in D:\ i=0,\ j<u\}=\{(0,j):\ j<\min(u,\lambda_1)\},
--   $$
--   the first $u$ cells of the top row (the whole top row when $u\ge\lambda_1$). It is an order ideal of the cell poset of $D$.
--
--   These sets are used to prove that, when $|\mathrm{Lower}(D)|\le\lambda_1$, the number of linear extensions of the cell poset of $D$ (equivalently, of standard Young tableaux of shape $D$) is at least $\binom{\lambda_1}{|\mathrm{Lower}(D)|}$; through the inequality between standard tableaux and Specht dimensions this becomes a lower bound on the degree of the Specht module of shape $D$.
--
--   **Formalization Note** `Lower D` is the subtype of `Cells D` of cells whose first coordinate is nonzero, and `topPrefix D u` is a `Set (Cells D)`. The lemmas about these sets (that `topPrefix D u` is a lower set, its cardinality, and the binomial bound) are proved elsewhere in the project; this module contains only the two definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/ExtensionBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/ExtensionBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions

namespace OAI

universe uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Young
open scoped Classical

abbrev Lower (D : YoungDiagram) := {x : Cells D // x.val.1 ≠ 0}

def topPrefix (D : YoungDiagram) (u : ℕ) : Set (Cells D) :=
  {x | x.val.1 = 0 ∧ x.val.2 < u}

end Thorp.Young

end

end OAI


