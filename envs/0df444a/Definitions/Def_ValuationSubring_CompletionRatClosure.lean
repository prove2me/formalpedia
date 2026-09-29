-- Prove2me | Definitions.Def_ValuationSubring_CompletionRatClosure
-- name    : ValuationSubring_CompletionRatClosure
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/50d9e2f8-0c28-543c-bfa1-c0a68501bf65
-- title:
--   Rational closure: prime field closure in a completion
-- statement:
--   Throughout, $A$ is a valuation subring of `AlgebraicClosure ℚ`, and $C_A$ denotes `A.valuation.Completion`, the completion of the algebraic closure of $\mathbb{Q}$ with respect to the topology attached to the valuation `A.valuation` associated with $A$. Since $C_A$ has characteristic zero, its bottom subfield $\bot$ is the prime field, i.e. the image of $\mathbb{Q}$ in $C_A$. The single definition of the module, [`ValuationSubring.ratClosure A`](../def/ValuationSubring_CompletionRatClosure.html#L13), is the topological closure of this bottom subfield: it is produced as `Subfield.topologicalClosure` applied to $(\bot : \text{Subfield } C_A)$, hence is again a `Subfield` of $C_A$, so that the coercion `↥(ratClosure A)` is a field in its own right and $C_A$ is an algebra over it.
--
--   The accompanying lemmas record the elementary properties of this subfield. `isClosed_ratClosure` states that its underlying set is closed in $C_A$; `bot_le_ratClosure` states that the prime field is contained in it; `coe_ratClosure` identifies its underlying set with the topological closure of the underlying set of $\bot$. Three simp lemmas state that the canonical images in $C_A$ of every rational number, every natural number and every integer belong to `ratClosure A`. Finally, `coe_ratCast_mem_ratClosure` and `coe_natCast_mem_ratClosure` state the same membership for elements obtained by first taking the rational or natural cast inside `AlgebraicClosure ℚ` and then mapping into the completion along the canonical ring homomorphism from `WithVal A.valuation`; the proofs compare the two routes using the compatibility of ring homomorphisms with rational and natural casts. No identification of `ratClosure A` with a $p$-adic field $\mathbb{Q}_p$ is asserted.
--
--   **Relation to Mathlib.** A specialisation, under a project name, of Mathlib's `Subfield.topologicalClosure` applied to the bottom subfield of the valued-field completion; the closedness and monotonicity lemmas are direct instances of the corresponding Mathlib results. The characteristic-zero instance for `A.valuation.Completion` that makes $\bot$ the image of $\mathbb{Q}$ comes from the project module on the decomposition-group action on completions.
--
--   **Where it is used.** The subfield `ratClosure A` serves as the ground field inside the completion $C_A$ of $\overline{\mathbb{Q}}$ at a place $A$, over which the analytic constructions attached to $C_A$ (rank-one valuation theory, compactness of closed balls, and the Bruhat–Tits/upper half-plane material) are carried out.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ValuationSubring_CompletionRatClosure.lean

import Mathlib.Topology.Algebra.Field
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_ValuationSubring_CompletionDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

variable (A : ValuationSubring (AlgebraicClosure ℚ))

def ratClosure : Subfield A.valuation.Completion :=
  (⊥ : Subfield A.valuation.Completion).topologicalClosure

theorem isClosed_ratClosure : IsClosed (ratClosure A : Set A.valuation.Completion) :=
  Subfield.isClosed_topologicalClosure _

theorem bot_le_ratClosure : (⊥ : Subfield A.valuation.Completion) ≤ ratClosure A :=
  Subfield.le_topologicalClosure _

theorem coe_ratClosure :
    (ratClosure A : Set A.valuation.Completion) = closure ((⊥ : Subfield A.valuation.Completion) : Set _) := rfl

@[simp] theorem ratCast_mem_ratClosure (q : ℚ) : (q : A.valuation.Completion) ∈ ratClosure A :=
  bot_le_ratClosure A (SubfieldClass.ratCast_mem _ q)

@[simp] theorem natCast_mem_ratClosure (n : ℕ) : (n : A.valuation.Completion) ∈ ratClosure A :=
  natCast_mem (ratClosure A) n

@[simp] theorem intCast_mem_ratClosure (n : ℤ) : (n : A.valuation.Completion) ∈ ratClosure A :=
  intCast_mem (ratClosure A) n

theorem coe_ratCast_mem_ratClosure (q : ℚ) :
    ((q : AlgebraicClosure ℚ) : A.valuation.Completion) ∈ ratClosure A := by
  have : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) = (q : A.valuation.Completion) := by
    show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
        ((WithVal.equiv A.valuation).symm (q : AlgebraicClosure ℚ)) = _
    rw [map_ratCast, map_ratCast]
  rw [this]; exact ratCast_mem_ratClosure A q

theorem coe_natCast_mem_ratClosure (n : ℕ) :
    ((n : AlgebraicClosure ℚ) : A.valuation.Completion) ∈ ratClosure A := by
  have : ((n : AlgebraicClosure ℚ) : A.valuation.Completion) = (n : A.valuation.Completion) := by
    show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
        ((WithVal.equiv A.valuation).symm (n : AlgebraicClosure ℚ)) = _
    rw [map_natCast, map_natCast]
  rw [this]; exact natCast_mem_ratClosure A n

end ValuationSubring

end


