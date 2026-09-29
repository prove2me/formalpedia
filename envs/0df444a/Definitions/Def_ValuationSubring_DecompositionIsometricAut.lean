-- Prove2me | Definitions.Def_ValuationSubring_DecompositionIsometricAut
-- name    : ValuationSubring_DecompositionIsometricAut
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/5504fd48-d5c0-5dd4-bda9-2a5644e695fb
-- title:
--   Decomposition group as isometric automorphisms of the completion
-- statement:
--   Throughout, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` subject to the standing hypothesis `A.DecompositionIsometric ℚ`, i.e. every $\sigma$ in the decomposition subgroup $D_A$ of $A$ over $\mathbb{Q}$ satisfies $v_A(\sigma x) = v_A(x)$ for all $x \in \overline{\mathbb{Q}}$, where $v_A =$ `A.valuation`; under this hypothesis $D_A$ acts by continuous ring automorphisms on the completion $C_A =$ `A.valuation.Completion`, written $\sigma \bullet x$. First, `smul_completion_eq_self_of_mem_ratClosure` states that for $\sigma \in D_A$ and $x$ in `ratClosure A` — the topological closure in $C_A$ of the bottom subfield, i.e. of the prime subfield $\mathbb{Q}$ — one has $\sigma \bullet x = x$; this is obtained from the fact that the fixed set of $\sigma$ is closed and contains the bottom subfield, so it contains its closure.
--
--   The principal definition, `decompositionToIsometricAut`, is the group homomorphism from $D_A$ to [`CerednikDrinfeld.Omega.IsometricAut ↥(ratClosure A) A.valuation.Completion`](../def/CerednikDrinfeld_DrinfeldHolomorphic.html#L587). The target is the group of triples consisting of a ring automorphism of $C_A$ together with proofs that it preserves the valuation and fixes the image of the base field pointwise — here the base field being `ratClosure A`; thus the structure carries two theorems as fields. The automorphism attached to $\sigma$ is $x \mapsto \sigma \bullet x$, its isometry is the valuation-invariance of the completed action, and the fixing of `ratClosure A` is the lemma above; the homomorphism property is the multiplicativity of the action.
--
--   Four further lemmas identify the underlying ring equivalence: on elements it is $x \mapsto \sigma \bullet x$, it agrees with `completionRingAut σ`, it sends the image of $a \in \overline{\mathbb{Q}}$ in $C_A$ to the image of $\sigma(a)$, where $\sigma$ is read as a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$, and its inverse is $x \mapsto \sigma^{-1} \bullet x$.
--
--   **Relation to Mathlib.** Mathlib supplies the valuation of a valuation subring, its completion, the decomposition subgroup and `Subfield.topologicalClosure`; the predicate `DecompositionIsometric`, the subfield `ratClosure` and the group `IsometricAut` of valuation-preserving ring automorphisms fixing a base field pointwise are the project's own.
--
--   **Where it is used.** The homomorphism recorded here is what lets the decomposition group at a place of $\overline{\mathbb{Q}}$ act on the rings of rigid-analytic functions on the Drinfeld upper half-plane over $C_A$, and hence on the associated Mumford quotients, in the Čerednik–Drinfeld uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ValuationSubring_DecompositionIsometricAut.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.FieldTheory.Fixed
import Mathlib.Topology.Algebra.Field

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CerednikDrinfeld

namespace ValuationSubring

variable (A : ValuationSubring (AlgebraicClosure ℚ)) [Fact (A.DecompositionIsometric ℚ)]

theorem smul_completion_eq_self_of_mem_ratClosure (σ : A.decompositionSubgroup ℚ)
    {x : A.valuation.Completion} (hx : x ∈ ratClosure A) : σ • x = x := by

  have hc : IsClosed {y : A.valuation.Completion | σ • y = y} :=
    isClosed_eq (continuous_smul_completion σ) continuous_id
  have hle : ratClosure A ≤ FixedBy.subfield A.valuation.Completion σ :=
    Subfield.topologicalClosure_minimal ⊥ bot_le hc
  exact hle hx

def decompositionToIsometricAut :
    A.decompositionSubgroup ℚ →* Omega.IsometricAut ↥(ratClosure A) A.valuation.Completion where
  toFun σ :=
    { toRingEquiv := completionRingAut σ
      isometry := fun x => valuation_smul_completion σ x
      fix := fun a => smul_completion_eq_self_of_mem_ratClosure A σ a.2 }
  map_one' := by
    apply Omega.IsometricAut.ext
    ext x
    change (1 : ↥(A.decompositionSubgroup ℚ)) • x = x
    exact one_smul _ x
  map_mul' σ τ := by
    apply Omega.IsometricAut.ext
    ext x
    change (σ * τ) • x = σ • (τ • x)
    exact mul_smul σ τ x

@[simp] theorem decompositionToIsometricAut_toRingEquiv_apply (σ : A.decompositionSubgroup ℚ)
    (x : A.valuation.Completion) :
    (decompositionToIsometricAut A σ).toRingEquiv x = σ • x := rfl

theorem decompositionToIsometricAut_toRingEquiv (σ : A.decompositionSubgroup ℚ) :
    (decompositionToIsometricAut A σ).toRingEquiv = completionRingAut σ := rfl

theorem decompositionToIsometricAut_coe (σ : A.decompositionSubgroup ℚ) (a : AlgebraicClosure ℚ) :
    (decompositionToIsometricAut A σ).toRingEquiv ((a : AlgebraicClosure ℚ) : A.valuation.Completion) =
      (((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a : AlgebraicClosure ℚ) : A.valuation.Completion) :=
  smul_completion_coe σ a

theorem decompositionToIsometricAut_toRingEquiv_symm_apply (σ : A.decompositionSubgroup ℚ)
    (x : A.valuation.Completion) :
    (decompositionToIsometricAut A σ).toRingEquiv.symm x = σ⁻¹ • x := by
  rw [← Omega.IsometricAut.inv_toRingEquiv, ← map_inv]
  rfl

end ValuationSubring

end


