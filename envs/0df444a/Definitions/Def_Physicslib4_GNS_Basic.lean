-- Prove2me | Definitions.Def_Physicslib4_GNS_Basic
-- name    : Physicslib4_GNS_Basic
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T21:06:18.54345+00:00
-- url     : https://prove2.me/theorems/e0edbb34-bc7c-4994-99d8-6c8ab471c2db
-- title:
--   GNS basic notions: states and cyclic vectors
-- statement:
--   A **state** on a unital C\*-algebra $A$ is a continuous linear functional $\omega:A\to\mathbb{C}$ that is positive ($\omega(a^*a)\ge 0$) and normalized ($\|\omega\|=1$). It is **faithful** when $\omega(a^*a)>0$ for every nonzero $a$. A vector $\Omega$ of a complex Hilbert space $H$ is **cyclic** for a representation $\pi:A\to\mathcal{B}(H)$ when $\{\pi(a)\Omega:a\in A\}$ is dense in $H$. These are the basic notions of the GNS construction (blueprint §10.1, `def:state`, `def:cyclic-vector`).
-- source:
--   https://github.com/physicslib/physicslib4/blob/main/Physicslib4/GNS/Basic.lean (def:state, def:cyclic-vector)

import Mathlib

namespace Physicslib4
namespace GNS

open scoped ComplexOrder

variable (A : Type*) [CStarAlgebra A]

/-- A state on a unital C*-algebra A: a positive, normalised continuous linear functional. -/
structure State extends A →L[ℂ] ℂ where
  isPositive : ∀ a : A, 0 ≤ toContinuousLinearMap (star a * a)
  isNormalized : ‖toContinuousLinearMap‖ = 1

namespace State

variable {A}

noncomputable instance : FunLike (State A) A ℂ where
  coe ω := ω.toContinuousLinearMap
  coe_injective := by
    intro ω₁ ω₂ h
    cases ω₁
    cases ω₂
    simp only [mk.injEq]
    exact DFunLike.coe_injective h

/-- A faithful state: ω(a* a) > 0 for every nonzero a. -/
def IsFaithful (ω : State A) : Prop :=
  ∀ a : A, a ≠ 0 → 0 < ω (star a * a)

end State

variable {A}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A cyclic vector Ω for a representation π: the vectors π(a)Ω are dense in H. -/
def IsCyclicVector (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H) : Prop :=
  Dense (Set.range fun a : A => π a Ω)

end GNS
end Physicslib4


