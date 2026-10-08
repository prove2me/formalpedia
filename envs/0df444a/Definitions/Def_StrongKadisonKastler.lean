-- Prove2me | Definitions.Def_StrongKadisonKastler
-- name    : StrongKadisonKastler
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:49.741998+00:00
-- url     : https://prove2.me/theorems/6cf42975-69bb-4105-9be8-d83170e11080
-- statement:
--   For a complex Hilbert space H (a complete complex inner product space in a fixed universe), unitBall(M) is the set of operators in a von Neumann algebra M of bounded operators on H whose norm is at most 1. The distance kkDistance(M,N) between two von Neumann algebras on H is the Hausdorff distance, in the operator norm, between their unit balls. For a unitary v, unitaryConj(v,x) is the conjugate v x v*, and Conjugates(v,M,N) says that the image of M under x ↦ v x v* is exactly N. NearConjugacy(M,N,ε) says that there is a unitary v with Conjugates(v,M,N) and ‖v−1‖<ε. UniversalStrongStability is a defined proposition, not an established theorem: for every real ε>0 there is a real δ>0 such that, for every complex Hilbert space H in the given universe and all von Neumann algebras M and N on H, if kkDistance(M,N)<δ then NearConjugacy(M,N,ε) holds. Thus a single tolerance δ, independent of H, must give a unitary conjugacy close to the identity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StrongKadisonKastler.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StrongKadisonKastler.lean; bytes 16..1272
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Theorem 1.1 of *Universal strong Kadison–Kastler stability*:
one tolerance gives small unitary conjugacies on every complex Hilbert space. -/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitBall (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ ‖x‖ ≤ 1}

noncomputable def kkDistance (M N : VonNeumannAlgebra H) : ℝ :=
  Metric.hausdorffDist (unitBall M) (unitBall N)

def unitaryConj (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) : H →L[ℂ] H :=
  (v : H →L[ℂ] H) * x * star (v : H →L[ℂ] H)

def Conjugates (v : unitary (H →L[ℂ] H)) (M N : VonNeumannAlgebra H) : Prop :=
  unitaryConj v '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H))

def NearConjugacy (M N : VonNeumannAlgebra H) (ε : ℝ) : Prop :=
  ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧ ‖(v : H →L[ℂ] H) - 1‖ < ε

def UniversalStrongStability : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ M N : VonNeumannAlgebra H,
        kkDistance M N < δ → NearConjugacy M N ε



end
end KadisonKastler
end OAI


