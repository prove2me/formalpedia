-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:13:56.248208+00:00
-- url     : https://prove2.me/theorems/d6a30b9e-4955-402e-a75e-949597a9eb20
-- title:
--   NZType F
-- statement:
--   Definitions and structural lemmas for NZType F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
attribute [local instance] Classical.propDecidable
section Eval
variable {K : Type} [Field K]
def evS {Γ : Type} [Finite Γ] (ψ : Γ → K) (x : MonoidAlgebra K Γ) : K :=
  letI := Fintype.ofFinite Γ
  ∑ g, x.coeff g * ψ g
variable {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
variable {L : I → Type} [∀ i, Fintype (L i)] (E : ∀ i, L i → MonoidAlgebra K (G i)) (S : (∀ i, L i) → Prop)
end Eval
section Triv
variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]
def eT : MonoidAlgebra K Γ := MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun _ => ((Nat.card Γ : K))⁻¹
variable {K Γ}
end Triv
section Family
variable (K : Type) [Field K] (Γ : Type) {Λ : Type} [Group Γ] [Finite Γ] (fA fB : Λ)
def esZ (f : Λ) : MonoidAlgebra K Γ := if f = fA then 1 - eT K Γ else if f = fB then eT K Γ else 0
def cfQ (f : Λ) (h : Γ) : ℚ :=
  if f = fA then (if (1 : Γ) = h then 1 else 0) - ((Nat.card Γ : ℚ))⁻¹
  else if f = fB then ((Nat.card Γ : ℚ))⁻¹ else 0
variable {K Γ fA fB} [CharZero K] (hAB : fA ≠ fB)
end Family
end Formalism.BasicNotions.Examples₂.NZ


