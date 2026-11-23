-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:31.693888+00:00
-- url     : https://prove2.me/theorems/45b57111-c152-4e56-b0dd-c9d890041a72
-- title:
--   Sha Fam Mono
-- statement:
--   Definitions and structural lemmas for Sha Fam Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_V_ThmBab_a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base
namespace UpperTheory.V.Chr
section Len
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O]
def Psi (e : ℕ) (ψ : G k Ω →* Oˣ) : G k Ω →* Oˣ := chiO k Ω l O ^ (e : ℤ) * ψ
abbrev rho (e : ℕ) (ψ : G k Ω →* Oˣ) : Representation O (G k Ω) (QO l O) :=
  twist₂ l (ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)))
def VS (n e : ℕ) (ψ : G k Ω →* Oˣ) : ℕ∞ := Module.length O (ShaU (rho l e ψ) n ⊤)
def V (e : ℕ) (ψ : G k Ω →* Oˣ) : ℕ∞ := VS l l e ψ
def V' (N e : ℕ) (ψ : G k Ω →* Oˣ) : ℕ∞ := VS l (l * N) e ψ
def h0 (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)) : ℕ∞ := Module.length O (H0U (rho l e ψ) U)
def eigL (e : ℕ) (U : Subgroup (G k Ω)) [U.Normal] (ψ : G k Ω →* Oˣ) : ℕ∞ :=
  Module.length O (shaEig (twist₂ l (chiO k Ω l O ^ (-(e : ℤ)))) l U ⊤ (ψ.comp (⊤ : Subgroup (G k Ω)).subtype))
variable (O) in

def nrm (a : ℕ∞) : ℝ := (a.toNat : ℝ) / ((eO l O).toNat : ℝ)
variable (O) in

def SumLe (f : ℕ → ℕ∞) (t : ℕ) (B : ℝ) : Prop :=
  (∀ e : ℕ, 0 < e → e < t → f e ≠ ⊤) ∧ ∑ e ∈ Finset.Ico 1 t, nrm l O (f e) ≤ B
abbrev resChar (Ω : Type) {E : Type} [Field Ω] [Algebra k Ω] [Field E] [Algebra k E] [Algebra E Ω] [IsScalarTower k E Ω] [Normal k E]
    (ψ : (E ≃ₐ[k] E) →* Oˣ) : G k Ω →* Oˣ := ψ.comp (AlgEquiv.restrictNormalHom E)
end Len
section Dir
variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
include k in
theorem card_roots (N : ℕ) [NeZero N] : Nat.card (rootsOfUnity N Ω) = N := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N
def cls (N : ℕ) [NeZero N] : G k Ω →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Ω (card_roots k Ω N)).comp (MulSemiringAction.toRingAut (G k Ω) Ω)
def dirG {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) : G k Ω →* Oˣ :=
  χ.toUnitHom.comp (cls k Ω N)
def levH {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) : Subgroup (G k Ω) := H.comap (cls k Ω N)
instance {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) : (levH k Ω H).Normal := Subgroup.Normal.comap inferInstance _
end Dir
section OverQ
variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
instance (A : AbF) : NeZero A.m := ⟨A.pos.ne'⟩
def abU (A : AbF) : Subgroup (G ℚ Ω) := levH ℚ Ω A.H
def HasLevel (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) : Prop :=
  ∃ (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ), IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (u : (ZMod N)ˣ), τ ζ = ζ ^ (u : ZMod N).val →
      ((∀ x : E, τ (j x) = j x) ↔ u ∈ H)
def evenSet (O : Type) [CommRing O] {N : ℕ} (H : Subgroup (ZMod N)ˣ) (e : ℕ) : Set (DirichletCharacter O N) :=
  {χ | H ≤ χ.toUnitHom.ker ∧ χ (-1) = (-1) ^ e}
def loss (l N n e : ℕ) : ℕ := (n + n ^ 2) * LDataCardLeFinrank.nuBound l N e + N.primeFactors.card * (n * n.factorization l)
end OverQ
example (N : ℕ) [NeZero N] : HasLevel ℚ N ⊤ := by
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  exact ⟨Algebra.ofId _ _, _, IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ), fun τ _ _ =>
    ⟨fun _ => trivial, fun _ x => τ.commutes x⟩⟩
example : (1 : DirichletCharacter ℤ 5) ∈ evenSet ℤ (⊤ : Subgroup (ZMod 5)ˣ) 2 :=
  ⟨fun u _ => by ext; simp, by rw [MulChar.one_apply (by simp)]; norm_num⟩
end UpperTheory.V.Chr
end


