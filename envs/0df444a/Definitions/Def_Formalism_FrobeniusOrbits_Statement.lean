-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_Statement
-- name    : Formalism_FrobeniusOrbits_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:31.581203+00:00
-- url     : https://prove2.me/theorems/7ddfce5d-abcf-47fe-9e49-f7f3846e88d6
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/Statement.lean

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
def HostHyp (q d : ℕ) : Prop :=
  q.Prime ∧ d.Prime ∧ q % 8 = 3 ∧ d % 16 = 7 ∧ jacobiSym (-(d : ℤ)) q = 1
abbrev HGrp (e : ℕ) : Type :=
  (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)
abbrev G0 : Type := ℤˣ × ℤˣ
abbrev GG (e : ℕ) : Type := G0 × HGrp e
def hcl (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) : HGrp e := QuotientGroup.mk u
def sg (e : ℕ) : GG e := ((-1, 1), 1)
def c0 : G0 := (-1, -1)
def cc (e : ℕ) : GG e := (c0, 1)
def chD (e : ℕ) : GG e →* ℤˣ := (MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst G0 (HGrp e))
def chQ (e : ℕ) : GG e →* ℤˣ := (MonoidHom.fst ℤˣ ℤˣ).comp (MonoidHom.fst G0 (HGrp e))
def Psi (e : ℕ) : Subgroup (GG e) := (chD e).ker
section Fields
variable {L : Type*} [Field L] [Algebra ℚ L]
def F1 (ζ : L) : IntermediateField ℚ L := ℚ⟮ζ + ζ⁻¹⟯
def Kd (b : L) : IntermediateField ℚ L := ℚ⟮b⟯
def E0 (a b : L) : IntermediateField ℚ L := ℚ⟮a, b⟯
def hostE (ζ a b : L) : IntermediateField ℚ L := E0 a b ⊔ F1 ζ
theorem theta_mem (ζ a b : L) : ζ + ζ⁻¹ ∈ hostE ζ a b := (le_sup_right : F1 ζ ≤ E0 a b ⊔ F1 ζ) (mem_adjoin_simple_self ℚ _)
theorem a_mem (ζ a b : L) : a ∈ hostE ζ a b := (le_sup_left : E0 a b ≤ E0 a b ⊔ F1 ζ) (subset_adjoin ℚ _ (by simp))
theorem b_mem (ζ a b : L) : b ∈ hostE ζ a b := (le_sup_left : E0 a b ≤ E0 a b ⊔ F1 ζ) (subset_adjoin ℚ _ (by simp))
def thE (ζ a b : L) : hostE ζ a b := ⟨ζ + ζ⁻¹, theta_mem ζ a b⟩
def aE (ζ a b : L) : hostE ζ a b := ⟨a, a_mem ζ a b⟩
def bE (ζ a b : L) : hostE ζ a b := ⟨b, b_mem ζ a b⟩
abbrev hostF (ζ a b : L) : Subfield (hostE ζ a b) := maximalRealSubfield (hostE ζ a b)
open Classical in

def hPart (e : ℕ) (ζ a b : L) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : HGrp e :=
  if h : ∃ u : (ZMod (2 ^ (e + 2)))ˣ,
      ((σ (thE ζ a b) : hostE ζ a b) : L) =
        ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val
  then hcl e (Classical.choose h) else 1
def galE (e : ℕ) (ζ a b : L) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : GG e :=
  ((sgn σ (aE ζ a b), sgn σ (bE ζ a b)), hPart e ζ a b σ)
def cmType (ζ a b : L) (d : ℕ) : Set (hostE ζ a b →+* ℂ) :=
  {φ | φ (bE ζ a b) = Complex.I * (Real.sqrt d : ℂ)}
end Fields
def HostExample : Prop :=
  HostHyp 11 7 ∧ ∀ e : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ζ a b : L),
    IsLayer (e + 2) 11 7 ζ a b
def HostGroup : Prop :=
  ∀ e : ℕ,
    Nat.card (GG e) = 2 ^ (e + 2) ∧ (Psi e).index = 2 ∧ cc e ∉ Psi e ∧ sg e ∈ Psi e ∧
    orderOf (cc e) = 2 ∧
    IsCyclic (HGrp e) ∧ Nat.card (HGrp e) = 2 ^ e ∧ orderOf (hcl e (u5 (e + 2))) = 2 ^ e ∧
    ∃ ι : Multiplicative (ZMod (2 ^ e)) ≃* HGrp e,
      ι (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2))
def HostOrders : Prop :=
  ∀ e : ℕ,
    (∀ (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ), ((u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) →
      (orderOf (hcl e u) ≤ 2 ^ j ↔
        ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1))) ∧
    ∀ g : GG e, cc e ∈ Subgroup.zpowers g ↔ g = cc e
def HostRecip : Prop := ∀ q d : ℕ, HostHyp q d → jacobiSym (-(q : ℤ)) d = -1
def HostFixed : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer (e + 2) q d ζ a b),
    hostE ζ a b = ℚ⟮ζ + ζ⁻¹, a, b⟯ ∧
    ∀ x : L, x ∈ hostE ζ a b ↔
      ∀ τ : L ≃ₐ[ℚ] L, galMap h.1 a b τ = ((-1, 1, 1) : GalL (e + 2)) → τ x = x
def HostGalois : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    IsGalois ℚ (hostE ζ a b) ∧ Module.finrank ℚ (hostE ζ a b) = 2 ^ (e + 2) ∧
    (∀ σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
      galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ) ∧
    Function.Bijective (galE e ζ a b)
def HostGalSpec : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
    ((σ (aE ζ a b) : L) = ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) : L) * a) ∧
    ((σ (bE ζ a b) : L) = ((((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * b) ∧
    (∀ u : (ZMod (2 ^ (e + 2)))ˣ, (galE e ζ a b σ).2 = hcl e u ↔
      ((σ (thE ζ a b) : hostE ζ a b) : L) =
        ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val) ∧
    ∀ τ : L ≃ₐ[ℚ] L, (∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) →
      galE e ζ a b σ =
        (((galMap h.1 a b τ).2.1, (galMap h.1 a b τ).2.2), hcl e (galMap h.1 a b τ).1)
def HostConj : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    IsCMField (hostE ζ a b) ∧
    ∀ (φ : hostE ζ a b →+* ℂ) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
      (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galE e ζ a b σ = cc e
def HostReal : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    Module.finrank ℚ (hostF ζ a b) = 2 ^ (e + 1) ∧
    ∀ x : hostE ζ a b,
      (x ∈ hostF ζ a b ↔
        ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e → σ x = x) ∧
      (x ∈ hostF ζ a b ↔ (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯)
def TwoPowerCyclotomicLayerRealSubfieldCharacterization : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    IsCyclotomicExtension {2 ^ (e + 2)} ℚ ℚ⟮ζ⟯ ∧
    (∀ x : ℚ⟮ζ⟯, x ∈ maximalRealSubfield ℚ⟮ζ⟯ ↔ (x : L) ∈ F1 ζ) ∧
    Module.finrank ℚ (F1 ζ) = 2 ^ e ∧
    (∀ x ∈ F1 ζ, ∀ φ : L →+* ℂ, starRingEnd ℂ (φ x) = φ x) ∧
    ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
      (galE e ζ a b σ).2 = 1 ↔ ∀ x : hostE ζ a b, (x : L) ∈ F1 ζ → σ x = x
def HostMu : Prop :=
  ∀ (e q d : ℕ), HostHyp q d → q ≠ 3 →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    ∀ x : hostE ζ a b, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1
def HostFrob : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    (∃ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ P) ∧
    (∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ P ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        ∃ u : (ZMod (2 ^ (e + 2)))ˣ, (u : ZMod (2 ^ (e + 2))) = (p : ZMod _) ∧
          (galE e ζ a b σ).2 = hcl e u)) ∧
    ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ σ = 1
def HostInertia : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})],
      (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ (galE e ζ a b σ).1 = 1) ∧
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(q : ℤ)})],
      (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ (galE e ζ a b σ = 1 ∨ galE e ζ a b σ = sg e)) ∧
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(d : ℤ)})],
      (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔
        (galE e ζ a b σ = 1 ∨ galE e ζ a b σ = ((1, -1), 1)))
def HostUnramEF : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))), P.IsPrime → P ≠ ⊥ →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e →
    ¬ ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P
def HostDecomp : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (uq ud : (ZMod (2 ^ (e + 2)))ˣ), (uq : ZMod (2 ^ (e + 2))) = (q : ZMod _) →
    (ud : ZMod (2 ^ (e + 2))) = (d : ZMod _) →
  ∀ (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})],
      σ ∈ MulAction.stabilizer _ P ↔ galE e ζ a b σ ∈ Psi e) ∧
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(q : ℤ)})],
      σ ∈ MulAction.stabilizer _ P ↔
        ((galE e ζ a b σ).1.2 = 1 ∧ ∃ k : ℕ, (galE e ζ a b σ).2 = hcl e uq ^ k)) ∧
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(d : ℤ)})],
      σ ∈ MulAction.stabilizer _ P ↔
        ∃ k : ℕ, (galE e ζ a b σ).1.1 = (-1) ^ k ∧ (galE e ζ a b σ).2 = hcl e ud ^ k)
def HostDecompConj : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), galE e ζ a b σ = cc e →
  ∀ (p : ℕ), (p = 2 ∨ p = q ∨ (p = d ∧ 2 ≤ e)) →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    σ ∉ MulAction.stabilizer _ P
def HostEFGTwo : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (hostE ζ a b)) = 2 ^ e ∧
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 (hostE ζ a b)) = 2 ∧
    (primesOver (span {(2 : ℤ)}) (𝓞 (hostE ζ a b))).ncard = 2 ∧
    (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard = 1 ∧
    (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (hostF ζ a b)) = 2 ^ e ∧
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 (hostF ζ a b)) = 2
def HostSplitK : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    (∀ p : ℕ, p.Prime →
      ((primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 ↔
        (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(d : ℤ)) p = 1)))) ∧
    (primesOver (span {(d : ℤ)}) (𝓞 (Kd b))).ncard = 1 ∧
    (primesOver (span {(q : ℤ)}) (𝓞 (Kd b))).ncard = 2 ∧
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
    ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
      (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), IsArithFrobAt ℤ σ P →
      (galE e ζ a b σ ∈ Psi e ↔ (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2)
def HostCMType : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    (∀ φ : hostE ζ a b →+* ℂ,
      φ ∈ cmType ζ a b d ↔ (starRingEnd ℂ).comp φ ∉ cmType ζ a b d) ∧
    (cmType ζ a b d).ncard = 2 ^ (e + 1) ∧
    ∀ φ ∈ cmType ζ a b d, ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
      φ.comp (σ : hostE ζ a b →+* hostE ζ a b) ∈ cmType ζ a b d ↔ galE e ζ a b σ ∈ Psi e
end Formalism.FrobeniusOrbits


