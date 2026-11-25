-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_CcKPrimitive
-- name    : Development_AbelianVarietyTheory_Definitions_GlobalTwisting_CcKPrimitive
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:10.571118+00:00
-- url     : https://prove2.me/theorems/e8580927-6eff-50f4-98e8-1a1aad794fff
-- title:
--   Cc KPrimitive
-- statement:
--   Definitions and structural lemmas for Cc KPrimitive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/CcKPrimitive.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
namespace GlobalTheory.GH
noncomputable def cmConj (E : Type) [Field E] [NumberField E] [IsCMField E] : E ≃ₐ[ℚ] E :=
  (IsCMField.complexConj E).restrictScalars ℚ
structure GField (e : ℕ) where
  q : ℕ
  d : ℕ

  hyp : Formalism.FrobeniusOrbits.HostHyp q d
  q_ne_three : q ≠ 3
  two_le_e : 2 ≤ e
  E : Type
  [instField : Field E]
  [instNF : NumberField E]
  [instCM : IsCMField E]
  [instAb : IsAbelianGalois ℚ E]

  aE : E

  bE : E
  aE_sq : aE ^ 2 = -(q : E)
  bE_sq : bE ^ 2 = -(d : E)

  N : ℕ
  N_pos : 0 < N
  cyc : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)
  dvd_N : 2 ^ (e + 2) * q * d ∣ N

  N_split : ∀ p : ℕ, p.Prime → p ∣ N → p ≠ 2 → p ≠ d → jacobiSym (-(d : ℤ)) p = 1

  inertia_qd : ∀ p : ℕ, p = q ∨ p = d → ∀ P : Ideal (𝓞 E), P.IsPrime → ((p : ℕ) : 𝓞 E) ∈ P →
    ∀ σ τ : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, σ • x - x ∈ P) → (∀ x : 𝓞 E, τ • x - x ∈ P) → σ = 1 ∨ τ = 1 ∨ σ = τ

  thE : E
  thE_spec : ∀ φ : E →+* ℂ, ∃ ζ : ℂ, IsPrimitiveRoot ζ (2 ^ (e + 2)) ∧ φ thE = ζ + ζ⁻¹

  hp : (E ≃ₐ[ℚ] E) →* Formalism.FrobeniusOrbits.HGrp e
  hp_spec : ∀ (φ : E →+* ℂ) (ζ : ℂ), IsPrimitiveRoot ζ (2 ^ (e + 2)) → φ thE = ζ + ζ⁻¹ →
    ∀ (σ : E ≃ₐ[ℚ] E) (u : (ZMod (2 ^ (e + 2)))ˣ), hp σ = Formalism.FrobeniusOrbits.hcl e u ↔
      φ (σ thE) = ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val
attribute [instance] GField.instField GField.instNF GField.instCM GField.instAb
structure GHost (e : ℕ) extends GField e where

  big : ℕ
  qd_big : big < q ∧ big < d
  splitBound : ℕ
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ splitBound → jacobiSym (-(d : ℤ)) p = 1
  φ₀ : E →+* ℂ
  φ₀_mem : φ₀ bE = Complex.I * (Real.sqrt d : ℂ)
  𝔟 : Ideal (𝓞 E)
  𝔟_spec : differentIdeal (𝓞 ℚ⟮bE⟯) (𝓞 E) = 𝔟 * (cmConj E • 𝔟) ∧ 𝔟 ⊔ cmConj E • 𝔟 = ⊤
  levelPrimes : Finset ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  g_level : ∀ i, g i ∈ levelPrimes
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_level : pde ∈ levelPrimes ∧ pde' ∈ levelPrimes
  pde_mod : pde % 15 = 1 ∧ pde' % 15 = 1
  pde_ne_g : ∀ i, pde ≠ g i ∧ pde' ≠ g i
  ccK : Ideal (𝓞 ℚ⟮bE⟯)
  ccK_ne_bot : ccK ≠ ⊥
  ccK_primitive : ∀ m : ℕ, 1 < m → ¬ ccK ≤ Ideal.span {(m : 𝓞 ℚ⟮bE⟯)}
  ccK_split : ∀ P : Ideal (𝓞 ℚ⟮bE⟯), P.IsPrime → ccK ≤ P →
    (Ideal.absNorm P).Prime ∧ jacobiSym (-(d : ℤ)) (Ideal.absNorm P) = 1
  ccK_coprime : Nat.Coprime (Ideal.absNorm ccK) (30 * N) ∧ ∀ p ∈ levelPrimes, Nat.Coprime (Ideal.absNorm ccK) p
namespace GHost
variable {e : ℕ} (H : GHost e)
abbrev F : Subfield H.E := maximalRealSubfield H.E
abbrev K : IntermediateField ℚ H.E := ℚ⟮H.bE⟯
abbrev GG : Type := H.E ≃ₐ[ℚ] H.E
noncomputable def conj : H.E ≃ₐ[ℚ] H.E := cmConj H.E
@[instance_reducible] noncomputable def cmStar : StarRing H.E := NumberField.IsCMField.starRing H.E
def Psi : Subgroup H.GG := MulAction.stabilizer H.GG H.bE
def cmType : Set (H.E →+* ℂ) := {φ | φ H.bE = Complex.I * (Real.sqrt H.d : ℂ)}
noncomputable def emb (σ : H.GG) : H.E →+* ℂ := H.φ₀.comp (σ : H.E →+* H.E)
noncomputable def f : ℕ := Module.finrank ℚ H.F
def n (_H : GHost e) : ℕ := 2 ^ e
def Ex : Subgroup H.GG := MulAction.stabilizer H.GG H.aE ⊓ MulAction.stabilizer H.GG H.bE ⊓ H.hp.ker
noncomputable def w : ℕ := NumberField.Units.torsionOrder H.E
noncomputable def rdE : ℝ := |(discr H.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ H.E : ℝ))
noncomputable def v : ℝ := H.rdE / 2
noncomputable def ka : ℝ := Real.pi / H.v
def sqrtMinusD : H.E := H.bE
noncomputable def xi0 : H.E := -1 / ((Ideal.absNorm H.ccK : H.E) * H.sqrtMinusD)
noncomputable def ccE : Ideal (𝓞 H.E) := Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) H.ccK
noncomputable def AA0 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  ((H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E))⁻¹
noncomputable def AA : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  (H.ccE : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) * H.AA0
noncomputable def AAbar : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  ((H.conj • H.ccE : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) *
    ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹
noncomputable def ddE : Ideal (𝓞 H.E) := differentIdeal ℤ (𝓞 H.E)
end GHost
end GlobalTheory.GH


