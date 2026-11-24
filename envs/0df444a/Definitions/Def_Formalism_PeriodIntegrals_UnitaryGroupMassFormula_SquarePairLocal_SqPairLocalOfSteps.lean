-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:49.969921+00:00
-- url     : https://prove2.me/theorems/776626b5-c44f-4351-b7e0-2352c0795b43
-- title:
--   Sq Pair Local Of Steps
-- statement:
--   Definitions and structural lemmas for Sq Pair Local Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
def cj (E : Type) [Field E] [NumberField E] [StarRing E] : 𝓞 E →+* 𝓞 E :=
  RingOfIntegers.mapRingHom (starRingEnd E)
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def Pres {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (e : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ y ∈ L, e *ᵥ y ∈ L
def SmallAt {N : ℕ} (Q : Ideal (𝓞 E)) (c : 𝓞 E) (L : Submodule (𝓞 E) (Fin N → E))
    (M : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ y ∈ L, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ m ∈ L, s • (M *ᵥ y) = c • m
def Good {N : ℕ} (Q : Ideal (𝓞 E)) (c : 𝓞 E) (L' L'' : Submodule (𝓞 E) (Fin N → E))
    (e : Matrix (Fin N) (Fin N) E) : Prop :=
  SmallAt Q c L' (e * e - e) ∧ SmallAt Q c L'' (e * e - e) ∧
    SmallAt Q c L' (e + eᴴ - 1) ∧ SmallAt Q c L'' (e + eᴴ - 1)
def IntAt (Q : Ideal (𝓞 E)) (x : E) : Prop :=
  ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, (s : E) * x = (w : E)
def DivAt (Q : Ideal (𝓞 E)) (c : 𝓞 E) (x : E) : Prop :=
  ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, (s : E) * x = (c : E) * (w : E)
def LocGlob : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (X : Submodule (𝓞 E) W) (x : W) (p : ℕ), p.Prime →
    (∀ Q : Ideal (𝓞 E), Q.IsMaximal → (p : 𝓞 E) ∈ Q → ∃ s : 𝓞 E, s ∉ Q ∧ s • x ∈ X) →
    ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ (s : 𝓞 E) • x ∈ X
def IntMul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L' L'' : Submodule (𝓞 E) (Fin N → E)), IsSDG E N L' → IsSDG E N L'' → ∀ n : 𝓞 E, n ≠ 0 →
    ∃ c : ℕ, c ≠ 0 ∧ ∀ y, (y ∈ L' ∨ y ∈ L'') → ∃ m, m ∈ L' ∧ m ∈ L'' ∧ (c : 𝓞 E) • y = n • m
def PowLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Q : Ideal (𝓞 E)), Q.IsMaximal → ∀ c : 𝓞 E, c ≠ 0 →
    ∃ K : ℕ, ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w
def Glued : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ p : ℕ, p.Prime → ∀ a : ℕ, ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
        ∀ Q : Ideal (𝓞 E), Q.IsMaximal → (p : 𝓞 E) ∈ Q → Good Q ((p : 𝓞 E) ^ a) L' L'' e
def OnePlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → ∀ c : 𝓞 E, c ≠ 0 →
        ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
          Good Q c L' L'' e ∧ Good (Q.comap (cj E)) c L' L'' e
def Glue : Prop := OnePlace → Glued
def SplitPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) ≠ Q → ∀ c : 𝓞 E, c ≠ 0 →
        ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
          Good Q c L' L'' e ∧ Good (Q.comap (cj E)) c L' L'' e
def InertPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) = Q → ∀ c : 𝓞 E, c ≠ 0 →
        ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧ Good Q c L' L'' e
structure StModel (E : Type) [Field E] [NumberField E] [StarRing E] (Q : Ideal (𝓞 E)) where
  R : Type
  [cr : CommRing R]
  σ : R ≃+* R
  σσ : ∀ x, σ (σ x) = x
  R₀ : Subring R
  mem₀ : ∀ x, x ∈ R₀ ↔ σ x = x
  [dom : IsDomain R₀]
  [dvr : IsDiscreteValuationRing R₀]
  [hens : HenselianLocalRing R₀]
  [fin : Finite (IsLocalRing.ResidueField R₀)]
  unram : ∃ θ : R, IsUnit (θ - σ θ)
  j : 𝓞 E →+* R
  j_cj : ∀ x : 𝓞 E, j (cj E x) = σ (j x)
  ϖ : 𝓞 E
  ϖ_cj : cj E ϖ = ϖ
  ϖ_Q : ϖ ∈ Q
  ϖ_mem : j ϖ ∈ R₀
  ϖ_irr : Irreducible (⟨j ϖ, ϖ_mem⟩ : R₀)
  unit_of : ∀ s : 𝓞 E, s ∉ Q → IsUnit (j s)
  dense : ∀ (x : R) (K : ℕ), ∃ y : 𝓞 E, ∃ z : R, x - j y = j ϖ ^ K * z
  detect : ∀ (x : 𝓞 E) (K : ℕ), (∃ z : R, j x = j ϖ ^ K * z) →
    ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = ϖ ^ K * w
def ModelEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) = Q → Nonempty (StModel E Q)
def Dict : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L : Submodule (𝓞 E) (Fin N → E)), IsSDG E N L →
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) = Q →
        ∃ G : Matrix (Fin N) (Fin N) E, Gᴴ * G = 1 ∧ G * Gᴴ = 1 ∧
          ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i)
def LocMat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (Q : Ideal (𝓞 E)), Q.IsMaximal →
    ∀ M : StModel E Q, LocCartanPair →
      ∀ (N : ℕ), Even N → ∀ u : Matrix (Fin N) (Fin N) E, uᴴ * u = 1 → u * uᴴ = 1 → ∀ K : ℕ,
        ∃ e₁ : Matrix (Fin N) (Fin N) E, (∀ i j, IntAt Q (e₁ i j)) ∧ (∀ i j, IntAt Q ((uᴴ * e₁ * u) i j)) ∧
          (∀ i j, DivAt Q (M.ϖ ^ K) ((e₁ * e₁ - e₁) i j)) ∧
          (∀ i j, DivAt Q (M.ϖ ^ K) ((uᴴ * (e₁ * e₁ - e₁) * u) i j)) ∧
          (∀ i j, DivAt Q (M.ϖ ^ K) ((e₁ + e₁ᴴ - 1) i j)) ∧
          (∀ i j, DivAt Q (M.ϖ ^ K) ((uᴴ * (e₁ + e₁ᴴ - 1) * u) i j))
def InertAsm : Prop := LocCartanPair → ModelEx → Dict → LocMat → PowLoc → InertPlace
section Alg
variable {N : ℕ}
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
end Alg
end PI.SqPairLocal


