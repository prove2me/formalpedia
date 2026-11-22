-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_Statement
-- name    : Formalism_HarderNarasimhan_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:02.817807+00:00
-- url     : https://prove2.me/theorems/aa6d4010-c0ae-4f3c-8cc8-f535d71bbb49
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/Statement.lean

import Mathlib
import Definitions.Def_Formalism_LatticeSlopes_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
namespace Formalism.HN
section Defs
variable {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [Module R V]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
def zl (ρ : V →+ E) (N : Submodule R V) : Submodule ℤ E := (N.toAddSubgroup.map ρ).toIntSubmodule
def IsLat (ρ : V →+ E) (L : Submodule R V) : Prop :=
  Set.InjOn ρ (L : Set V) ∧ DiscreteTopology (zl ρ L)
def deg (ρ : V →+ E) (N : Submodule R V) : ℝ := Formalism.F.deg (zl ρ N)
def rk (ρ : V →+ E) (N : Submodule R V) : ℕ := Formalism.F.rk (zl ρ N)
def slope (ρ : V →+ E) (N : Submodule R V) : ℝ := Formalism.F.slope (zl ρ N)
def IsSat (ρ : V →+ E) (L N : Submodule R V) : Prop :=
  N ≤ L ∧ Formalism.F.IsSaturated (zl ρ L) (zl ρ N)
def muMax (ρ : V →+ E) (L : Submodule R V) : ℝ :=
  sSup {t | ∃ N : Submodule R V, N ≤ L ∧ N ≠ ⊥ ∧ slope ρ N = t}
def muMin (ρ : V →+ E) (L : Submodule R V) : ℝ :=
  sInf {t | ∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ L ∧
    Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N)) = t}
def hnStep (ρ : V →+ E) (L : Submodule R V) (θ : ℝ) : Submodule R V :=
  sSup {N | N ≤ L ∧ N ≠ ⊥ ∧ θ ≤ muMin ρ N}
def slopeList (ρ : V →+ E) (L : Submodule R V) : Fin (rk ρ L) → ℝ :=
  fun j => sSup {θ | (j : ℕ) < rk ρ (hnStep ρ L θ)}
def hnPoly (ρ : V →+ E) (L : Submodule R V) (k : ℕ) : ℝ :=
  ∑ j : Fin (rk ρ L), if (j : ℕ) < k then slopeList ρ L j else 0
end Defs
def DegSupermod : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L A B : Submodule R V),
    IsLat ρ L → A ≤ L → B ≤ L →
    rk ρ (A ⊔ B) + rk ρ (A ⊓ B) = rk ρ A + rk ρ B ∧
    deg ρ A + deg ρ B ≤ deg ρ (A ⊔ B) + deg ρ (A ⊓ B)
def MuChar : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L → L ≠ ⊥ →
    (∀ θ : ℝ, muMax ρ L ≤ θ ↔ ∀ N : Submodule R V, N ≤ L → deg ρ N ≤ θ * rk ρ N) ∧
    (∀ θ : ℝ, θ ≤ muMin ρ L ↔
      ∀ N : Submodule R V, N ≤ L → θ * ((rk ρ L : ℝ) - rk ρ N) ≤ deg ρ L - deg ρ N) ∧
    (∃ N : Submodule R V, IsSat ρ L N ∧ N ≠ ⊥ ∧ slope ρ N = muMax ρ L) ∧
    muMin ρ L ≤ slope ρ L ∧ slope ρ L ≤ muMax ρ L
def HNStep : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L → ∀ θ : ℝ,
    IsSat ρ L (hnStep ρ L θ) ∧
    (hnStep ρ L θ ≠ ⊥ → θ ≤ muMin ρ (hnStep ρ L θ)) ∧
    (∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N → N ≤ hnStep ρ L θ) ∧
    (∀ N : Submodule R V, hnStep ρ L θ < N → N ≤ L →
      deg ρ N - deg ρ (hnStep ρ L θ) < θ * ((rk ρ N : ℝ) - rk ρ (hnStep ρ L θ)))
def HNSlopes : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L →
    Antitone (slopeList ρ L) ∧
    (∀ θ : ℝ, (Finset.univ.filter (fun j => θ ≤ slopeList ρ L j)).card = rk ρ (hnStep ρ L θ)) ∧
    ∑ j, slopeList ρ L j = deg ρ L ∧
    (∀ N : Submodule R V, N ≤ L → deg ρ N ≤ hnPoly ρ L (rk ρ N)) ∧
    (∀ θ : ℝ, deg ρ (hnStep ρ L θ) = hnPoly ρ L (rk ρ (hnStep ρ L θ)))
def HNExtreme : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L → L ≠ ⊥ →
    (∀ j, muMin ρ L ≤ slopeList ρ L j ∧ slopeList ρ L j ≤ muMax ρ L) ∧
    (∃ j, slopeList ρ L j = muMax ρ L) ∧ (∃ j, slopeList ρ L j = muMin ρ L)
def SlopeIneq : Prop :=
  ∀ (R V W E F : Type*) [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : V →+ E) (ρ' : W →+ F) (L : Submodule R V) (M : Submodule R W), IsLat ρ L → IsLat ρ' M →
    ∀ (φ : L →ₗ[R] M) (C : ℝ), 0 < C → (∀ x : L, ‖ρ' (φ x : W)‖ ≤ C * ‖ρ (x : V)‖) →
    (φ ≠ 0 → muMin ρ L - Real.log C ≤ muMin ρ' ((LinearMap.range φ).map M.subtype) ∧
      muMin ρ L ≤ muMax ρ' M + Real.log C) ∧
    (Function.Injective φ → L ≠ ⊥ → muMax ρ L ≤ muMax ρ' M + Real.log C)
def HNSum : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E),
    (∀ (L : Submodule R V) (ι : Type*) (s : Finset ι) (A : ι → Submodule R V) (θ : ℝ),
      IsLat ρ L → s.Nonempty → (∀ i ∈ s, A i ≤ L ∧ A i ≠ ⊥ ∧ θ ≤ muMin ρ (A i)) →
      θ ≤ muMin ρ (⨆ i ∈ s, A i)) ∧
    (∀ A B : Submodule R V, IsLat ρ A → IsLat ρ B →
      (∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) →
      IsLat ρ (A ⊔ B) ∧ deg ρ (A ⊔ B) = deg ρ A + deg ρ B ∧
      (A ≠ ⊥ → B ≠ ⊥ → muMax ρ (A ⊔ B) = max (muMax ρ A) (muMax ρ B) ∧
        muMin ρ (A ⊔ B) = min (muMin ρ A) (muMin ρ B)))
def dualZ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : Submodule ℤ E) :
    Submodule ℤ E :=
  (Submodule.span ℝ (L : Set E)).restrictScalars ℤ ⊓
    ⨅ x ∈ L, ((Int.castAddHom ℝ).range.toIntSubmodule).comap
      ((innerSL ℝ x : E →L[ℝ] ℝ).toLinearMap.restrictScalars ℤ)
def Duality : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L →
    DiscreteTopology (dualZ L) ∧ Formalism.F.rk (dualZ L) = Formalism.F.rk L ∧
    Formalism.F.deg (dualZ L) = - Formalism.F.deg L ∧ dualZ (dualZ L) = L ∧
    (L ≠ ⊥ → muMax (AddMonoidHom.id E) (dualZ L) = - muMin (AddMonoidHom.id E) L ∧
      muMin (AddMonoidHom.id E) (dualZ L) = - muMax (AddMonoidHom.id E) L)
def Example : Prop :=
  let e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  let e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  let ρ : EuclideanSpace ℝ (Fin 2) →+ EuclideanSpace ℝ (Fin 2) := AddMonoidHom.id _
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) := Submodule.span ℤ {e₀, (2 : ℝ) • e₁}
  IsLat ρ L ∧ rk ρ L = 2 ∧
    (∀ j : Fin (rk ρ L), slopeList ρ L j = if (j : ℕ) = 0 then 0 else - Real.log 2) ∧
    hnStep ρ L 0 = Submodule.span ℤ {e₀} ∧ hnStep ρ L (- Real.log 2) = L ∧
    muMax ρ L = 0 ∧ muMin ρ L = - Real.log 2
def ShiftInvariance : Prop :=
  ∀ (R V E E₂ : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E₂]
    [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂] (ρ : V →+ E) (ρ₂ : V →+ E₂)
    (L : Submodule R V) (c : ℝ), IsLat ρ L → IsLat ρ₂ L →
    (∀ N : Submodule R V, N ≤ L → rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N + c * rk ρ N) →
    (∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N) ∧
    (L ≠ ⊥ → muMax ρ₂ L = muMax ρ L + c ∧ muMin ρ₂ L = muMin ρ L + c) ∧
    (∀ θ : ℝ, hnStep ρ₂ L (θ + c) = hnStep ρ L θ) ∧
    (∀ k : ℕ, hnPoly ρ₂ L k = hnPoly ρ L k + c * (min k (rk ρ L) : ℕ))
def piReal {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    (ρ : ∀ i, V i →+ E i) : (∀ i, V i) →+ PiLp 2 E :=
  (WithLp.linearEquiv 2 ℝ (∀ i, E i)).symm.toLinearMap.toAddMonoidHom.comp
    (AddMonoidHom.pi fun i => (ρ i).comp (Pi.evalAddMonoidHom V i))
def PiSum : Prop :=
  ∀ (R ι : Type*) [Ring R] [Fintype ι] [DecidableEq ι] (V E : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (ρ : ∀ i, V i →+ E i) (L : ∀ i, Submodule R (V i)), (∀ i, IsLat (ρ i) (L i)) →
    IsLat (piReal ρ) (Submodule.pi Set.univ L) ∧
    rk (piReal ρ) (Submodule.pi Set.univ L) = ∑ i, rk (ρ i) (L i) ∧
    deg (piReal ρ) (Submodule.pi Set.univ L) = ∑ i, deg (ρ i) (L i) ∧
    ((∃ i, L i ≠ ⊥) → ∀ θ : ℝ,
      (muMax (piReal ρ) (Submodule.pi Set.univ L) ≤ θ ↔ ∀ i, L i ≠ ⊥ → muMax (ρ i) (L i) ≤ θ) ∧
      (θ ≤ muMin (piReal ρ) (Submodule.pi Set.univ L) ↔ ∀ i, L i ≠ ⊥ → θ ≤ muMin (ρ i) (L i)))
end Formalism.HN


