-- Prove2me | Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
-- name    : Formalism_GaussIdealIdentity_StatementLA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:24.088103+00:00
-- url     : https://prove2.me/theorems/f91bfc9f-0521-4196-80d7-79aef421eaf8
-- title:
--   Statement LA
-- statement:
--   Definitions and structural lemmas for Statement LA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussIdealIdentity/StatementLA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace Pointwise
noncomputable section
namespace Formalism.DV
def dualIn {𝕜 V : Type} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (S : Set 𝕜) (W M : Set V) : Set V :=
  {x | x ∈ W ∧ ∀ m ∈ M, ⟪x, m⟫_𝕜 ∈ S}
def ProjDual : Prop :=
  ∀ (𝕜 V : Type) [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (Z : Submodule 𝕜 V) [Z.HasOrthogonalProjection] (S : Set 𝕜) (M : Set V),
    let pr : V → V := fun v => Z.starProjection v
    dualIn S (Z : Set V) (pr '' M) = dualIn S Set.univ M ∩ (Z : Set V) ∧
    (dualIn S Set.univ M ⊆ M →
      dualIn S (Z : Set V) (pr '' M) ⊆ M ∩ (Z : Set V) ∧ M ∩ (Z : Set V) ⊆ pr '' M)
def GramDetIndex : Prop :=
  ∀ (V ι : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (Ld : Submodule ℤ V),
    let L : Submodule ℤ V := Submodule.span ℤ (Set.range b)
    (∀ x, x ∈ Ld ↔ ∀ y ∈ L, ∃ z : ℤ, ⟪x, y⟫_ℝ = z) → Ld ≤ L →
      (Matrix.of fun i j => ⟪b i, b j⟫_ℝ).det *
        ((Ld.toAddSubgroup.relIndex L.toAddSubgroup : ℕ) : ℝ) = 1
def GramDet : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (d : ℕ) (e F : Fin d → V),
    Pairwise (fun σ τ => ⟪e σ, e τ⟫_ℂ = 0) → (∀ σ, e σ ≠ 0) →
    let Z : Submodule ℂ V := Submodule.span ℂ (Set.range e)
    letI : FiniteDimensional ℂ Z := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
    let pr : V → V := fun v => Z.starProjection v
    let G : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun a b => ⟪pr (F a), pr (F b)⟫_ℂ
    let C : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun σ a => ⟪e σ, F a⟫_ℂ
    G.det = ((‖C.det‖ ^ 2 / ∏ σ, ‖e σ‖ ^ 2 : ℝ) : ℂ)
def MasterIdentity : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (d : ℕ) (e F : Fin d → V),
    Pairwise (fun σ τ => ⟪e σ, e τ⟫_ℂ = 0) → (∀ σ, e σ ≠ 0) →
    let Z : Submodule ℂ V := Submodule.span ℂ (Set.range e)
    letI : FiniteDimensional ℂ Z := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
    let pr : V → V := fun v => Z.starProjection v
    let G : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun a b => ⟪pr (F a), pr (F b)⟫_ℂ
    let C : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun σ a => ⟪e σ, F a⟫_ℂ
    LinearIndependent ℂ (fun a => pr (F a)) →
    ∀ (A : ℂ) (B₀ : Matrix (Fin d) (Fin d) ℂ),
      let P : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i a => A⁻¹ * (B₀ * C.map (starRingEnd ℂ)) i a
      ‖P.det‖ ^ 2 / G.det.re = ‖A‖ ^ (-(2 * (d : ℤ))) * ‖B₀.det‖ ^ 2 * ∏ σ, ‖e σ‖ ^ 2
def ExponentForm : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ) (M Θ : Submodule O X), M.FG → Θ ≤ M → ∀ Vc : Submodule K X,
      let M₁ : Submodule O X := (ϖ ^ e) • M ⊔ Θ
      let MV : Submodule O X := M ⊓ Vc.restrictScalars O
      let ΘV : Submodule O X := Θ ⊓ Vc.restrictScalars O
      Module.length O (MV ⧸ ΘV.comap MV.subtype) ≤
        (e * Module.finrank K Vc : ℕ) + Module.length O (M₁ ⧸ Θ.comap M₁.subtype)
def gaussIdeal (σ O : Type) [CommRing O] [IsLocalRing O] : Ideal (MvPolynomial σ O) :=
  Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal O)
def GaussDVR : Prop :=
  ∀ (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O],
    (gaussIdeal σ O).IsPrime ∧
    ∀ [(gaussIdeal σ O).IsPrime],
      IsDiscreteValuationRing (Localization.AtPrime (gaussIdeal σ O)) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime (gaussIdeal σ O)) =
        Ideal.map (algebraMap O (Localization.AtPrime (gaussIdeal σ O))) (IsLocalRing.maximalIdeal O)
def GaussLength : Prop :=
  ∀ (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [(gaussIdeal σ O).IsPrime] (N : Type) [AddCommGroup N] [Module O N],
    Module.length (Localization.AtPrime (gaussIdeal σ O))
        (TensorProduct O (Localization.AtPrime (gaussIdeal σ O)) N) = Module.length O N
def GramDetLength : Prop :=
  ∀ (O K X ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K X) (B : LinearMap.BilinForm K X)
    (Ld : Submodule O X),
    let L : Submodule O X := Submodule.span O (Set.range b)
    (∀ x, x ∈ Ld ↔ ∀ y ∈ L, ∃ c : O, B x y = algebraMap O K c) → Ld ≤ L →
      ∃ g : O, algebraMap O K g * (Matrix.of fun i j => B (b i) (b j)).det = 1 ∧
        Module.length O (L ⧸ Ld.comap L.subtype) = IsDiscreteValuationRing.addVal O g
end Formalism.DV


