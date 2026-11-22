-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:10.437128+00:00
-- url     : https://prove2.me/theorems/ce20a687-0069-4c3d-9a3a-f03112ea2ef0
-- title:
--   Reduction Quotient
-- statement:
--   Definitions and structural lemmas for Reduction Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/ReductionQuotient.lean

import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Module Polynomial
open scoped ComplexOrder
def ReductionQuotient : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (X Θ N₀ T : Submodule O V), N₀ ≤ Θ → T ≤ Θ → T ≤ X →
    let NK : Submodule O V := (Submodule.span K (N₀ : Set V)).restrictScalars O
    let M₁ : Submodule O V := (X ⊓ NK) ⊔ N₀
    Module.length O (↥(X ⊔ Θ) ⧸ Θ.comap (X ⊔ Θ).subtype) ≤
      Module.length O (↥M₁ ⧸ N₀.comap M₁.subtype) +
        Module.length O (↥X ⧸ ((X ⊓ NK) ⊔ T).comap X.subtype)
def LevelsJoint : Prop :=
  ∀ (O V W : Type) [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
    (N' M₁ N₁ Z Zm : Submodule O V) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W),
    M₁ ≤ N' → N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    let N₀ : Submodule O V := N₁ ⊔ Z
    Module.length O (↥M₁ ⧸ N₀.comap M₁.subtype) ≤
      Module.length O (↥AA' ⧸ AA.comap AA'.subtype) +
        Module.length O (↥AA ⧸ N₁'.comap AA.subtype) +
          Module.length O (↥Zm ⧸ Z.comap Zm.subtype)
def ZMinusIndex : Prop :=
  ∀ (O K U : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U]
    [FiniteDimensional K U] (ϖ : O), Irreducible ϖ → ∀ (crude : ℕ) (Zs Z : Submodule O U),
      Formalism.LatticeIndexTer.IsLat O K U Zs → Formalism.LatticeIndexTer.IsLat O K U Z →
      Formalism.LatticeIndexTer.idx O U
                (Zs.map ((((algebraMap O K ϖ) ^ (-(crude : ℤ))) • LinearMap.id : U →ₗ[K] U).restrictScalars O))
                Z =
        (crude : ℤ) * (finrank K U : ℤ) + Formalism.LatticeIndexTer.idx O U Zs Z
def QuotientLength : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (c : V →ₗ[K] (Fin n → K)) (N : Submodule K V),
    LinearMap.ker c ≤ N → ∀ (X : Submodule O V) (e be : ℕ) (th : Fin n → V),
    (∀ x ∈ X, ∀ i, ∃ a : O, c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a) →
    (∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X) →
    ∀ a a' : O, a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
      let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
      ∃ m : ℕ, Module.length O (↥X ⧸ ((X ⊓ N.restrictScalars O) ⊔ Tj).comap X.subtype) = m ∧
        (m : ℤ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)
def DeepMinor : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (d ρ : ℕ) (b : Basis (Fin d) K V) (z : Fin ρ → V), LinearIndependent K z →
    (∀ k, z k ∈ Submodule.span O (Set.range b)) →
    ∀ Z : Submodule O V, Submodule.span O (Set.range z) ≤ Z →
    Z ≤ Submodule.span O (Set.range b) ⊓ (Submodule.span K (Set.range z)).restrictScalars O →
    ∀ (J : Fin ρ ↪ Fin d) (a a' : O), a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i k => b.repr (z k) (J i)).det * algebraMap O K a' →
      let Zsat : Submodule O V :=
        Submodule.span O (Set.range b) ⊓ (Submodule.span K (Set.range z)).restrictScalars O
      ∃ m : ℕ, Module.length O (↥Zsat ⧸ Z.comap Zsat.subtype) = m ∧
        (m : ℤ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℤ)
def FilteredLength : Prop :=
  ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] (n : ℕ) (F : ℕ → Submodule O A),
    F 0 = ⊤ → F n = ⊥ → (∀ k, F (k + 1) ≤ F k) → ∀ N : Submodule O A,
      Module.length O (A ⧸ N) =
        ∑ k ∈ Finset.range n,
          Module.length O (↥(F k) ⧸ (F (k + 1) ⊔ (N ⊓ F k)).comap (F k).subtype)
def LocalAssembly : Prop :=
  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' : Submodule O V) (e be n : ℕ) (th : Fin n → V)
    (c : V →ₗ[K] (Fin n → K)) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W) (a a' : O),
    let X : Submodule O V := M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V))
    let NK : Submodule O V := (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    LinearMap.ker c ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    (∀ x ∈ M, ∀ i, ∃ u : O, c x i = (algebraMap O K ϖ) ^ (-(be : ℤ)) * algebraMap O K u) →
    a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
    X ⊓ NK ≤ N' → N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
      Module.length O (↥(X ⊔ Θ) ⧸ Θ.comap (X ⊔ Θ).subtype) ≤
        Module.length O (↥AA' ⧸ AA.comap AA'.subtype) +
          Module.length O (↥AA ⧸ N₁'.comap AA.subtype) +
          Module.length O (↥Zm ⧸ Z.comap Zm.subtype) +
          (((((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
            ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)).toNat : ℕ) : ℕ∞)
def OrdCeil : Prop :=
  ∀ (n : ℤ) (x : ℝ), -(x + 1) < (n : ℝ) → -⌈x⌉ ≤ n
def PoleOrderGood : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ) (e : ℤ), 1 ≤ ep → 0 ≤ c' → 0 ≤ vet →
    ν ≤ νs + c' * vet → (∃ n : ℤ, (ep : ℝ) * ν = n) → (T : ℝ) * νs ≤ e →
      ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet
def PoleOrderBad : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ), 1 ≤ ep → 1 ≤ T → 0 ≤ c' → 0 ≤ vet → ν ≤ νs + c' * vet →
    let e : ℤ := ⌈(T : ℝ) * (νs + 1)⌉
    ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet
def LevelsSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (mm : ι → ℤ) (v : ι → ℝ) (T : ℕ) (c' : ℝ),
    (∀ z, (mm z : ℝ) ≤ ep z * T * c' * v z) →
      ∑ z, (mm z : ℝ) * f z ≤ T * c' * ∑ z, ((ep z : ℝ) * f z) * v z
def MonomialCount : Prop :=
  ∀ D k : ℕ, Set.ncard {α : Fin D → ℕ | ∑ i, α i ≤ k} = (k + D).choose D
def JetRank : Prop :=
  ∀ D T : ℕ, D + 1 ≤ T → Set.ncard {α : Fin D → ℕ | ∑ i, α i ≤ T - D - 1} = (T - 1).choose D
def HockeyStick : Prop :=
  ∀ D E : ℕ, 1 ≤ D →
    ∑ j ∈ Finset.range (E + 1), (E - j + D - 1).choose (D - 1) = (E + D).choose D
def ShareBinomial : Prop :=
  ∀ D T a : ℕ, (D : ℝ) * (a + 1) ≤ (T : ℝ) - D →
    ((T + a).choose D : ℝ) ≤ ((T - 1).choose D : ℝ) * (1 + 2 * D * (a + 1) / ((T : ℝ) - D))
def ShareExponent : Prop :=
  ∀ (D T : ℕ) (δ xL xF : ℝ), 0 < δ → xL ≤ δ + xL / 4 → xF ≤ ((D : ℝ) + 4) * xL →
    xF + T * δ ≤ ((T : ℝ) + 2 * D + 6) * δ
def ShareRho : Prop :=
  ∀ (D T : ℕ) (d ρ ρ' m δ : ℝ), 0 ≤ δ → ρ ≤ d - ((T - 1).choose D : ℝ) * δ → d = ρ' + m →
    m ≤ δ * ((T + 3 * D + 6).choose D : ℝ) → ((T - 1).choose D : ℝ) * δ ≤ d →
    (D : ℝ) * (3 * D + 7) ≤ (T : ℝ) - D →
      ρ ≤ ρ' + 2 * D * (3 * D + 7) * d / ((T : ℝ) - D)
def MarkovIneq : Prop :=
  ∀ (P : ℝ[X]) (D : ℕ) (a b Mx : ℝ), a < b → P.natDegree ≤ D →
    (∀ x ∈ Set.Icc a b, |P.eval x| ≤ Mx) →
      ∀ x ∈ Set.Icc a b, |P.derivative.eval x| ≤ 2 * (D : ℝ) ^ 2 * Mx / (b - a)
def MarkovStep : Prop :=
  MarkovIneq → ∀ (P : ℝ[X]) (D Y₀ : ℕ), P.natDegree ≤ D → 2 * D ^ 2 ≤ Y₀ →
    (∀ y : ℕ, y ≤ Y₀ → 0 ≤ P.eval (y : ℝ) ∧ P.eval (y : ℝ) ≤ P.eval 0) →
      (∀ x ∈ Set.Icc (0 : ℝ) Y₀, |P.eval x| ≤ 2 * P.eval 0) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) Y₀, |P.derivative.eval x| ≤ 4 * (D : ℝ) ^ 2 * P.eval 0 / Y₀
def ShareRhoPrime : Prop :=
  ∀ (P : ℝ[X]) (D Y₀ j n₀ : ℕ) (d ga ρ' : ℝ), 1 ≤ n₀ → 2 * (n₀ : ℝ) + 2 ≤ ga →
    (Y₀ : ℤ) = ⌊(ga - 1) / n₀⌋ → j ≤ Y₀ → P.eval 0 = d → 0 ≤ d →
    (∀ x ∈ Set.Icc (0 : ℝ) Y₀, |P.derivative.eval x| ≤ 4 * (D : ℝ) ^ 2 * d / Y₀) →
    ρ' ≤ P.eval 0 - P.eval (j : ℝ) →
      ρ' ≤ 8 * j * (D : ℝ) ^ 2 * n₀ * d / ga
def SFChain : Prop :=
  ∀ (ξn lam d' ρ φ t p RR T c : ℝ), 0 < ξn → 0 ≤ lam → ξn * lam ≤ d' → 0 ≤ ρ → 0 ≤ φ →
    φ ≤ 2 * ρ * lam ^ 2 → t ≤ ξn ^ 2 * p / 4 → 1 ≤ RR → 0 ≤ T * c →
    RR * T * c * d' ^ 2 * ρ / 2 < t →
      T * c * φ < p
def AmGmTrace : Prop :=
  ∀ (f : ℕ) (x : Fin f → ℝ) (dE : ℝ), 1 ≤ f → 0 < dE → (∀ τ, 0 < x τ) →
    (dE ^ 2)⁻¹ ≤ (∏ τ, x τ) ^ 2 →
      (f : ℝ) / (dE ^ ((1 : ℝ) / (2 * f))) ^ 2 ≤ ∑ τ, x τ
def EtaPowerStep : Prop :=
  ∀ (c₁ rd RR PP T c d' ρ : ℝ) (i f : ℕ), 1 ≤ i → 1 ≤ f → 0 < rd →
    let j : ℤ := 1 + ⌊c₁ * rd ^ 2 / (2 * i * f)⌋
    c₁ < (j : ℝ) * (2 * i) * (f / rd ^ 2) ∧
      (c₁ = RR * T * c * d' ^ 2 * ρ / 2 → d' ^ 2 * ρ ≤ PP → rd ^ 2 ≤ RR → 0 ≤ RR * T * c →
        0 ≤ d' ^ 2 * ρ → (j : ℝ) ≤ 1 + RR ^ 2 * PP * T * c)
def FilIntegerStep : Prop :=
  ∀ (νF νE : ℤ) (T : ℕ) (c φ μ : ℝ), μ ≤ νF → (T : ℝ) * c * φ < μ → (νE : ℝ) ≤ c * φ →
    (T : ℤ) * νE + 1 ≤ νF
def HeightAbsorb : Prop :=
  ∀ (HL Hde X Y a : ℝ), 0 ≤ a → a ≤ 1 / 2 → 0 ≤ Y → HL ≤ X + a * Hde → Hde ≤ HL + Y →
    HL ≤ 2 * max X 0 + Y
def BetaLogMean : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ∫ t in (0 : ℝ)..1, Real.log t * ((N : ℝ) * (1 - t) ^ (N - 1)) =
      -∑ i ∈ Finset.range N, (1 : ℝ) / (i + 1)
def TraceMono : Prop :=
  ∀ (n : ℕ) (χ A B : Matrix (Fin n) (Fin n) ℂ), χ.PosSemidef → (B - A).PosSemidef →
    (χ * A).trace.re ≤ (χ * B).trace.re
def SumClose : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ : ℝ), 0 ≤ d → 0 < T → 0 < ga → 0 ≤ PP → 0 ≤ D →
    0 ≤ RR ^ 2 * c + 1 / T → κ ≤ C * k * f * b →
    PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 3 →
    PP ^ 2 * T * c ≤ f * m * b * δ₂ / 3 →
    PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 3 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) ≤ d * f * m * b * δ₂
end Formalism.LatticeBaseChangeAlt


