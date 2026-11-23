-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_IntegralModuleBasisStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_IntegralModuleBasisStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:41.906234+00:00
-- url     : https://prove2.me/theorems/3b0b1afe-f3f4-4458-b51d-924b3a9a6cc5
-- title:
--   Integral Module Basis Statement
-- statement:
--   Definitions and structural lemmas for Integral Module Basis Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/IntegralModuleBases/IntegralModuleBasisStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Module Matrix
open scoped NumberField
def gramConst (d : ℕ) : ℝ := 2 ^ (d * (d - 1))
def endConst (d : ℕ) : ℝ := 4 ^ (d * d)
def ShortBasisStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (R : ℝ)
    (v : Fin (finrank ℝ E) → E), LinearIndependent ℝ v → (∀ i, v i ∈ L) → (∀ i, ‖v i‖ ≤ R) →
    ∃ b : Module.Basis (Fin (finrank ℝ E)) ℤ L, ∀ j, ‖(b j : E)‖ ≤ (finrank ℝ E : ℝ) * R
def ModuleBasisStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (J κ : Type) [Finite J] [Finite κ]
    (A : J → E →ₗ[ℝ] E) (x : κ → E) (α R : ℝ), 0 ≤ α → (∀ j y, ‖A j y‖ ≤ α * ‖y‖) →
    (∀ k, ‖x k‖ ≤ R) → (∀ j k, A j (x k) ∈ L) →
    Submodule.span ℝ (Set.range fun p : J × κ => A p.1 (x p.2)) = ⊤ →
    ∃ b : Module.Basis (Fin (finrank ℝ E)) ℤ L, ∀ i, ‖(b i : E)‖ ≤ (finrank ℝ E : ℝ) * (α * R)
def LatticeRedStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ V : ℝ)
    (c : Module.Basis (Fin (finrank ℝ E)) ℤ L), 0 < μ → 0 ≤ V →
    (∀ x ∈ L, x ≠ 0 → μ ≤ ‖x‖) → (Matrix.gram ℝ fun i => (c i : E)).det ≤ V ^ 2 →
    ∃ b : Module.Basis (Fin (finrank ℝ E)) ℤ L,
      (∀ i, ‖(b i : E)‖ ≤ 2 ^ (finrank ℝ E * finrank ℝ E) * V / μ ^ (finrank ℝ E - 1)) ∧
      ∀ (x : L) (i : Fin (finrank ℝ E)),
        |((b.repr x i : ℤ) : ℝ)| ≤ 3 ^ finrank ℝ E * ‖(x : E)‖ / μ
def IntegerBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ ω : Module.Basis (Fin (finrank ℚ K)) ℤ (𝓞 K), ∀ (i : Fin (finrank ℚ K)) (φ : K →+* ℂ),
      ‖φ (ω i : K)‖ ≤ 2 ^ (finrank ℚ K * finrank ℚ K) * Real.sqrt |(NumberField.discr K : ℝ)|
def IntegralModuleBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : 𝓞 K →+* Module.End ℝ E) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (κ : Type) [Finite κ] (x : κ → E) (R : ℝ),
    (∀ (a : 𝓞 K) (B : ℝ), (∀ φ : K →+* ℂ, ‖φ (a : K)‖ ≤ B) → ∀ y, ‖ρ a y‖ ≤ B * ‖y‖) →
    (∀ k, ‖x k‖ ≤ R) → (∀ (a : 𝓞 K) k, ρ a (x k) ∈ L) →
    Submodule.span ℝ (Set.range fun p : 𝓞 K × κ => ρ p.1 (x p.2)) = ⊤ →
    ∃ b : Module.Basis (Fin (finrank ℝ E)) ℤ L, ∀ i, ‖(b i : E)‖ ≤
      (finrank ℝ E : ℝ) * (2 ^ (finrank ℚ K * finrank ℚ K) *
        Real.sqrt |(NumberField.discr K : ℝ)| * R)
def RedGramStatement : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (m D : ℝ), A.PosDef → 0 < m →
    (∀ x : Fin d → ℤ, x ≠ 0 → m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ))) →
    A.det ≤ D →
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ),
      (∀ i, (fun l => (e i l : ℝ)) ⬝ᵥ (A *ᵥ fun l => (e i l : ℝ)) ≤
        2 ^ (d * (d - 1)) * D / m ^ (d - 1)) ∧
      ∀ (x : Fin d → ℤ) (i : Fin d), ((e.repr x i : ℤ) : ℝ) ^ 2 ≤
        9 ^ d * ((fun l => (x l : ℝ)) ⬝ᵥ (A *ᵥ fun l => (x l : ℝ))) / m
def GramReduceStatement : Prop :=
  ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℤ), Gᵀ = G → (G.map ((↑) : ℤ → ℝ)).PosDef →
    ∃ P : Matrix (Fin d) (Fin d) ℤ, IsUnit P.det ∧
      ∀ i j, |((Pᵀ * G * P) i j : ℝ)| ≤ gramConst d * (G.det : ℝ)
def DecoratedReduceStatement : Prop :=
  ∀ (d k : ℕ) (G : Matrix (Fin d) (Fin d) ℤ) (T : Fin k → Matrix (Fin d) (Fin d) ℤ) (α : ℝ),
    Gᵀ = G → (G.map ((↑) : ℤ → ℝ)).PosDef → 0 ≤ α →
    (∀ (a : Fin k) (x : Fin d → ℝ),
      ((T a).map ((↑) : ℤ → ℝ) *ᵥ x) ⬝ᵥ (G.map ((↑) : ℤ → ℝ) *ᵥ ((T a).map ((↑) : ℤ → ℝ) *ᵥ x)) ≤
        α ^ 2 * (x ⬝ᵥ (G.map ((↑) : ℤ → ℝ) *ᵥ x))) →
    ∃ P : Matrix (Fin d) (Fin d) ℤ, IsUnit P.det ∧
      (∀ i j, |((Pᵀ * G * P) i j : ℝ)| ≤ gramConst d * (G.det : ℝ)) ∧
      ∀ a i j, |((P⁻¹ * T a * P) i j : ℝ)| ≤ endConst d * α * Real.sqrt (G.det : ℝ)
def BoxCountStatement : Prop :=
  ∀ (k d : ℕ) (B : ℝ), 0 ≤ B →
    ({T : Fin k → Matrix (Fin d) (Fin d) ℤ | ∀ a i j, |((T a i j : ℤ) : ℝ)| ≤ B}.ncard : ℝ) ≤
      (2 * B + 1) ^ (k * (d * d))
def GramCountStatement : Prop :=
  ∀ (d : ℕ) (D : ℝ), 1 ≤ D →
    ∃ S : Finset (Matrix (Fin d) (Fin d) ℤ),
      (S.card : ℝ) ≤ (2 * gramConst d * D + 1) ^ (d * d) ∧
      ∀ G : Matrix (Fin d) (Fin d) ℤ, Gᵀ = G → (G.map ((↑) : ℤ → ℝ)).PosDef → (G.det : ℝ) ≤ D →
        ∃ P : Matrix (Fin d) (Fin d) ℤ, IsUnit P.det ∧ Pᵀ * G * P ∈ S
def DecoratedCountStatement : Prop :=
  ∀ (d k : ℕ) (α D : ℝ), 0 ≤ α → 1 ≤ D →
    ∃ S : Finset (Matrix (Fin d) (Fin d) ℤ × (Fin k → Matrix (Fin d) (Fin d) ℤ)),
      (S.card : ℝ) ≤ (2 * gramConst d * D + 1) ^ (d * d) *
        (2 * endConst d * α * Real.sqrt D + 1) ^ (k * (d * d)) ∧
      ∀ (G : Matrix (Fin d) (Fin d) ℤ) (T : Fin k → Matrix (Fin d) (Fin d) ℤ),
        Gᵀ = G → (G.map ((↑) : ℤ → ℝ)).PosDef → (G.det : ℝ) ≤ D →
        (∀ (a : Fin k) (x : Fin d → ℝ),
          ((T a).map ((↑) : ℤ → ℝ) *ᵥ x) ⬝ᵥ (G.map ((↑) : ℤ → ℝ) *ᵥ ((T a).map ((↑) : ℤ → ℝ) *ᵥ x)) ≤
            α ^ 2 * (x ⬝ᵥ (G.map ((↑) : ℤ → ℝ) *ᵥ x))) →
        ∃ P : Matrix (Fin d) (Fin d) ℤ, IsUnit P.det ∧ (Pᵀ * G * P, fun a => P⁻¹ * T a * P) ∈ S
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
end


