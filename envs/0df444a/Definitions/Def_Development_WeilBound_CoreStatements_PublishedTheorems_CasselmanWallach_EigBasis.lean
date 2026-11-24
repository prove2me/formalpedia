-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigBasis
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:52.616804+00:00
-- url     : https://prove2.me/theorems/23779b75-a9ca-462b-8355-875ba7deffab
-- title:
--   Eig Basis
-- statement:
--   Definitions and structural lemmas for Eig Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigBasis.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CW
variable {n : ℕ}
def hs2 (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖ ^ 2
def nc (ε : Fin n → Bool) : Finset (Fin n × Fin n) := univ.filter fun p => ε p.1 ≠ ε p.2
def Xp (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single a b ((1 + Complex.I) / 2) + Matrix.single b a ((1 - Complex.I) / 2)
def phiR (s : ℕ) (R x : ℝ) : ℝ := max (((1 + x) ^ s)⁻¹ - ((1 + R) ^ s)⁻¹) 0
section Alg
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def U (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {x | ∃ l : List (Fin n × Fin n), l.length ≤ k ∧ x = (l.map fun p => E p.1 p.2).prod}
def Z (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  casimirK ε E * E a b - E a b * casimirK ε E
def Mm (E : Fin n → Fin n → Module.End ℂ V) : Matrix (Fin n) (Fin n) (Module.End ℂ V) := Matrix.of E
def Md (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Matrix (Fin n) (Fin n) (Module.End ℂ V) :=
  Matrix.of fun a b => adjSign ε a b • E a b
def Eig (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (μ : ℝ) (v : V) : Prop :=
  casimirK ε E v = (μ : ℂ) • v
def Cas (E : Fin n → Fin n → Module.End ℂ V) (κ : ℝ) : Prop := ∀ v, casimir E v = (κ : ℂ) • v
end Alg
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
structure Mod (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl : IsGlRep E
  uni : IsInfUnitary ε E
  irr : ∀ N : Submodule ℂ V, (∀ a b, ∀ v ∈ N, E a b v ∈ N) → N = ⊥ ∨ N = ⊤
  span : Submodule.span ℂ {v | ∃ μ : ℝ, Eig ε E μ v} = ⊤
  fin : ∀ R : ℝ, FiniteDimensional ℂ (Submodule.span ℂ {v | ∃ μ : ℝ, μ ≤ R ∧ Eig ε E μ v})
structure EigBasis (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {ι : Type} (b : Module.Basis ι ℂ V)
    (μ : ι → ℝ) : Prop where
  on : Orthonormal ℂ b
  eig : ∀ i, Eig ε E (μ i) (b i)
  nonneg : ∀ i, 0 ≤ μ i
  fin : ∀ R : ℝ, {i | μ i ≤ R}.Finite
def fc {ι : Type} (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) : Module.End ℂ V :=
  b.constr ℂ fun i => ((φ (μ i) : ℝ) : ℂ) • b i
def beta (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (A : Module.End ℂ V) (v w : V) : ℂ :=
  ∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (A (E p.1 p.2 w))
def MaxPr : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Mod ε E → ∀ N : ℕ,
    ∃ (m : ℕ) (K : ℝ) (I₀ : Finset V), 0 ≤ K ∧
      ∀ F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ v, ContinuousOn (F v) (UJset ε)) →
        (∀ X, inP ε X → ∀ v, ∀ g ∈ UJset ε,
          HasDerivAt (fun t : ℝ => F v (g * NormedSpace.exp (t • X))) (F (actM E X v) g) 0) →
        (∀ v, ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F v g‖ ≤ C * (1 + hs2 g) ^ N) →
        ∀ B : ℝ, 0 ≤ B → (∀ e ∈ I₀, ∀ g ∈ UJset ε, ‖F e g‖ ≤ B * (1 + hs2 g) ^ N) →
          ∀ v, ‖F v 1‖ ≤ K * B * ‖((1 + casimirK ε E) ^ m) v‖
end PositivityTheory.CW
end


