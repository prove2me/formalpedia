-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_GradedFreeLengthFiltered
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_GradedFreeLengthFiltered
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:56:29.929599+00:00
-- url     : https://prove2.me/theorems/4260ff5b-20a7-4b30-80c1-837fde95a392
-- title:
--   Graded Free Length Filtered
-- statement:
--   Definitions and structural lemmas for Graded Free Length Filtered, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/GradedFreeLengthFiltered.lean

import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LocalStepLevelsExt
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
open Module
def LocalisationSplit : Prop :=
  ∀ (B Q : Type) [CommRing B] [AddCommGroup Q] [Module B Q],
    Module.length B Q ≠ ⊤ → Finite (MaximalSpectrum B) →
      Nonempty (Q ≃ₗ[B] ((m : MaximalSpectrum B) → LocalizedModule m.asIdeal.primeCompl Q))
def LeadingTermLength : Prop :=
  ∀ (O A A0 : Type) [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup A0] [Module O A0]
    (n : ℕ) (F : ℕ → Submodule O A) (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (δ : ℕ)
    (t : Fin δ → A0) (σ : ∀ k, ↥(F k) →ₗ[O] ({α : ι // deg α = k} → A0)) (u : ι → Fin δ → A),
    F 0 = ⊤ → F n = ⊥ → (∀ k, F (k + 1) ≤ F k) →
    (∀ k, LinearMap.ker (σ k) = (F (k + 1)).comap (F k).subtype) →
    (∀ k, Function.Surjective (σ k)) → (∀ α, deg α < n) →
    (∀ α i, ∃ h : u α i ∈ F (deg α), σ (deg α) ⟨u α i, h⟩ = Pi.single ⟨α, rfl⟩ (t i)) →
    LinearIndependent O t →
      Module.length O (A ⧸ Submodule.span O (Set.range fun p : ι × Fin δ => u p.1 p.2)) =
        (Fintype.card ι : ℕ∞) * Module.length O (A0 ⧸ Submodule.span O (Set.range t))
def IndexBaseChange : Prop :=
  ∀ (O O' K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Flat O O'] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (ϖ : O), Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (A B : Submodule O V), Formalism.LatticeIndexTer.IsLat O K V A → Formalism.LatticeIndexTer.IsLat O K V B →
      Formalism.LatticeIndexTer.idx O' (TensorProduct O O' V) (A.baseChange O') (B.baseChange O') =
        Formalism.LatticeIndexTer.idx O V A B
def LocalStepClosed : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O K K₁ V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
    [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' : Submodule O V) (e be n : ℕ) (th : Fin n → V)
    (c : V →ₗ[K] (Fin n → K₁)) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W) (a a' : O),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    LinearMap.ker c ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    LinearMap.ker c ⊔ Submodule.span K (Set.range th) = ⊤ →
    (∀ x ∈ M, ∀ i, ∃ y ∈ integralClosure O K₁, c x i = (algebraMap O K₁ ϖ) ^ (-(be : ℤ)) * y) →
    a ≠ 0 → a' ≠ 0 →
    algebraMap O K a =
      Algebra.norm K (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
    M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) ⊓
      (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    ∀ (Rr Aq : ι → Type) [∀ z, CommRing (Rr z)] [∀ z, IsLocalRing (Rr z)] [∀ z, Algebra O (Rr z)]
      [∀ z, IsLocalHom (algebraMap O (Rr z))] [∀ z, AddCommGroup (Aq z)] [∀ z, Module (Rr z) (Aq z)]
      [∀ z, Module O (Aq z)] [∀ z, IsScalarTower O (Rr z) (Aq z)]
      (xq : ∀ z, Rr z) (nq : ι → ℕ) (Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)) (rq : ι → ℕ → ℕ),
    (∀ z, Fq z 0 = ⊤) → (∀ z, Fq z (nq z) = ⊥) → (∀ z k, k < nq z → Fq z (k + 1) ≤ Fq z k) →
    (∀ z k, k < nq z → ∀ y ∈ Fq z k, xq z • y ∈ Fq z (k + 1) → y ∈ Fq z (k + 1)) →
    (∀ z k, k < nq z →
      Module.length (Rr z)
          (↥(Fq z k) ⧸ (Fq z (k + 1) ⊔ (Fq z k).map
            ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
              (LinearMap.id : Aq z →ₗ[Rr z] Aq z))).comap (Fq z k).subtype) =
        ((rq z k * (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat : ℕ) : ℕ∞)) →
    (∀ z, ∑ k ∈ Finset.range (nq z), rq z k = R) →
    (∀ z, Module.length (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (Rr z)) = (f z : ℕ∞)) →
    Nonempty ((↥AA' ⧸ AA.comap AA'.subtype) ≃ₗ[O]
      ((z : ι) → Aq z ⧸ (⊤ : Submodule (Rr z) (Aq z)).map
        ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
          (LinearMap.id : Aq z →ₗ[Rr z] Aq z)))) →
    ∀ (A0 : Type) [AddCommGroup A0] [Module O A0] (n1 : ℕ) (F1 : ℕ → Submodule O ↥AA) (ι1 : Type)
      [Fintype ι1] [DecidableEq ι1] (deg : ι1 → ℕ) (δ : ℕ) (t : Fin δ → A0)
      (σ : ∀ k, ↥(F1 k) →ₗ[O] ({α : ι1 // deg α = k} → A0)) (u : ι1 → Fin δ → ↥AA),
    F1 0 = ⊤ → F1 n1 = ⊥ → (∀ k, F1 (k + 1) ≤ F1 k) →
    (∀ k, LinearMap.ker (σ k) = (F1 (k + 1)).comap (F1 k).subtype) →
    (∀ k, Function.Surjective (σ k)) → (∀ α, deg α < n1) →
    (∀ α i, ∃ h : u α i ∈ F1 (deg α), σ (deg α) ⟨u α i, h⟩ = Pi.single ⟨α, rfl⟩ (t i)) →
    LinearIndependent O t →
    N₁'.comap AA.subtype = Submodule.span O (Set.range fun p : ι1 × Fin δ => u p.1 p.2) →
    Fintype.card ι1 = R →
    Module.length O (A0 ⧸ Submodule.span O (Set.range t)) = (I : ℕ∞) →
    ∀ V' : Submodule K V,
      (finrank K K₁ : ℝ) *
          (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (finrank K K₁ : ℝ) * ((e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ)) +
          (((IsDiscreteValuationRing.addVal O a).toNat : ℝ) -
            ((IsDiscreteValuationRing.addVal O a').toNat : ℝ) +
            (finrank K K₁ : ℝ) * (n : ℝ) * (be : ℝ))
def IndexBaseChangeQlen : Prop :=
  ∀ (O O' V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Flat O O']
    [AddCommGroup V] [Module O V] (ϖ : O), Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (A B : Submodule O V), Formalism.LatticeIndexTer.qlen O V A B ≠ ⊤ → Formalism.LatticeIndexTer.qlen O V B A ≠ ⊤ →
      Formalism.LatticeIndexTer.idx O' (TensorProduct O O' V) (A.baseChange O') (B.baseChange O') =
        Formalism.LatticeIndexTer.idx O V A B
def GradedFreeLength : Prop :=
  ∀ (Rr D G : Type) [CommRing Rr] [IsLocalRing Rr] [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] [Algebra Rr D] [AddCommGroup G] [Module Rr G] (x : Rr) (r mm : ℕ),
    Function.Surjective (algebraMap Rr D) → Irreducible (algebraMap Rr D x) →
    Nonempty (G ≃ₗ[Rr] (Fin r → D)) →
      Module.length Rr (G ⧸ (⊤ : Submodule Rr G).map ((x ^ mm) • (LinearMap.id : G →ₗ[Rr] G))) =
        ((r * mm : ℕ) : ℕ∞)
def GradedFreeLengthFiltered : Prop :=
  ∀ (Rr D A : Type) [CommRing Rr] [IsLocalRing Rr] [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] [Algebra Rr D] [AddCommGroup A] [Module Rr A] (x : Rr) (r mm : ℕ)
    (F F' : Submodule Rr A) (σ : ↥F →ₗ[Rr] (Fin r → D)),
    Function.Surjective (algebraMap Rr D) → Irreducible (algebraMap Rr D x) →
    Function.Surjective σ → LinearMap.ker σ = F'.comap F.subtype →
      Module.length Rr
          (↥F ⧸ (F' ⊔ F.map ((x ^ mm) • (LinearMap.id : A →ₗ[Rr] A))).comap F.subtype) =
        ((r * mm : ℕ) : ℕ∞) ∧
      ∀ a ∈ F, x • a ∈ F' → a ∈ F'
end Formalism.LatticeBaseChangeAlt


