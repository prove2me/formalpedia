-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
-- name    : Formalism_HarderNarasimhan_QuotRealize
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:53:22.7608+00:00
-- url     : https://prove2.me/theorems/a4262901-f65c-43a1-ba26-d6a581789118
-- title:
--   Quot Realize
-- statement:
--   Definitions and structural lemmas for Quot Realize, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/QuotRealize.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.HN
section Dual
variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
def dualLat (A : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ A, f x ∈ Set.range (algebraMap (𝓞 K) K)}
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    rintro f g hf hg x hx
    obtain ⟨a, ha⟩ := hf x hx
    obtain ⟨c, hc⟩ := hg x hx
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' := by
    rintro r f hf x hx
    obtain ⟨a, ha⟩ := hf x hx
    exact ⟨r * a, by simp [ha, Algebra.smul_def]⟩
def dualFrame (X : InfinitePlace K → Matrix ι ι ℂ) : InfinitePlace K → Matrix ι ι ℂ :=
  fun v => ((X v).transpose)⁻¹
end Dual
def Rerealize : Prop :=
  ∀ (K V ι V'' κ : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V''] [Module K V''] [Module (𝓞 K) V''] [IsScalarTower (𝓞 K) K V'']
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b'' : Basis κ K V'') (X'' : InfinitePlace K → Matrix κ κ ℂ) (ψ : V →ₗ[K] V''),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X'' v).det) → Function.Injective ψ →
    (∀ v x, Formalism.HermitianLatticesTheory.normAt b'' X'' v (ψ x) = Formalism.HermitianLatticesTheory.normAt b X v x) →
    ∀ A : Submodule (𝓞 K) V, A.FG →
      ht b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) = ht b X A ∧
      size b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) = size b X A ∧
      slope (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) =
        slope (Formalism.HermitianLatticesTheory.realize b X) A ∧
      muMax (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) =
        muMax (Formalism.HermitianLatticesTheory.realize b X) A ∧
      muMin (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) =
        muMin (Formalism.HermitianLatticesTheory.realize b X) A ∧
      leastSize b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) = leastSize b X A ∧
      largestSize b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) = largestSize b X A
def QuotRealize : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A S : Submodule (𝓞 K) V, A.FG → IsSat (Formalism.HermitianLatticesTheory.realize b X) A S →
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
        (b'' : Basis κ K (V ⧸ Submodule.span K (S : Set V)))
        (X'' : InfinitePlace K → Matrix κ κ ℂ),
        (∀ v, IsUnit (X'' v).det) ∧
        (∀ v (x : V), Formalism.HermitianLatticesTheory.normAt b'' X'' v ((Submodule.span K (S : Set V)).mkQ x) =
          ‖(Submodule.span ℂ ((fun y => (WithLp.equiv 2 (ι → ℂ)).symm
              (Formalism.HermitianLatticesTheory.fcoord b X v y)) '' (Submodule.span K (S : Set V) : Set V)))ᗮ.starProjection
            ((WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v x))‖) ∧
        ∀ N : Submodule (𝓞 K) V, S ≤ N → N ≤ A →
          htQ b X N S = ht b'' X''
            (N.map ((Submodule.span K (S : Set V)).mkQ.restrictScalars (𝓞 K))) ∧
          sizeQ b X N S = size b'' X''
            (N.map ((Submodule.span K (S : Set V)).mkQ.restrictScalars (𝓞 K)))
def DualPl : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A : Submodule (𝓞 K) V, A.FG → Submodule.span K (A : Set V) = ⊤ →
      (dualLat A).FG ∧ Submodule.span K (dualLat A : Set (Module.Dual K V)) = ⊤ ∧
      ht b.dualBasis (dualFrame X) (dualLat A) = (ht b X A)⁻¹ ∧
      size b.dualBasis (dualFrame X) (dualLat A) = (size b X A)⁻¹ ∧
      leastSize b.dualBasis (dualFrame X) (dualLat A) = (largestSize b X A)⁻¹ ∧
      largestSize b.dualBasis (dualFrame X) (dualLat A) = (leastSize b X A)⁻¹ ∧
      (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) = A
end Formalism.HN


