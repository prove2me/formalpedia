-- Prove2me | Definitions.Def_SpectralStoneSolution
-- name    : SpectralStoneSolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:12:40.697841+00:00
-- url     : https://prove2.me/theorems/6c8bd40c-f980-56f0-9c8e-82ace3048d41
-- title:
--   Spectral Stone Solution
-- statement:
--   Definitions and structural lemmas for Spectral Stone Solution, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/SpectralStoneSolution.lean

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
set_option autoImplicit false
open Function MeasureTheory
namespace PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
structure PVM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  proj : Set ℝ → (E →L[ℂ] E)
  isOrthogonalProjection : ∀ S, MeasurableSet S →
    IsSelfAdjoint (proj S) ∧ IsIdempotentElem (proj S)
  empty : proj ∅ = 0
  univ : proj Set.univ = 1
  inter : ∀ S T, MeasurableSet S → MeasurableSet T →
    proj (S ∩ T) = proj S * proj T
  countably_additive : ∀ (S : ℕ → Set ℝ),
    (∀ i, MeasurableSet (S i)) →
    Pairwise (Disjoint on S) →
    ∀ x, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, proj (S i) x)
      Filter.atTop (nhds (proj (⋃ i, S i) x))
def PVM.Represents (E_pvm : PVM E) (A : E →ₗ.[ℂ] E) : Prop :=
  ∃ scalarMeasure : E → Measure ℝ,
    (∀ (x : E) (S : Set ℝ), MeasurableSet S →
      scalarMeasure x S =
        ENNReal.ofReal ((@inner ℂ E _ (E_pvm.proj S x) x).re)) ∧
    (∀ x : E, x ∈ A.domain ↔
      ∫⁻ t, ‖(t : ℂ)‖₊ ^ 2 ∂(scalarMeasure x) < ⊤) ∧
    (∀ x : A.domain,
      @inner ℂ E _ (x : E) (A x) =
        ∫ t, (t : ℂ) ∂(scalarMeasure (x : E)))
def PVM.ofRoot (p : _root_.PVM E) : PVM E :=
  ⟨p.proj, p.isOrthogonalProjection, p.empty, p.univ, p.inter, p.countably_additive⟩
def PVM.toRoot (p : PVM E) : _root_.PVM E :=
  ⟨p.proj, p.isOrthogonalProjection, p.empty, p.univ, p.inter, p.countably_additive⟩
structure StrongContUnitary (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  toFun : ℝ → (E →L[ℂ] E)
  isUnitary : ∀ t, toFun t ∈ unitary (E →L[ℂ] E)
  zero : toFun 0 = 1
  add : ∀ s t, toFun (s + t) = toFun s * toFun t
  stronglyContinuous : ∀ x, Continuous (fun t => toFun t x)
def StrongContUnitary.Generates (U : StrongContUnitary E)
    (A : E →ₗ.[ℂ] E) : Prop :=
  (∀ x : E, x ∈ A.domain ↔
    ∃ y, Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
      (nhdsWithin 0 {0}ᶜ) (nhds y)) ∧
  ∀ x : A.domain, Filter.Tendsto
    (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
    (nhdsWithin 0 {0}ᶜ) (nhds (A x))
def StrongContUnitary.ofRoot (u : _root_.StrongContUnitary E) : StrongContUnitary E :=
  ⟨u.toFun, u.isUnitary, u.zero, u.add, u.stronglyContinuous⟩
def StrongContUnitary.toRoot (u : StrongContUnitary E) : _root_.StrongContUnitary E :=
  ⟨u.toFun, u.isUnitary, u.zero, u.add, u.stronglyContinuous⟩
end PalomarSpectralStone


