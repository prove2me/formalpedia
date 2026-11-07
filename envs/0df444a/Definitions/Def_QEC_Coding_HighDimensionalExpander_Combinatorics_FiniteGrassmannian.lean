-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
-- name    : QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:36:09.276998+00:00
-- url     : https://prove2.me/theorems/8443b0ef-e645-4584-9795-a72e26376360
-- title:
--   Finite Grassmannian
-- statement:
--   Definitions and structural lemmas for Finite Grassmannian, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
def FiniteGrassmannian (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (r : ℕ) := {W : Submodule k V // Module.finrank k W = r}
instance (k V : Type*) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) : Finite (FiniteGrassmannian k V r) :=
  Finite.of_injective (fun W ↦ (W.1 : Set V))
    (fun _ _ h ↦ Subtype.ext (SetLike.coe_injective h))
def IndependentFrames (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    (r : ℕ) := {v : Fin r → V // LinearIndependent k v}
noncomputable def frameSpanGrassmannian
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ) :
    IndependentFrames k V r → FiniteGrassmannian k V r :=
  fun v ↦ ⟨Submodule.span k (Set.range v.1), by
    rw [finrank_span_eq_card v.2, Fintype.card_fin]⟩
noncomputable def basisOfFrameFiber
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ)
    (W : FiniteGrassmannian k V r)
    (v : {v : IndependentFrames k V r // frameSpanGrassmannian k V r v = W}) :
    Basis (Fin r) k W.1 := by
  have hW : Submodule.span k (Set.range v.1.1) = W.1 :=
    congrArg Subtype.val v.property
  exact (Basis.span v.1.2).map (LinearEquiv.ofEq _ _ hW)
@[simp]
theorem coe_basisOfFrameFiber
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ)
    (W : FiniteGrassmannian k V r)
    (v : {v : IndependentFrames k V r // frameSpanGrassmannian k V r v = W})
    (i : Fin r) :
    ((basisOfFrameFiber k V r W v i : W.1) : V) = v.1.1 i := by
  unfold basisOfFrameFiber
  change ((Basis.span v.1.2) i : V) = v.1.1 i
  exact Basis.coe_span_apply v.1.2 i
noncomputable def grassmannianBasisEquivFrameFiber
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (r : ℕ)
    (W : FiniteGrassmannian k V r) :
    Basis (Fin r) k W.1 ≃
      {v : IndependentFrames k V r // frameSpanGrassmannian k V r v = W} where
  toFun b := ⟨⟨fun i ↦ (b i : V), b.linearIndependent.map' W.1.subtype
    (Submodule.ker_subtype _)⟩, by
      apply Subtype.ext
      change Submodule.span k (Set.range (W.1.subtype ∘ b)) = W.1
      rw [Set.range_comp, Submodule.span_image, b.span_eq,
        Submodule.map_subtype_top]⟩
  invFun v := basisOfFrameFiber k V r W v
  left_inv b := by
    apply DFunLike.coe_injective
    funext i
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp
instance finiteBasisFin
    (k V : Type*) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) : Finite (Basis (Fin r) k V) :=
  Finite.of_injective (fun b : Basis (Fin r) k V ↦ (b : Fin r → V))
    (fun _ _ h ↦ DFunLike.coe_injective h)
instance finiteIndependentFrames
    (k V : Type*) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) : Finite (IndependentFrames k V r) :=
  Finite.of_injective Subtype.val Subtype.val_injective
noncomputable def basesEquivIndependentFrames
    (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (r : ℕ) (h : Module.finrank k V = r) :
    Basis (Fin r) k V ≃ IndependentFrames k V r where
  toFun b := ⟨b, b.linearIndependent⟩
  invFun v := basisOfLinearIndependentOfCardEqFinrank' v.1 v.2 (by simp [h])
  left_inv b := by ext i; simp
  right_inv v := by apply Subtype.ext; simp
def coordinateFrame (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    Fin r → (Fin d → k) :=
  fun i ↦ Pi.single (Fin.castLE hr i) 1
theorem coordinateFrame_linearIndependent
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    LinearIndependent k (coordinateFrame k d r hr) := by
  exact (Pi.linearIndependent_single_one (Fin d) k).comp
    (Fin.castLEEmb hr) (Fin.castLEEmb hr).injective
def coordinateGrassmannian
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    FiniteGrassmannian k (Fin d → k) r :=
  frameSpanGrassmannian k (Fin d → k) r
    ⟨coordinateFrame k d r hr, coordinateFrame_linearIndependent k d r hr⟩
end QEC.Coding.HighDimensionalExpander.FiniteGeometry


