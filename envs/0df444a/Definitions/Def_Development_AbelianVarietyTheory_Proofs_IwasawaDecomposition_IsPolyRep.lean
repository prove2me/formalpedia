-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:09.435852+00:00
-- url     : https://prove2.me/theorems/e193c6ec-2e96-42e1-a4e2-eab8ffdd5b4c
-- title:
--   Is Poly Rep
-- statement:
--   Definitions and structural lemmas for Is Poly Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPolyRep.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix
namespace GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
def upt (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) : (L →+* ℂ) × Fin n × Fin n → ℂ :=
  fun p => X p.1 p.2.1 p.2.2
def IsUPt (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1
def ratPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => γ₀.map σ
def evM {ι : Type} (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (x : (L →+* ℂ) × Fin n × Fin n → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => MvPolynomial.eval x (P i j)
def Agrees (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) : Prop :=
  ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
    (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
    LinearMap.toMatrix b b (a.ρ γ) =
      fun i j => MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix _ _ L) p.2.1 p.2.2)) (P i j)
structure IsPolyRep {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) : Prop where
  one : Φ 1 = 1
  mul : ∀ A B, Φ (A * B) = Φ A * Φ B
  poly : ∀ i j, ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ B : GL (Fin n) ℂ,
    Φ B i j = MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) Q
def IsBEig {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (v : ι → ℂ) (lam : Fin n → ℤ) : Prop :=
  v ≠ 0 ∧ ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Φ B *ᵥ v = (∏ i, (B.val i i) ^ (lam i)) • v
def IsWtVec {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ : Fin n → ℤ) (w : ι → ℂ) : Prop :=
  ∀ D : GL (Fin n) ℂ, D.val.IsDiag → Φ D *ᵥ w = (∏ i, (D.val i i) ^ (μ i)) • w
def IsWt {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ : Fin n → ℤ) : Prop :=
  ∃ w : ι → ℂ, w ≠ 0 ∧ IsWtVec Φ μ w
def DomLE (μ lam : Fin n → ℤ) : Prop :=
  ∑ i, μ i = ∑ i, lam i ∧ ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), μ i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), lam i
def Sle {ι : Type} [Fintype ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (lam : Fin n → ℤ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ {w | ∃ ν, DomLE ν lam ∧ IsWtVec Φ ν w}
end GlobalTheory.AlgWtHW


