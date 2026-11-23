-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CokernelPairSum
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CokernelPairSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:36.31593+00:00
-- url     : https://prove2.me/theorems/dbe10713-9a42-4527-b7af-d59c6235941f
-- title:
--   Cokernel Pair Sum
-- statement:
--   Definitions and structural lemmas for Cokernel Pair Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CokernelPairSum.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc
namespace GlobalTheory.SgLoc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
def psiQ (M : Model F E) (x : E ⧸ M.Rsub) : ℂ := M.psiR (Quotient.out x)
open scoped Classical in

def cokernelPairSum (M : Model F E) {m : ℕ} (c : E) (Z Z' : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : ℂ :=
  if h : IsInt M Z ∧ IsInt M Z' then
    ∑ᶠ (θ : M.Cok (toMat M Z h.1) ≃ₗ[M.R] M.Cok (toMat M Z' h.2))
      (α : M.Cok (toMat M Z h.1) →ₗ[M.R] E ⧸ M.Rsub) (β : M.Cok (toMat M Z h.1)),
      if α β = Submodule.Quotient.mk (-c) then
        psiQ M (α (M.eCls _ - θ.symm (M.eCls _)) + (M.lam _ β - M.lam _ (θ β)))
      else 0
  else 0
def uXi {E : Type} [CommRing E] (n k : ℕ) (ξ : Fin (k + 1) → E) : Matrix (Fin n) (Fin n) E :=
  (1 : Matrix (Fin n) (Fin n) E) + Matrix.of fun a b : Fin n => if h : (b : ℕ) = k + 1 ∧ (a : ℕ) < k + 1 then ξ ⟨a, h.2⟩ else 0
open scoped Classical in

def nIsoC (M : Model F E) {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (c : M.Cls m) : ℕ :=
  if h : IsInt M Z then M.nIso (toMat M Z h) (Quotient.out c) else 0
def glue {E : Type} [CommRing E] {m p : ℕ} (H : Matrix (Fin m) (Fin m) E)
    (a : Fin (p + 1) → Fin m → E) (b : Fin m → Fin (p + 1) → E)
    (C : Matrix (Fin (p + 1)) (Fin (p + 1)) E) : Matrix (Fin (m + p + 1)) (Fin (m + p + 1)) E :=
  Matrix.reindex (finSumFinEquiv (m := m) (n := p + 1)) (finSumFinEquiv (m := m) (n := p + 1))
    (Matrix.fromBlocks H (H * Matrix.of b) (Matrix.of a * H) (Matrix.of a * H * Matrix.of b + C))
def Phi (M : Model F E) {m p : ℕ} (h : Pt E m) (c : M.Cls (m + p))
    (C : Matrix (Fin (p + 1)) (Fin (p + 1)) E) : ℂ :=
  ∫ q : Orb h × ((Fin (p + 1) → Fin m → E) × (Fin m → Fin (p + 1) → E)),
    (nIsoC M (glue (orbMat h q.1) q.2.1 q.2.2 C) c : ℂ) * phase M h q.1 *
      M.psiR (∑ i : Fin m, if (i : ℕ) + 1 = m then q.2.1 0 i + q.2.2 i 0 else 0)
    ∂((orbMeas M h).prod ((Measure.pi fun _ => volK M m).prod (Measure.pi fun _ => volK M (p + 1))))
def Om (M : Model F E) {n : ℕ} (Φ : Matrix (Fin n) (Fin n) E → ℂ) (g : Pt E n) : ℂ :=
  ∫ xy, Φ (orbMat g xy) * phase M g xy ∂(orbMeas M g)
def Tame {E : Type} [CommRing E] [TopologicalSpace E] {n : ℕ}
    (Φ : Matrix (Fin n) (Fin n) E → ℂ) : Prop :=
  (∃ S : Set E, IsCompact S ∧ ∀ C, Φ C ≠ 0 → ∀ a b, C a b ∈ S) ∧
  ∀ Q : Set E, IsCompact Q → (∀ x ∈ Q, IsUnit x) → ∃ V ∈ nhds (0 : E),
    ∀ C D : Matrix (Fin n) (Fin n) E, C.det ∈ Q → (∀ a b, D a b ∈ V) → Φ (C + D) = Φ C
def ptTwo {E : Type} [CommRing E] (t : Eˣ) (m : ℕ+) (c : Eˣ) : Pt E ((m : ℕ) + 1) :=
  ⟨[(t, m), (c, 1)], by simp⟩
def ptOne {E : Type} [CommRing E] (z : Eˣ) (m : ℕ+) : Pt E ((m : ℕ) + 1) :=
  ⟨[(z, m + 1)], by simp⟩
abbrev IB (m : ℕ) : Type := {p : Fin (m + 1) × Fin (m + 1) // m < (p.1 : ℕ) + p.2}
def zeroMat {E : Type} [CommRing E] {m : ℕ} (D : E) (x : Fin m → E) (y : IB m → E) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E := fun a b =>
  if h : m < (a : ℕ) + b then y ⟨(a, b), h⟩
  else if (a : ℕ) + b = m then
    (if h' : (a : ℕ) < m then x ⟨m - 1 - a, by omega⟩ else D * Ring.inverse (∏ k, x k))
  else 0
def gOne {E : Type} [CommRing E] {m : ℕ} (D : E) (x : Fin m → E) (y : IB m → E) : E :=
  ∑ p : IB m, if h : (p.1.1 : ℕ) + p.1.2 = m + 1 then
    (if h' : (p.1.1 : ℕ) < m then
      D * Ring.inverse (∏ k, x k) * y p *
        Ring.inverse (x ⟨m - 1 - p.1.1, by omega⟩ * x ⟨m - p.1.1, by have := p.1.2.2; omega⟩)
    else y p * Ring.inverse (x ⟨0, by have := p.1.1.2; have := p.1.2.2; omega⟩))
  else 0
def ampl (M : Model F E) {m : ℕ} (Φ : Matrix (Fin (m + 1)) (Fin (m + 1)) E → ℂ) (D : E)
    (x : Fin m → E) : ℂ :=
  (((M.modK (∏ k, x k))⁻¹ : ℝ) : ℂ) *
    ∫ y : IB m → E, Φ (zeroMat D x y) * M.psiR (gOne D x y) ∂(Measure.pi fun _ => M.mu)
end GlobalTheory.SgLoc


