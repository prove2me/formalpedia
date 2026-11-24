-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumPairAtStarMul
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SumPairAtStarMul
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:50:47.938497+00:00
-- url     : https://prove2.me/theorems/0c06a37e-ec33-480a-89a4-781f5ae5c3b4
-- title:
--   Sum Pair At Star Mul
-- statement:
--   Definitions and structural lemmas for Sum Pair At Star Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P5.HerA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
section Gen
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
def IntOn (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) : Prop :=
  ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U, Integrable (fun g : Mt k r =>
    B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ
def AdjOn (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) (a : Pr (RadSp k r z z' π π')) : Prop :=
  (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ (∀ Φ ∈ U, a.2.unop Φ ∈ U) ∧
    ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U, pairAt μ (a.1 Φ) Ψ c = pairAt μ Φ (a.2.unop Ψ) c
theorem hsInner_swap (A C : Wq →L[ℂ] Wp) : B.hsInner C A = conj (B.hsInner A C) := by
  simp only [B.hsInner]
  rw [inner_conj_symm]
theorem hsVec_smul_hermitian_curvature' (a : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (a • A) = a • B.hsVec A := by
  ext i
  simp [B.hsVec]
theorem hsInner_smul_left' (A C : Wq →L[ℂ] Wp) (a : ℂ) : B.hsInner (a • A) C = a * B.hsInner A C := by
  simp only [B.hsInner, hsVec_smul_hermitian_curvature', inner_smul_right]
theorem hsInner_smul_right' (A C : Wq →L[ℂ] Wp) (a : ℂ) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  simp only [B.hsInner, hsVec_smul_hermitian_curvature', inner_smul_left]
theorem pairAt_swap (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Ψ Φ c = conj (pairAt μ Φ Ψ c) := by
  simp only [pairAt]
  rw [← integral_conj]
  congr 1
  funext g
  exact hsInner_swap _ _
theorem pairAt_smul_left (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairAt μ (a • Φ) Ψ c = a * pairAt μ Φ Ψ c := by
  simp only [pairAt, Submodule.coe_smul, Pi.smul_apply, hsInner_smul_left']
  exact integral_const_mul a _
theorem pairAt_smul_right (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairAt μ Φ (a • Ψ) c = conj a * pairAt μ Φ Ψ c := by
  simp only [pairAt, Submodule.coe_smul, Pi.smul_apply, hsInner_smul_right']
  exact integral_const_mul _ _
variable {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}
theorem hsInner_add_left' (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  have h : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
    ext i
    simp [B.hsVec]
  simp only [B.hsInner, h, inner_add_right]
theorem pairAt_add_left (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Φ' Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΦ' : Φ' ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (Φ + Φ') Ψ c = pairAt μ Φ Ψ c + pairAt μ Φ' Ψ c := by
  simp only [pairAt, Submodule.coe_add, Pi.add_apply, hsInner_add_left']
  exact integral_add (hU c hc Φ hΦ Ψ hΨ) (hU c hc Φ' hΦ' Ψ hΨ)
theorem hsInner_add_right' (A C C' : Wq →L[ℂ] Wp) :
    B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  have h : B.hsVec (C + C') = B.hsVec C + B.hsVec C' := by
    ext i
    simp [B.hsVec]
  simp only [B.hsInner, h, inner_add_left]
theorem pairAt_add_right (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {Φ Ψ Ψ' : RadSp k r z z' π π'}
    (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) (hΨ' : Ψ' ∈ U) :
    pairAt μ Φ (Ψ + Ψ') c = pairAt μ Φ Ψ c + pairAt μ Φ Ψ' c := by
  simp only [pairAt, Submodule.coe_add, Pi.add_apply, hsInner_add_right']
  exact integral_add (hU c hc Φ hΦ Ψ hΨ) (hU c hc Φ hΦ Ψ' hΨ')
theorem pr_alg_fst (a : ℂ) : (algebraMap ℂ (Pr (RadSp k r z z' π π')) a).1 = algebraMap ℂ _ a := rfl
theorem pr_alg_snd (a : ℂ) : (algebraMap ℂ (Pr (RadSp k r z z' π π')) a).2.unop = algebraMap ℂ _ (conj a) := rfl
def adjAlg (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π')) (hU : IntOn μ U) :
    StarSubalgebra ℂ (Pr (RadSp k r z z' π π')) where
  carrier := {a | AdjOn μ U a}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ), fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.1 (b.1 Φ)) Ψ c = pairAt μ Φ (b.2.unop (a.2.unop Ψ)) c
    rw [ha c hc _ (hb1 Φ hΦ) Ψ hΨ, hb c hc Φ hΦ _ (ha2 Ψ hΨ)]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha⟩ ⟨hb1, hb2, hb⟩
    refine ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ),
      fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.1 Φ + b.1 Φ) Ψ c = pairAt μ Φ (a.2.unop Ψ + b.2.unop Ψ) c
    rw [pairAt_add_left hU hc (ha1 Φ hΦ) (hb1 Φ hΦ) hΨ, pairAt_add_right hU hc hΦ (ha2 Ψ hΨ) (hb2 Ψ hΨ),
      ha c hc Φ hΦ Ψ hΨ, hb c hc Φ hΦ Ψ hΨ]
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun c hc Φ hΦ Ψ hΨ => ?_⟩
    · rw [pr_alg_fst, Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · rw [pr_alg_snd, Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
    · rw [pr_alg_fst, pr_alg_snd, Module.algebraMap_end_apply, Module.algebraMap_end_apply, pairAt_smul_left,
        pairAt_smul_right, Complex.conj_conj]
  star_mem' := by
    rintro a ⟨ha1, ha2, ha⟩
    refine ⟨ha2, ha1, fun c hc Φ hΦ Ψ hΨ => ?_⟩
    change pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c
    rw [pairAt_swap μ Ψ, ← ha c hc Ψ hΨ Φ hΦ, ← pairAt_swap]
end Gen
section Top
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
end Top
end Formalism.FourierDecayAlt.P5.HerA


