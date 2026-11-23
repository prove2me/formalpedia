-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EigenOfTwoStep
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_EigenOfTwoStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:27.735063+00:00
-- url     : https://prove2.me/theorems/2fa02a44-d3a9-49d5-a26d-d4d46c5d75e9
-- title:
--   Eigen Of Two Step
-- statement:
--   Definitions and structural lemmas for Eigen Of Two Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/EigenOfTwoStep.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv
import Theorems.Thm_GlobalTheory_KZ_Betti_mem_potSub
import Theorems.Thm_GlobalTheory_KZ_Betti_mem_trivSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KZ.Betti.mem_potSub
attribute [local simp] GlobalTheory.KZ.Betti.mem_trivSub


set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
namespace GlobalTheory.KZ
def SSPotA (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ Algebra.adjoin ℂ (FreeAlgebra.ι ℂ '' {T : Letter | admitted N l T}),
    FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
def Tower.SSBA (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) :
    Prop :=
  ∃ P ∈ Algebra.adjoin E (FreeAlgebra.ι E '' {T : Letter | admitted N l T}),
    FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0
namespace SSAdm
variable {R : Type} [CommRing R] {A : Set Letter}
theorem lift_congr {B : Type} [Semiring B] [Algebra R B] {f g : Letter → B} (h : ∀ T ∈ A, f T = g T)
    {P : FreeAlgebra R Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P = FreeAlgebra.lift R g P := by
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [h T hT]
  | algebraMap r => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]
variable {M : Type} [AddCommGroup M] [Module R M]
open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
variable {R : Type} [CommRing R] {A : Set _root_.GlobalTheory.KZ.Letter} in
variable {M : Type} [AddCommGroup M] [Module R M] in

theorem _root_.GlobalTheory.KZ.SSAdm.lift_sub_smul_mem {f : _root_.GlobalTheory.KZ.Letter → Module.End R M}
    {lam : _root_.GlobalTheory.KZ.Letter → R} {W : Submodule R M}
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W) {x : M} (hx : ∀ T ∈ A, f T x - lam T • x ∈ W)
    {P : FreeAlgebra R _root_.GlobalTheory.KZ.Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
  have key : ∀ P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A),
      (∀ y ∈ W, FreeAlgebra.lift R f P y ∈ W) ∧
        FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
    intro P hP
    induction hP using Algebra.adjoin_induction with
    | mem P hP =>
      obtain ⟨T, hT, rfl⟩ := hP
      simp only [FreeAlgebra.lift_ι_apply]
      exact ⟨hW T hT, hx T hT⟩
    | algebraMap r =>
      simp only [AlgHom.commutes, Module.algebraMap_end_apply, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
      exact ⟨fun y hy => W.smul_mem r hy, W.zero_mem⟩
    | add P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_add, LinearMap.add_apply]
        exact W.add_mem (hP.1 y hy) (hQ.1 y hy)
      · convert W.add_mem hP.2 hQ.2 using 1
        simp only [map_add, LinearMap.add_apply, add_smul]
        abel
    | mul P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_mul, Module.End.mul_apply]
        exact hP.1 _ (hQ.1 y hy)
      · convert W.add_mem (hP.1 _ hQ.2) (W.smul_mem (FreeAlgebra.lift R lam Q) hP.2) using 1
        simp only [map_mul, Module.End.mul_apply, map_sub, LinearMap.map_smul, smul_sub,
          smul_smul]
        rw [mul_comm (FreeAlgebra.lift R lam Q)]
        abel
  exact (key P hP).2
theorem eigen_of_two_step {f : Letter → Module.End R M} {lam : Letter → R} {Z : Submodule R M}
    (hZ : ∀ T ∈ A, ∀ z ∈ Z, f T z ∈ Z) {P : FreeAlgebra R Letter}
    (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) (h1 : FreeAlgebra.lift R lam P = 1) {x : M}
    (hPx : ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) (FreeAlgebra.lift R f P x) ∈ Z)
    (hx : ∀ S ∈ A, ∀ T ∈ A,
      (f S - lam S • (1 : Module.End R M)) ((f T - lam T • (1 : Module.End R M)) x) ∈ Z) :
    ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) x ∈ Z := by
  let W : Submodule R M := ⨅ T ∈ A, Z.comap (f T - lam T • (1 : Module.End R M))
  have hmem : ∀ y, y ∈ W ↔ ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) y ∈ Z := by
    intro y; simp only [W, Submodule.mem_iInf, Submodule.mem_comap]
  have hZW : ∀ z ∈ Z, z ∈ W := fun z hz => (hmem z).2 fun T hT => by
    simpa using Z.sub_mem (hZ T hT z hz) (Z.smul_mem _ hz)
  have hW : ∀ T ∈ A, ∀ y ∈ W, f T y ∈ W := fun T hT y hy => by
    have h := W.add_mem (hZW _ ((hmem y).1 hy T hT)) (W.smul_mem (lam T) hy)
    simpa using h
  have hx' : ∀ T ∈ A, f T x - lam T • x ∈ W := fun T hT => (hmem _).2 fun S hS => by
    simpa using hx S hS T hT
  have h2 := lift_sub_smul_mem hW hx' hP
  rw [h1, one_smul] at h2
  have h3 := W.sub_mem ((hmem _).2 hPx) h2
  rw [sub_sub_cancel] at h3
  exact (hmem x).1 h3
end SSAdm
theorem SSPotA_congr {N l w : ℕ} {lam lam' : Letter → ℂ} (h : ∀ T, admitted N l T → lam T = lam' T) :
    SSPotA N l w lam ↔ SSPotA N l w lam' := by
  have key : ∀ {a b : Letter → ℂ}, (∀ T, admitted N l T → a T = b T) → SSPotA N l w a → SSPotA N l w b := by
    rintro a b hab ⟨P, hP, h1, h2⟩
    refine ⟨P, hP, ?_, fun F hF T hT => ?_⟩
    · rw [← SSAdm.lift_congr (A := {T | admitted N l T}) hab hP, h1]
    · rw [← hab T hT]; exact h2 F hF T hT
  exact ⟨key h, key fun T hT => (h T hT).symm⟩
theorem Tower.SSBA.eigen_of_two_step {X : Tower Ω ε} {N l w : ℕ} [Fact l.Prime] {E : Type} [Field E]
    [Algebra ℤ_[l] E] {lam : Letter → E} (h : X.SSBA N l w E lam) {x : E ⊗[ℤ_[l]] X.Fn l} (hx : x ∈ X.VB N l w E)
    (h2 : ∀ S, admitted N l S → ∀ T, admitted N l T →
      (X.opV N l E S - lam S • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l)))
        ((X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) x) = 0) :
    ∀ T, admitted N l T → X.opV N l E T x = lam T • x := by
  obtain ⟨P, hP, h1, hk⟩ := h
  intro T hT
  have := SSAdm.eigen_of_two_step (A := {T | admitted N l T}) (Z := ⊥) (f := X.opV N l E) (lam := lam)
    (fun T _ z hz => by rw [(Submodule.mem_bot E).1 hz, map_zero]; exact Submodule.zero_mem _) hP h1 (x := x)
    (fun T hT => (Submodule.mem_bot E).2 (hk x hx T hT))
    (fun S hS T hT => (Submodule.mem_bot E).2 (h2 S hS T hT)) T hT
  rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
  exact sub_eq_zero.1 this
example (N l : ℕ) : ¬ admitted N l (Letter.T 1) := fun h => Nat.not_prime_one h.1
example : admitted 5 3 (Letter.T 2) ∧ admitted 5 3 Letter.U ∧ admitted 5 3 (Letter.D 2) ∧
    ¬ admitted 5 3 (Letter.T 3) ∧ ¬ admitted 5 3 (Letter.T 5) ∧ ¬ admitted 5 3 (Letter.D 5) := by
  simp only [admitted]
  norm_num
example (N l w : ℕ) (lam : Letter → ℂ) (c : ℂ) :
    SSPotA N l w lam ↔
      SSPotA N l w (fun T => match T with | Letter.T 1 => c | T => lam T) := by
  refine SSPotA_congr fun T hT => ?_
  split
  · exact absurd hT.1 Nat.not_prime_one
  · rfl
example (N l : ℕ) (f : Letter → Module.End ℂ (ℂ × ℂ)) (lam : Letter → ℂ)
    (hU : f Letter.U = LinearMap.inl ℂ ℂ ℂ ∘ₗ LinearMap.snd ℂ ℂ ℂ)
    (hf : ∀ T, admitted N l T → T ≠ Letter.U → f T = 0) (hl : ∀ T, admitted N l T → lam T = 0) :
    ¬ ∃ P ∈ Algebra.adjoin ℂ (FreeAlgebra.ι ℂ '' {T : Letter | admitted N l T}), FreeAlgebra.lift ℂ lam P = 1 ∧
      ∀ x : ℂ × ℂ, ∀ T, admitted N l T →
        (f T - lam T • (1 : Module.End ℂ (ℂ × ℂ))) (FreeAlgebra.lift ℂ f P x) = 0 := by
  rintro ⟨P, hP, h1, hk⟩
  have hcase : ∀ T, admitted N l T → f T = 0 ∨ f T = LinearMap.inl ℂ ℂ ℂ ∘ₗ LinearMap.snd ℂ ℂ ℂ := fun T hT => by
    by_cases h : T = Letter.U
    · exact Or.inr (h ▸ hU)
    · exact Or.inl (hf T hT h)
  have := SSAdm.eigen_of_two_step (A := {T | admitted N l T}) (Z := ⊥) (f := f) (lam := lam)
    (fun T _ z hz => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]; exact Submodule.zero_mem _) hP h1 (x := (0, 1))
    (fun T hT => (Submodule.mem_bot ℂ).2 (hk _ T hT))
    (fun S hS T hT => by
      rcases hcase S hS with a | a <;> rcases hcase T hT with b | b <;> simp [a, b, hl S hS, hl T hT])
    Letter.U trivial
  simp [hU, hl Letter.U trivial] at this
end GlobalTheory.KZ


