-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:20.459794+00:00
-- url     : https://prove2.me/theorems/33b017ea-2c33-4065-b16c-f598c77296e2
-- title:
--   Op LDOne Sub Mem Triv
-- statement:
--   Definitions and structural lemmas for Op LDOne Sub Mem Triv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
namespace GlobalTheory.KZ
def slP {R : Type} [CommRing R] (m : Matrix (Fin 2) (Fin 2) ℤ) : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval fun i => (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1
def Pot (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Set (ℂ → MvPolynomial (Fin 2) R) :=
  {F | (∀ z, (F z).IsHomogeneous w) ∧ ∀ γ ∈ Γ, ∃ p, ∀ z ∈ Hs,
    slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z = p}
def Triv (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Set (ℂ → MvPolynomial (Fin 2) R) :=
  {F | ∃ (ψ : ℂ → MvPolynomial (Fin 2) R) (p : MvPolynomial (Fin 2) R),
    (∀ γ ∈ Γ, ∀ z ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (ψ (mob (ofSL γ) z)) = ψ z) ∧ ∀ z ∈ Hs, F z = ψ z + p}
def opP (R : Type) [CommRing R] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    (ℂ → MvPolynomial (Fin 2) R) →ₗ[R] (ℂ → MvPolynomial (Fin 2) R) where
  toFun F z := slP m (F (mob (toGQ m) z))
  map_add' F G := by funext z; simp
  map_smul' c F := by funext z; simp
def opL (R : Type) [CommRing R] (N l : ℕ) :
    Letter → ((ℂ → MvPolynomial (Fin 2) R) →ₗ[R] (ℂ → MvPolynomial (Fin 2) R))
  | Letter.T q => (∑ j ∈ Finset.range q, opP R !![1, (j : ℤ); 0, (q : ℤ)]) +
      opP R ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])
  | Letter.U => ∑ j ∈ Finset.range l, opP R !![1, (j : ℤ); 0, (l : ℤ)]
  | Letter.D d => opP R (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)
def admitted (N l : ℕ) : Letter → Prop
  | Letter.T q => q.Prime ∧ ¬ q ∣ N * l
  | Letter.U => True
  | Letter.D d => Nat.Coprime d N
def LetAlg (R : Type) [CommRing R] (S : Letter → Prop) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | S T})
def SSPot (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ LetAlg ℂ (admitted N l), FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
def FrobAt (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ∃ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ V.valuation (s x - x ^ q) < 1
def Tower.VB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] :
    Submodule E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.range (LinearMap.baseChange E (X.B N l w).subtype)
def Tower.opV (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (T : Letter) :
    Module.End E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.baseChange E (X.op N l T)
def Tower.galV (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (s : Ω ≃ₐ[ℚ] Ω) :
    Module.End E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.baseChange E (X.galB l s)
def Tower.SSB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) : Prop :=
  ∃ P ∈ LetAlg E (admitted N l), FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0
namespace Betti
section Letters
variable {R : Type} [CommRing R] {S : Letter → Prop}
theorem lift_congr {A : Type} [Semiring A] [Algebra R A] {f g : Letter → A} (h : ∀ T, S T → f T = g T)
    {P : FreeAlgebra R Letter} (hP : P ∈ LetAlg R S) : FreeAlgebra.lift R f P = FreeAlgebra.lift R g P := by
  unfold LetAlg at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [h T hT]
  | algebraMap r => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]
end Letters
section Slash
variable {R : Type} [CommRing R]
theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (MvPolynomial.X i) = (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1 := by
  simp only [slP, MvPolynomial.aeval_X]
variable {w : ℕ} {Γ : Subgroup SL(2, ℤ)}
def potSub (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Submodule R (ℂ → MvPolynomial (Fin 2) R) where
  carrier := Pot R w Γ
  zero_mem' := ⟨fun _ => MvPolynomial.isHomogeneous_zero _ _ _, fun _ _ => ⟨0, fun _ _ => by simp⟩⟩
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    obtain ⟨q, hq⟩ := hG' γ hγ
    refine ⟨p + q, fun z hz => ?_⟩
    rw [← hp z hz, ← hq z hz]; simp only [Pi.add_apply, map_add]; ring
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    refine ⟨fun z => (MvPolynomial.homogeneousSubmodule (Fin 2) R w).smul_mem c (hF z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    refine ⟨c • p, fun z hz => ?_⟩
    rw [← hp z hz]; simp only [Pi.smul_apply, map_smul, smul_sub]
def trivSub (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Submodule R (ℂ → MvPolynomial (Fin 2) R) where
  carrier := Triv R w Γ
  zero_mem' := ⟨0, 0, fun _ _ _ _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro F G ⟨ψ, p, h1, h2⟩ ⟨ψ', p', h1', h2'⟩
    refine ⟨ψ + ψ', p + p', fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp [h1 γ hγ z hz, h1' γ hγ z hz]
    · simp only [Pi.add_apply, h2 z hz, h2' z hz]; ring
  smul_mem' := by
    rintro c F ⟨ψ, p, h1, h2⟩
    refine ⟨c • ψ, c • p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp [h1 γ hγ z hz]
    · simp [h2 z hz]
end Slash
example : slP (R := ℤ) !![1, 2; 0, 3] (MvPolynomial.X 0) = MvPolynomial.X 0 + 2 * MvPolynomial.X 1 := by
  simp [slP_X, MvPolynomial.smul_eq_C_mul]
example : admitted 5 3 (Letter.T 2) ∧ ¬ admitted 5 3 (Letter.T 0) ∧ ¬ admitted 5 3 (Letter.T 1) ∧ ¬ admitted 5 3 (Letter.T 3) ∧
    ¬ admitted 5 3 (Letter.T 4) ∧ admitted 5 3 (Letter.D 3) ∧ ¬ admitted 5 3 (Letter.D 0) := by
  simp only [admitted]; decide
example : FreeAlgebra.ι ℂ (Letter.T 0) ∉ LetAlg ℂ (admitted 5 3) := by
  intro h
  have := lift_congr (f := fun _ => (0 : ℂ)) (g := fun T => match T with | Letter.T 0 => 1 | _ => 0) (fun T hT => by
    rcases T with (_ | q) | _ | d
    · exact absurd hT.1 Nat.not_prime_zero
    all_goals rfl) h
  simp at this
example (s : Ω ≃ₐ[ℚ] Ω) : ¬ FrobAt 1 s := by
  rintro ⟨V, h, -⟩
  simp [ValuationSubring.mem_nonunits_iff] at h
end Betti
end GlobalTheory.KZ


