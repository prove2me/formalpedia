-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_CuspInfChar
-- name    : Formalism_PeriodIntegrals_CuspInfChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:16.672014+00:00
-- url     : https://prove2.me/theorems/072ee7b6-7120-4412-b14d-ffc44f20014f
-- title:
--   Cusp Inf Char
-- statement:
--   Definitions and structural lemmas for Cusp Inf Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/CuspInfChar.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Complex Filter
open NumberField.InfinitePlace.Completion
open scoped ContDiff Classical
namespace PI.CuspInfChar
section matrices
variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
def emb (ι : A →ₙ+* B) : GL (Fin n) A →* GL (Fin n) B := Units.map
  { toFun := fun g : Matrix (Fin n) (Fin n) A => (1 + (g - 1).map ι : Matrix (Fin n) (Fin n) B)
    map_one' := by simp
    map_mul' := fun g h => by
      have : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
      rw [this, Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), Matrix.map_mul]; noncomm_ring }
abbrev GlobalTheory (n i : ℕ) : Type := {p : Fin n × Fin n // p.1.val < i ∧ i ≤ p.2.val}
def blk {i : ℕ} (x : GlobalTheory n i → A) : Matrix (Fin n) (Fin n) A :=
  of fun a b => if h : a.val < i ∧ i ≤ b.val then x ⟨(a, b), h⟩ else 0
theorem blk_mul {i : ℕ} (x y : GlobalTheory n i → A) : blk x * blk y = 0 := by
  ext a b; rw [mul_apply]; refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : c.val < i <;> simp [blk, h]
def uni {i : ℕ} (x : GlobalTheory n i → A) : GL (Fin n) A :=
  ⟨1 + blk x, 1 - blk x, by simp [add_mul, mul_sub, blk_mul], by simp [mul_add, sub_mul, blk_mul]⟩
def dia (i : ℕ) (t : Aˣ) : GL (Fin n) A :=
  ⟨diagonal fun a => if a.val < i then t else 1, diagonal fun a => if a.val < i then ↑t⁻¹ else 1,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; ext a; split_ifs <;> simp,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; ext a; split_ifs <;> simp⟩
end matrices
variable (F : Type) [Field F] [NumberField F]
abbrev Ad := AdeleRing (𝓞 F) F
abbrev Pl := HeightOneSpectrum (𝓞 F)
abbrev G (n : ℕ) := GL (Fin n) (Ad F)
instance (n i : ℕ) : MeasurableSpace (GlobalTheory n i → Ad F) := borel _
variable {F} {n : ℕ}
structure IsCuspForm (φ : G F n → ℂ) : Prop where
  cont : Continuous φ
  inv : ∀ (γ : GL (Fin n) F) g, φ (GeneralLinearGroup.map (algebraMap F (Ad F)) γ * g) = φ g
  cen : ∀ z : (Ad F)ˣ, ∃ c : ℂ, ∀ g, φ (dia n z * g) = c * φ g
  bdd : ∃ C, ∀ g, ‖φ g‖ ≤ C
  cusp : ∀ i, 0 < i → i < n → ∀ (μ : Measure (GlobalTheory n i → Ad F)) [μ.IsAddHaarMeasure] (D : Set (GlobalTheory n i → Ad F)),
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : GlobalTheory n i => AdeleRing.principalSubgroup (𝓞 F) F) D μ →
    ∀ g, ∫ x in D, φ (uni x * g) ∂μ = 0
  ne : φ ≠ 0
section finite
variable (v : Pl F)
def q : ℝ := Ideal.absNorm v.asIdeal
def Unif (ϖ : (v.adicCompletion F)ˣ) : Prop := Valued.v ϖ.val = WithZero.exp (-1 : ℤ)
def jFin : GL (Fin n) (v.adicCompletion F) →* G F n := emb
  { toFun := fun x => (0, RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v x)
    map_zero' := Prod.ext rfl (RestrictedProduct.single_zero ..)
    map_add' := fun x y => Prod.ext (add_zero _).symm (RestrictedProduct.single_add ..)
    map_mul' := fun x y => Prod.ext (mul_zero _).symm (by
      refine Eq.trans ?_ (RestrictedProduct.single_mul ..); rw [RestrictedProduct.single_eq_same]) }
def KO (n : ℕ) : Subgroup (GL (Fin n) (v.adicCompletion F)) :=
  (GeneralLinearGroup.map (v.adicCompletionIntegers F).subtype).range
def hecke (t : GL (Fin n) (v.adicCompletion F)) (φ : G F n → ℂ) (g : G F n) : ℂ :=
  ∑ᶠ h ∈ MulAction.orbit (KO v n) (t : _ ⧸ KO v n), φ (g * jFin v h.out)
def Sat (φ : G F n → ℂ) (a : Multiset ℂ) : Prop := a.card = n ∧ (∀ k ∈ KO v n, ∀ g, φ (g * jFin v k) = φ g) ∧
  ∀ ϖ, Unif v ϖ → ∀ i ≤ n, ∀ g, hecke v (dia i ϖ) φ g = √(q v) ^ (i * (n - i)) * a.esymm i * φ g
end finite
section infinite
variable {𝕜 : Type} [RCLike 𝕜]
def jInf (w : InfinitePlace F) (e : w.Completion ≃+* 𝕜) : GL (Fin n) 𝕜 →* G F n := emb
  { toFun := fun x => (Pi.single (M := fun w : InfinitePlace F => w.Completion) w (e.symm x), 0)
    map_zero' := Prod.ext (by simp; rfl) rfl
    map_add' := fun x y => Prod.ext (by rw [map_add]; exact Pi.single_add ..) (add_zero _).symm
    map_mul' := fun x y => Prod.ext (by rw [map_mul]; exact Pi.single_mul ..) (mul_zero _).symm }
variable {H : Type} [Group H] (j : GL (Fin n) 𝕜 →* H)
def SmoothAt (φ : H → ℂ) : Prop := ∀ g, ∃ Φ : (Fin n → Fin n → 𝕜) → ℂ,
  ContDiffOn ℝ ∞ Φ {x | (Matrix.of x).det ≠ 0} ∧ ∀ h, φ (g * j h) = Φ h.val
def lie (X : Matrix (Fin n) (Fin n) 𝕜) (φ : H → ℂ) (g : H) : ℂ :=
  deriv (fun t : ℝ => φ (g * j (Matrix.isUnit_exp ((t : 𝕜) • X)).unit)) 0
def dE (a b : Fin n) (φ : H → ℂ) (g : H) : ℂ :=
  (lie j (single a b 1) φ g - I * lie j (single a b RCLike.I) φ g) / Module.finrank ℝ 𝕜
def capelli (u : ℂ) (φ : H → ℂ) (g : H) : ℂ := ∑ σ : Equiv.Perm (Fin n), (σ.sign : ℤ) *
  (List.finRange n).foldr
    (fun b f x => dE j (σ b) b f x + if σ b = b then (u + ((n : ℂ) - 1) / 2 - b.val) * f x else 0) φ g
def InfAt (φ : H → ℂ) (l : Multiset ℂ) : Prop := l.card = n ∧ SmoothAt j φ ∧
  ∀ u g, capelli j u φ g = (l.map (u + ·)).prod * φ g
end infinite
def Inf (τ : F →+* ℂ) (φ : G F n → ℂ) (l : Multiset ℂ) : Prop :=
  (∀ e : (InfinitePlace.mk τ).Completion ≃+* ℝ, InfAt (jInf _ e) φ l) ∧
  ∀ e : (InfinitePlace.mk τ).Completion ≃+* ℂ, Continuous e → (∀ x : F, e (algebraMap F _ x) = τ x) →
    InfAt (jInf _ e) φ l
variable (F) in

structure Form where
  n : ℕ
  pos : 0 < n
  φ : G F n → ℂ
  cusp : IsCuspForm φ
def InfExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : Form F), (∀ᶠ v in cofinite, ∃ s, Sat v f.φ s) →
    ∀ τ : F →+* ℂ, ∃ f' : Form F, f'.n = f.n ∧ (∀ᶠ v in cofinite, ∀ s, Sat v f.φ s ↔ Sat v f'.φ s) ∧
      ∃ l : Multiset ℂ, Inf τ f'.φ l
end PI.CuspInfChar
end


