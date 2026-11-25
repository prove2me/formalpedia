-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:28:28.958291+00:00
-- url     : https://prove2.me/theorems/b2d25211-3887-4f86-9aed-330e395691b0
-- title:
--   Is Herm Of Mem LZ
-- statement:
--   Definitions and structural lemmas for Is Herm Of Mem LZ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Cm_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Cm_mul_Am
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Mmat_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_embH_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_nonempty_Psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_tau_kappa0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.MaxCusp
open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}
def IsIsoFam (G : Matrix (Fin r) (Fin r) E) (u : Fin d → Fin r → E) : Prop :=
  (∀ i k, herm G (u i) (u k) = 0) ∧ LinearIndependent E u
def IsHerm {ι : Type} (b : ι → Fin d → Fin d → ℂ) : Prop := ∀ τ i k, b τ k i = conj (b τ i k)
variable (X : Data E r)
def zmat (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a j => (if a = j then 1 else 0) -
    I * X.c τ * ∑ i, ∑ k, b τ i k * Data.emb τ.1 (u i) a *
      ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l)
def Zb (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (zmat X u b τ * mat x τ : Matrix (Fin r) (Fin r) ℂ)
def pairR (χ b : X.Ψ → Fin d → Fin d → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re
def embH (β : Matrix (Fin d) (Fin d) E) : X.Ψ → Fin d → Fin d → ℂ := fun τ i k => τ.1 (β i k)
def LZ (d g : ℕ) : Set (X.Ψ → Fin d → Fin d → ℂ) :=
  {b | ∃ β : Matrix (Fin d) (Fin d) E, (∀ i k, cc (β i k) = β k i) ∧
    (∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((g * dEnat E : ℕ) : E) / 2 * γ) ∧ b = embH X β}
def IsFreqZ (g : ℕ) (χ : X.Ψ → Fin d → Fin d → ℂ) : Prop :=
  ∀ b ∈ LZ X d g, ∃ k : ℤ, 2 * pairR X χ b = k
def IsLZBasis (g : ℕ) (ω : Fin (d * d * Fintype.card X.Ψ) → X.Ψ → Fin d → Fin d → ℂ) : Prop :=
  (∀ j, ω j ∈ LZ X d g) ∧
    (∀ b ∈ LZ X d g, ∃! n : Fin (d * d * Fintype.card X.Ψ) → ℤ, b = ∑ j, (n j : ℂ) • ω j) ∧
    LinearIndependent ℝ ω
open Classical in

def fz (u : Fin d → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin d → Fin d → ℂ) (G : Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℂ :=
  if IsHerm χ ∧ IsFreqZ X g χ then
    if h : ∃ ω, IsLZBasis (d := d) X g ω then
      ∫ t in Set.pi Set.univ (fun _ : Fin (d * d * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1),
        G (Zb X u (∑ j, (t j : ℂ) • h.choose j) x) *
          cexp (-(4 * Real.pi * I) * pairR X χ (∑ j, (t j : ℂ) • h.choose j))
    else 0
  else 0
def chiAt (χ : X.Ψ → Fin d → Fin d → ℂ) (a : X.Ψ → Fin d → ℂ) (τ : X.Ψ) : ℂ :=
  ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)
def uvec (u : Fin d → Fin r → E) (a : X.Ψ → Fin d → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => ∑ i, a τ i • Data.emb τ.1 (u i)
def embC (a : Fin d → E) : X.Ψ → Fin d → ℂ := fun τ i => τ.1 (a i)
section Two
end Two
def Am (u : Fin d → Fin r → E) (τ : X.Ψ) : Matrix (Fin r) (Fin d) ℂ :=
  Matrix.of fun a i => Data.emb τ.1 (u i) a
def Cm (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    Matrix (Fin d) (Fin r) ℂ :=
  Matrix.of fun i j => -(I * X.c τ) * ∑ k, b τ i k *
    ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l)
theorem zmat_eq (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    zmat X u b τ = 1 + Am X u τ * Cm X u b τ := by
  ext a j
  simp only [zmat, Am, Cm, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring
theorem Cm_add (u : Fin d → Fin r → E) (b b' : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    Cm X u (b + b') τ = Cm X u b τ + Cm X u b' τ := by
  ext i j
  simp only [Cm, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring
theorem Cm_mul_Am (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) : Cm X u b τ * Am X u τ = 0 := by
  have hS : ∀ i' k, ∑ j, Data.emb τ.1 (u i') j *
      ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l) = 0 := by
    intro i' k
    have h := hermC_emb τ.1 X.Gm (u i') (u k)
    rw [hu, map_zero] at h
    rw [← h]
    simp only [hermC, Finset.mul_sum, mul_assoc]
  ext i i'
  simp only [Cm, Am, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  have : ∑ j, -(I * (X.c τ : ℂ)) *
      (∑ k, b τ i k * ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l)) *
      Data.emb τ.1 (u i') j = -(I * X.c τ) * ∑ k, b τ i k *
        ∑ j, Data.emb τ.1 (u i') j * ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [this]
  simp [hS]
theorem zmat_mul (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    zmat X u b τ * zmat X u b' τ = zmat X u (b + b') τ := by
  rw [zmat_eq, zmat_eq, zmat_eq, Cm_add]
  have h := Cm_mul_Am X u hu b τ
  have h0 : Am X u τ * Cm X u b τ * (Am X u τ * Cm X u b' τ) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Cm X u b τ), h, Matrix.zero_mul, Matrix.mul_zero]
  simp only [mul_add, add_mul, mul_one, one_mul, h0, add_zero]
  rw [Matrix.mul_add, add_assoc]
def Mmat (u : Fin d → Fin r → E) (β : Matrix (Fin d) (Fin d) E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a j => (if a = j then 1 else 0) +
    X.κ0 * ∑ i, ∑ k, β i k * u i a * ∑ l, X.Gm j l * cc (u k l)
theorem Mmat_map (u : Fin d → Fin r → E) (β : Matrix (Fin d) (Fin d) E) (τ : X.Ψ) :
    (Mmat X u β).map τ.1 = zmat X u (embH X β) τ := by
  ext a j
  simp only [Mmat, zmat, embH, Matrix.map_apply, Matrix.of_apply, map_add, map_mul, map_sum,
    Data.emb, emb_cc, X.tau_kappa0, apply_ite, map_one, map_zero]
  ring
theorem embH_add (β β' : Matrix (Fin d) (Fin d) E) : embH X (β + β') = embH X β + embH X β' := by
  funext τ i k; simp [embH]
theorem Mmat_zero (u : Fin d → Fin r → E) : Mmat X u 0 = 1 := by
  ext a j; simp [Mmat, Matrix.one_apply]
theorem Mmat_mul (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β β' : Matrix (Fin d) (Fin d) E) : Mmat X u β * Mmat X u β' = Mmat X u (β + β') := by
  obtain ⟨τ0⟩ := X.nonempty_Psi
  apply Matrix.map_injective τ0.1.injective
  simp only
  rw [Matrix.map_mul, Mmat_map, Mmat_map, Mmat_map, zmat_mul X u hu, embH_add]
def gam (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin d) (Fin d) E) : GL (Fin r) E :=
  ⟨Mmat X u β, Mmat X u (-β), by rw [Mmat_mul X u hu, add_neg_cancel, Mmat_zero],
    by rw [Mmat_mul X u hu, neg_add_cancel, Mmat_zero]⟩
section Level
variable (Y : DataX E r)
end Level
end
end GlobalTheory.MaxCusp


