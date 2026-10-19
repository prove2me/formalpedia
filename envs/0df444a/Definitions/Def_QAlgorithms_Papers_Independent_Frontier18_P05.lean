-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05
-- name    : QAlgorithms_Papers_Independent_Frontier18_P05
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:45:19.495525+00:00
-- url     : https://prove2.me/theorems/3bdcf1b9-3f34-48de-afd7-c6b7a38badc3
-- title:
--   Definitions for Multi-mode bosonic Gaussian channels
-- statement:
--   The objects the formalized statements of *Multi-mode bosonic Gaussian channels* (arXiv:0804.0511) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsEnvironmentalForm`: Actual environmental CCR form, possibly reordered: PDF pp.7–8, Eq.(21), footnote 3. Degenerate skew forms are excluded.
--   - `minimalNoise`: Order minimality at fixed X, PDF pp.16–17, §2.3. This is minimality in positive semidefinite order, not convex extremality.
--   - `normalizedDefect`: Normalized skew spectrum with zero eigenvalues included, PDF p.11, Eq.(37). This is a constructed normal form, not a replacement commutation form.
--   - `couplingWeight`: The diagonal M^(1/2) from Eqs.(39),(41), PDF pp.11–12. At a zero skew eigenvalue M has entry 1, not 0.
--   - `environmentVariance`: Entries of alpha and beta, PDF p.12, Eq.(45): xi=5/4 on null modes, and mu^(-1) otherwise. The reciprocal is used only on the nonzero branch.
--   - `nullSwap`: Null-mode swap A of Eq.(42), PDF p.12. Its sign reversal of the null symplectic block cancels the corresponding block contributed by M.
--   - `fullCoupling`: Normal-coordinate version of [K^(-1), O^T A], before multiplication by Ybar^(1/2) O^T and the support projection. PDF pp.11–13, Eqs.(34),(41),(52). Both blocks are explicit functions of the normalized skew spectrum.
--   - `retainedModes`: The purifier modes retained in Appendix C, PDF pp.32–33, Eqs.(126),(130). For a pure environment remove just mu=1 purifiers; for a mixed environment retain only the null-mode entangled partners. No tensor matrix power is used.
--   - `retainedCount`: Number of retained purifier modes, Appendix C, PDF pp.32–33.
--   - `retainedIndex`: A concrete enumeration of the retained original mode labels, Appendix C, PDF pp.32–33. This determines the rectangular A and correlation blocks.
--   - `retainedEmbedding`: Keep all alpha coordinates and exactly the indicated Q and P coordinates of beta, Appendix C, PDF pp.32–33, Eqs.(126)–(133).
-- source:
--   Multi-mode bosonic Gaussian channels, arXiv:0804.0511v3, https://arxiv.org/abs/0804.0511v3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

/-!
# Multi-mode bosonic Gaussian channels: covariance statements
Source: Caruso, Eisert, Giovannetti and Holevo, arXiv:0804.0511v3.
Accepted P10 definitions supply the covariance conventions and support inverse.
Operational results are deferred separately. Covariance identities do not stand
for channel equality on arbitrary Fock-space densities.
-/

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P05

open QAlgorithms.Papers.Independent.Dependency50.P10

/-- Actual environmental CCR form, possibly reordered: PDF pp.7–8, Eq.(21),
footnote 3. Degenerate skew forms are excluded. -/
def IsEnvironmentalForm {q : ℕ}
    (omega : Matrix (Phase q) (Phase q) ℝ) : Prop :=
  ∃ e : Phase q ≃ Phase q, omega = (sigma q).submatrix e e

/-- Order minimality at fixed X, PDF pp.16–17, §2.3.
This is minimality in positive semidefinite order, not convex extremality. -/
def minimalNoise {n : ℕ} (X Y : Matrix (Phase n) (Phase n) ℝ) : Prop :=
  (cpMatrix X Y).PosSemidef ∧
    ∀ Z : Matrix (Phase n) (Phase n) ℝ,
      (cpMatrix X Z).PosSemidef → (Y - Z).PosSemidef → Z = Y

example (q : ℕ) : IsEnvironmentalForm (sigma q) := by
  exact ⟨Equiv.refl _, rfl⟩

example : minimalNoise (1 : Matrix (Phase 0) (Phase 0) ℝ) 0 := by
  constructor
  · have hzero : cpMatrix (1 : Matrix (Phase 0) (Phase 0) ℝ) 0 = 0 :=
      Subsingleton.elim _ _
    rw [hzero]
    exact Matrix.PosSemidef.zero
  · intro Z _ _
    exact Subsingleton.elim _ _

/-- Normalized skew spectrum with zero eigenvalues included, PDF p.11, Eq.(37).
This is a constructed normal form, not a replacement commutation form. -/
def normalizedDefect {n : ℕ} (mu : Fin n → ℝ) :
    Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks 0 (Matrix.diagonal mu) (-Matrix.diagonal mu) 0

/-- The diagonal M^(1/2) from Eqs.(39),(41), PDF pp.11–12.
At a zero skew eigenvalue M has entry 1, not 0. -/
def couplingWeight (x : ℝ) : ℝ := if x = 0 then 1 else Real.sqrt x

/-- Entries of alpha and beta, PDF p.12, Eq.(45): xi=5/4 on null modes,
and mu^(-1) otherwise. The reciprocal is used only on the nonzero branch. -/
def environmentVariance (x : ℝ) : ℝ := if x = 0 then 5 / 4 else x⁻¹

/-- Null-mode swap A of Eq.(42), PDF p.12. Its sign reversal of the null
symplectic block cancels the corresponding block contributed by M. -/
def nullSwap {n : ℕ} (mu : Fin n → ℝ) : Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks 0 (Matrix.diagonal (fun j => if mu j = 0 then 1 else 0))
    (Matrix.diagonal (fun j => if mu j = 0 then 1 else 0)) 0

/-- Normal-coordinate version of [K^(-1), O^T A], before multiplication by
Ybar^(1/2) O^T and the support projection. PDF pp.11–13, Eqs.(34),(41),(52).
Both blocks are explicit functions of the normalized skew spectrum. -/
def fullCoupling {n : ℕ} (mu : Fin n → ℝ) :
    Matrix (Phase n) (Phase n ⊕ Phase n) ℝ :=
  fun i => Sum.elim (thermalCovariance (fun j => couplingWeight (mu j)) i)
    (nullSwap mu i)

/-- The purifier modes retained in Appendix C, PDF pp.32–33, Eqs.(126),(130).
For a pure environment remove just mu=1 purifiers; for a mixed environment
retain only the null-mode entangled partners. No tensor matrix power is used. -/
def retainedModes {n : ℕ} (mu : Fin n → ℝ) (pure : Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => if pure then mu j ≠ 1 else mu j = 0)

/-- Number of retained purifier modes, Appendix C, PDF pp.32–33. -/
def retainedCount {n : ℕ} (mu : Fin n → ℝ) (pure : Bool) : ℕ :=
  (retainedModes mu pure).card

/-- A concrete enumeration of the retained original mode labels, Appendix C,
PDF pp.32–33. This determines the rectangular A and correlation blocks. -/
def retainedIndex {n : ℕ} (mu : Fin n → ℝ) (pure : Bool)
    (k : Fin (retainedCount mu pure)) : Fin n :=
  ((retainedModes mu pure).equivFin.symm k).val

/-- Keep all alpha coordinates and exactly the indicated Q and P coordinates
of beta, Appendix C, PDF pp.32–33, Eqs.(126)–(133). -/
def retainedEmbedding {n : ℕ} (mu : Fin n → ℝ) (pure : Bool) :
    Phase n ⊕ Phase (retainedCount mu pure) → Phase n ⊕ Phase n :=
  Sum.map id (Sum.map (retainedIndex mu pure) (retainedIndex mu pure))

example : couplingWeight 0 = 1 := by simp [couplingWeight]

example : environmentVariance 0 = (5 : ℝ) / 4 := by simp [environmentVariance]

example : environmentVariance 1 = 1 := by simp [environmentVariance]

example : normalizedDefect (fun _ : Fin 1 => (1 : ℝ)) = sigma 1 := by
  simp [normalizedDefect, sigma, Matrix.diagonal_one]

example : nullSwap (fun _ : Fin 1 => (0 : ℝ)) (Sum.inl 0) (Sum.inr 0) = 1 := by
  simp [nullSwap]

example : fullCoupling (fun _ : Fin 1 => (0 : ℝ))
    (Sum.inl 0) (Sum.inl (Sum.inl 0)) = 1 := by
  simp [fullCoupling, thermalCovariance, couplingWeight]

example (n : ℕ) : retainedCount (fun _ : Fin n => (1 : ℝ)) true = 0 := by
  simp [retainedCount, retainedModes]

example (n : ℕ) : retainedCount (fun _ : Fin n => (0 : ℝ)) false = n := by
  simp [retainedCount, retainedModes]

example {n : ℕ} (mu : Fin n → ℝ) (pure : Bool) (k : Phase n) :
    retainedEmbedding mu pure (Sum.inl k) = Sum.inl k := rfl

example {n : ℕ} (mu : Fin n → ℝ) (pure : Bool)
    (k : Fin (retainedCount mu pure)) :
    retainedIndex mu pure k ∈ retainedModes mu pure :=
  ((retainedModes mu pure).equivFin.symm k).property

end QAlgorithms.Papers.Independent.Frontier18.P05


