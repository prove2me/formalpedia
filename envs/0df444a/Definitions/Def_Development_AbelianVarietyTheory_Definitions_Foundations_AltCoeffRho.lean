-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:32.103025+00:00
-- url     : https://prove2.me/theorems/235aad5e-b30f-406a-bb9f-7affe7702851
-- title:
--   Alt Coeff Rho
-- statement:
--   Definitions and structural lemmas for Alt Coeff Rho, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/AltCoeffRho.lean

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace GlobalTheory.FlagHook
def altCoeff {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (-1) ^ Formalism.DegreeFormula.dimFl ι N * ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
    P.coeff (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => n x.1 (σ x.1 x.2)))
def rho (N : ℕ) : Fin N → ℕ := fun c => N - 1 - (c : ℕ)
def hookRho (N k r : ℕ) : Fin N → ℕ :=
  fun c => N - 1 - (c : ℕ) + (if (c : ℕ) = 0 then k - r else if (c : ℕ) ≤ r then 1 else 0)
def detE {N : ℕ} (n : Fin N → ℕ) : MvPolynomial (Fin N) ℝ :=
  Matrix.det (Matrix.of fun i c : Fin N => C (((n c).factorial : ℝ)⁻¹) * X i ^ n c)
def hookR (N k : ℕ) : MvPolynomial (Fin N) ℝ :=
  ∑ r ∈ range k, C ((-1 : ℝ) ^ r) * detE (hookRho N k r)
def hookFl {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (k : ℕ)
    (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ r ∈ range k, (-1 : ℝ) ^ r *
    altCoeff (fun τ' => if τ' = τ then hookRho N k r else rho N) P
def pw {ι : Type} (N : ℕ) (τ : ι) (k : ℕ) : MvPolynomial (ι × Fin N) ℝ := ∑ i : Fin N, X (τ, i) ^ k
def kap {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (u : ι → Fin N → ℝ) (k : ℕ)
    (γ Q : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  k * Formalism.DegreeFormula.degFl ι N (γ * Q) / (((Formalism.DegreeFormula.dimFl ι N : ℝ) + 1) * Formalism.DegreeFormula.flagDeg ι N u)
def IsDecomp {ι : Type} [Fintype ι] {N : ℕ} (u : ι → Fin N → ℝ)
    (Q : ι → ℕ → MvPolynomial (ι × Fin N) ℝ) : Prop :=
  (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (Formalism.DegreeFormula.dimFl ι N + 1 - k)) ∧
    Formalism.DegreeFormula.linRoot u ^ (Formalism.DegreeFormula.dimFl ι N + 1) = ∑ τ, ∑ k ∈ Icc 1 N, pw N τ k * Q τ k
end GlobalTheory.FlagHook


