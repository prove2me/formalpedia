-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P17
-- name    : QAlgorithms_Papers_Independent_Frontier30_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:52:38.043193+00:00
-- url     : https://prove2.me/theorems/3a38888a-9cb1-43d5-98d1-bc0273141fd6
-- title:
--   Definitions for The mixed Schur transform: efficient quantum circuit and applications
-- statement:
--   The objects the formalized statements of *The mixed Schur transform: efficient quantum circuit and applications* (arXiv:2310.01613) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `teleportSeed`: The normalized Bell projector on A times A-prime, regrouping the m Bell pairs with all A wires first (arXiv:2310.01613v1, PDF p.29, Eq.(87)). Its nonzero entries are 1/d^m. Results require positive d.
--   - `IsUnitaryEquivariant`: Equivariance on all normalized input density matrices, with the same unitary on every input and output qudit (arXiv:2310.01613v1, PDF p.27, Eq.(77)). CPTP is a separate hypothesis, supplied by the accepted IsChannel predicate.
--   - `conclusiveDensity`: Resolved successful POVM density C M^U, relative to probability Haar measure (arXiv:2310.01613v1, PDF p.29, Eqs.(86)–(87)). The dual factor is entrywise conjugation, not the adjoint.
--   - `conclusiveEffect`: The coarse successful effect, used only for its probability. The quantum protocol also keeps the resolved U for feed-forward (arXiv:2310.01613v1, PDF p.29, Eq.(86)). The accepted Haar measure is normalized on all of U(d).
--   - `inputChoi`: The actual input rho tensor J_N, reassociated as (A times A-prime) times B so the first two registers can be measured (arXiv:2310.01613v1, PDF p.27, Eq.(82)). Exactly one normalized Choi resource is used.
--   - `correctedOutcome`: The unnormalized corrected output density for a resolved successful U. Partial trace eliminates Alice's measured systems; Bob applies (U dagger)^n. This is the density version of Eq.(82), including the factor C from Eq.(86) (arXiv:2310.01613v1, PDF pp.27,29).
--   - `twoSwap`: The two-wire SWAP in the word convention used for Eq.(92) (arXiv:2310.01613v1, PDF p.29).
--   - `twoInputScale`: The normalization explicitly chosen below Eq.(92) (arXiv:2310.01613v1, PDF p.29). Subtraction takes place in the reals.
--   - `twoInputEffectFormula`: The explicit Haar-integrated effect in Eq.(92), at the source's chosen C (arXiv:2310.01613v1, PDF p.29). Results exclude d=0 and d=1.
--   - `conclusiveProbability`: The Born success probability from Alice's reduced input, whose resource marginal is I/d^m (arXiv:2310.01613v1, PDF p.29, Eq.(88)).
-- source:
--   The mixed Schur transform: efficient quantum circuit and applications, arXiv:2310.01613v1, https://arxiv.org/abs/2310.01613v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
Statements from Nguyen, arXiv:2310.01613v1, Section 5.1.1, PDF pp.27–30.
The remaining inventoried nodes are explicitly deferred in the unit's HARD.md.
The accepted Register and normalizedChoi definitions are imported from the pinned
library as explicitly requested by the repair; neither is redeclared here.
Matrix integrals use the finite elementwise norm topology, as does unitaryHaar;
all displayed operator-norm bounds continue to use specNorm explicitly.
Integrability is stated for every complex matrix entry, equivalently to
Bochner integrability for these finite matrix spaces.
The reference half of a Choi state comes first. A resolved successful outcome U
is retained until the correction by (U dagger) tensor n has been applied.
-/

noncomputable section

open MeasureTheory Filter
open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Information100.P75 (Register)
open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

namespace QAlgorithms.Papers.Independent.Frontier30.P17

/-- The normalized Bell projector on A times A-prime, regrouping the m Bell
pairs with all A wires first (arXiv:2310.01613v1, PDF p.29, Eq.(87)).
Its nonzero entries are 1/d^m. Results require positive d. -/
def teleportSeed (d m : ℕ) :
    Matrix (Register (fun _ : Fin m => d) × Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d) × Register (fun _ : Fin m => d)) ℂ :=
  Matrix.of fun p q =>
    if p.1 = p.2 ∧ q.1 = q.2 then ((d : ℂ) ^ m)⁻¹ else 0

/-- Equivariance on all normalized input density matrices, with the same
unitary on every input and output qudit (arXiv:2310.01613v1, PDF p.27, Eq.(77)).
CPTP is a separate hypothesis, supplied by the accepted IsChannel predicate. -/
def IsUnitaryEquivariant {d m n : ℕ}
    (N : Superop (Register (fun _ : Fin m => d)) (Register (fun _ : Fin n => d))) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    ∀ rho : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ, IsDensityMatrix rho →
      N (piKron m (U : Matrix (Fin d) (Fin d) ℂ) * rho *
          (piKron m (U : Matrix (Fin d) (Fin d) ℂ))ᴴ) =
        piKron n (U : Matrix (Fin d) (Fin d) ℂ) * N rho *
          (piKron n (U : Matrix (Fin d) (Fin d) ℂ))ᴴ

/-- Resolved successful POVM density C M^U, relative to probability Haar
measure (arXiv:2310.01613v1, PDF p.29, Eqs.(86)–(87)). The dual factor is
entrywise conjugation, not the adjoint. -/
def conclusiveDensity (d m : ℕ) (C : ℝ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Register (fun _ : Fin m => d) × Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d) × Register (fun _ : Fin m => d)) ℂ :=
  let L := Matrix.kronecker (1 : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ)
    (piKron m ((U : Matrix (Fin d) (Fin d) ℂ).map conj))
  (C : ℂ) • (L * teleportSeed d m * Lᴴ)

/-- The coarse successful effect, used only for its probability. The quantum
protocol also keeps the resolved U for feed-forward (arXiv:2310.01613v1,
PDF p.29, Eq.(86)). The accepted Haar measure is normalized on all of U(d). -/
def conclusiveEffect (d m : ℕ) (C : ℝ) :
    Matrix (Register (fun _ : Fin m => d) × Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d) × Register (fun _ : Fin m => d)) ℂ :=
  ∫ U, conclusiveDensity d m C U ∂Schur.unitaryHaar d

/-- The actual input rho tensor J_N, reassociated as (A times A-prime) times B
so the first two registers can be measured (arXiv:2310.01613v1, PDF p.27,
Eq.(82)). Exactly one normalized Choi resource is used. -/
def inputChoi {d m n : ℕ} (N : Superop (Register (fun _ : Fin m => d)) (Register (fun _ : Fin n => d)))
    (rho : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ) :
    Matrix ((Register (fun _ : Fin m => d) × Register (fun _ : Fin m => d)) × Register (fun _ : Fin n => d))
      ((Register (fun _ : Fin m => d) × Register (fun _ : Fin m => d)) × Register (fun _ : Fin n => d)) ℂ :=
  Matrix.of fun p q =>
    rho p.1.1 q.1.1 * normalizedChoi N (p.1.2, p.2) (q.1.2, q.2)

/-- The unnormalized corrected output density for a resolved successful U.
Partial trace eliminates Alice's measured systems; Bob applies (U dagger)^n.
This is the density version of Eq.(82), including the factor C from Eq.(86)
(arXiv:2310.01613v1, PDF pp.27,29). -/
def correctedOutcome {d m n : ℕ} (C : ℝ)
    (N : Superop (Register (fun _ : Fin m => d)) (Register (fun _ : Fin n => d)))
    (rho : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Register (fun _ : Fin n => d)) (Register (fun _ : Fin n => d)) ℂ :=
  let V := piKron n (U : Matrix (Fin d) (Fin d) ℂ)
  Vᴴ * traceLeft (inputChoi N rho *
    Matrix.kronecker (conclusiveDensity d m C U)
      (1 : Matrix (Register (fun _ : Fin n => d)) (Register (fun _ : Fin n => d)) ℂ)) * V

/-- The two-wire SWAP in the word convention used for Eq.(92)
(arXiv:2310.01613v1, PDF p.29). -/
def twoSwap (d : ℕ) : Matrix (Register (fun _ : Fin 2 => d)) (Register (fun _ : Fin 2 => d)) ℂ :=
  Matrix.of fun x y => if x = (fun i => y (Fin.rev i)) then 1 else 0

/-- The normalization explicitly chosen below Eq.(92)
(arXiv:2310.01613v1, PDF p.29). Subtraction takes place in the reals. -/
def twoInputScale (d : ℕ) : ℝ := (d : ℝ) ^ 3 * ((d : ℝ) - 1) / 2

/-- The explicit Haar-integrated effect in Eq.(92), at the source's chosen C
(arXiv:2310.01613v1, PDF p.29). Results exclude d=0 and d=1. -/
def twoInputEffectFormula (d : ℕ) :
    Matrix (Register (fun _ : Fin 2 => d) × Register (fun _ : Fin 2 => d)) (Register (fun _ : Fin 2 => d) × Register (fun _ : Fin 2 => d)) ℂ :=
  ((twoInputScale d : ℂ) / ((d : ℂ) ^ 2 * ((d : ℂ) ^ 2 - 1))) •
    (1 + Matrix.kronecker (twoSwap d) (twoSwap d) -
      (d : ℂ)⁻¹ •
        (Matrix.kronecker (twoSwap d) (1 : Matrix (Register (fun _ : Fin 2 => d)) (Register (fun _ : Fin 2 => d)) ℂ) +
          Matrix.kronecker (1 : Matrix (Register (fun _ : Fin 2 => d)) (Register (fun _ : Fin 2 => d)) ℂ) (twoSwap d)))

/-- The Born success probability from Alice's reduced input, whose resource
marginal is I/d^m (arXiv:2310.01613v1, PDF p.29, Eq.(88)). -/
def conclusiveProbability {d m : ℕ} (C : ℝ)
    (rho : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ) : ℝ :=
  effectProb (conclusiveEffect d m C)
    (Matrix.kronecker rho (((d : ℂ) ^ m)⁻¹ •
      (1 : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ)))

/-- The empty tensor seed has its sole matrix entry equal to one. -/
example (d : ℕ) (x y : Register (fun _ : Fin 0 => d)) : teleportSeed d 0 (x,x) (y,y) = 1 := by
  simp [teleportSeed]

/-- Positive-dimensional Bell diagonal entries have the required factor 1/d^m. -/
example (d m : ℕ) (x y : Register (fun _ : Fin m => d)) :
    teleportSeed d m (x,x) (y,y) = ((d : ℂ) ^ m)⁻¹ := by
  simp [teleportSeed]

/-- The paper's Choi orientation: reference indices are the first pair. -/
example {d m n : ℕ} (N : Superop (Register (fun _ : Fin m => d)) (Register (fun _ : Fin n => d)))
    (a a1 : Register (fun _ : Fin m => d)) (b b1 : Register (fun _ : Fin n => d)) :
    normalizedChoi N (a,b) (a1,b1) =
      N (Matrix.single a a1 1) b b1 /
        (Fintype.card (Register (fun _ : Fin m => d)) : ℂ) := rfl

/-- At zero scale there is no successful operator density. -/
example (d m : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    conclusiveDensity d m 0 U = 0 := by
  simp [conclusiveDensity]

/-- This scale test also checks that d=1 would give zero conclusive success. -/
example : twoInputScale 2 = 4 ∧ twoInputScale 1 = 0 := by
  norm_num [twoInputScale]

/-- The empty register remains a singleton even for d=0. -/
example (d : ℕ) : Subsingleton (Register (fun _ : Fin 0 => d)) := inferInstance

/-- The identity channel satisfies the paper's full unitary-equivariance rule. -/
example (d m : ℕ) :
    IsUnitaryEquivariant (fun rho : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ => rho) := by
  intro U rho hrho
  rfl

/-- An input-Choi matrix element retains the reference coordinate in the resource. -/
example {d m n : ℕ} (N : Superop (Register (fun _ : Fin m => d)) (Register (fun _ : Fin n => d)))
    (rho : Matrix (Register (fun _ : Fin m => d)) (Register (fun _ : Fin m => d)) ℂ)
    (a r a1 r1 : Register (fun _ : Fin m => d)) (b b1 : Register (fun _ : Fin n => d)) :
    inputChoi N rho ((a,r),b) ((a1,r1),b1) =
      rho a a1 * normalizedChoi N (r,b) (r1,b1) := rfl

/-- Zero successful density integrates to the zero successful effect. -/
example (d m : ℕ) : conclusiveEffect d m 0 = 0 := by
  simp [conclusiveEffect, conclusiveDensity]

/-- On two different computational symbols the two-wire permutation swaps them. -/
example : twoSwap 2 (fun i => Fin.rev i) (fun i => i) = 1 := by
  simp [twoSwap]

end QAlgorithms.Papers.Independent.Frontier30.P17


