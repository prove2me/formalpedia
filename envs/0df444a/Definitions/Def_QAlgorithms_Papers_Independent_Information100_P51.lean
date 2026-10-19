-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P51
-- name    : QAlgorithms_Papers_Independent_Information100_P51
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:49:48.950093+00:00
-- url     : https://prove2.me/theorems/4ba11c3a-767d-4720-8e47-87db7549e444
-- title:
--   Definitions for No advantage from classical assistance for energy-constrained bosonic dephasing channels
-- statement:
--   The objects the formalized statements of *No advantage from classical assistance for energy-constrained bosonic dephasing channels* (arXiv:2610.13854) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FockMatrix`: Fock-basis coefficients of an operator on the single-mode space `l²(N; C)`. Source: arXiv:2610.13854v1, PDF pp.5–6, Eqs.(19)–(20).
--   - `IsFockTraceClass`: Trace-class coefficients through a nuclear representation: a countable sum of rank-one operators `|u_r><v_r|` with summable products of Hilbert-space norms. On a Hilbert space nuclear operators are exactly trace-class operators. Norm-product summability guarantees convergence of every coefficient series below. This representation allows arbitrary trace-class inputs, without positivity, normalization, or an energy bound. Source concept: arXiv:2610.13854v1, PDF p.3, Table 1.
--   - `FockTraceClass`: All trace-class input operators, in the fixed Fock basis (PDF p.3, Table 1).
--   - `PhaseDensity`: The phase law has a Lebesgue density on the closed interval `[-pi,pi]`. Integrability makes the defining integral genuine; singular probability laws are excluded. Source: arXiv:2610.13854v1, PDF p.5, Definition 2.8.
--   - `dephasingKernel`: The Schur kernel, with the source's negative sign and integer difference. Source: arXiv:2610.13854v1, PDF p.6, Eq.(20).
--   - `bosonicDephasing`: Coordinate action of the bosonic dephasing channel. The input and output Fock spaces are identified, exactly as on PDF p.6. This formula can be evaluated on arbitrary coefficient arrays; channel-map identities below restrict their domain to trace-class inputs. Source: arXiv:2610.13854v1, PDF p.5, Eq.(19).
--   - `fockDephasing`: Complete Fock dephasing, with the same basis at input and output. Source: arXiv:2610.13854v1, PDF p.4, Eq.(6), and p.6, Lemma 2.2.
-- source:
--   No advantage from classical assistance for energy-constrained bosonic dephasing channels, arXiv:2610.13854v1, https://arxiv.org/abs/2610.13854v1

import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

/-!
# No advantage from classical assistance for energy-constrained bosonic dephasing channels

Paper-local countable Fock coordinates for Lemma 2.2 of arXiv:2610.13854v1.
All local definitions have complete bodies; only the source theorem is admitted.
The entropy and operational capacity results are explicitly deferred in this unit's GAPS.json.
No finite-dimensional truncation of any source result is asserted.
-/

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P51

/-- Fock-basis coefficients of an operator on the single-mode space `l²(N; C)`.
Source: arXiv:2610.13854v1, PDF pp.5–6, Eqs.(19)–(20). -/
abbrev FockMatrix := ℕ → ℕ → ℂ

/-- Trace-class coefficients through a nuclear representation: a countable sum of
rank-one operators `|u_r><v_r|` with summable products of Hilbert-space norms.
On a Hilbert space nuclear operators are exactly trace-class operators. Norm-product
summability guarantees convergence of every coefficient series below. This representation
allows arbitrary trace-class inputs, without positivity, normalization, or an energy bound.
Source concept: arXiv:2610.13854v1, PDF p.3, Table 1. -/
def IsFockTraceClass (X : FockMatrix) : Prop :=
  ∃ u v : ℕ → RealRegisters.Hilbert ℕ,
    Summable (fun r => ‖u r‖ * ‖v r‖) ∧
      ∀ k l, X k l = ∑' r : ℕ, u r k * star (v r l)

/-- All trace-class input operators, in the fixed Fock basis (PDF p.3, Table 1). -/
abbrev FockTraceClass := {X : FockMatrix // IsFockTraceClass X}

/-- The phase law has a Lebesgue density on the closed interval `[-pi,pi]`.
Integrability makes the defining integral genuine; singular probability laws are excluded.
Source: arXiv:2610.13854v1, PDF p.5, Definition 2.8. -/
structure PhaseDensity where
  density : ℝ → ℝ
  nonnegative : ∀ phi ∈ Set.Icc (-Real.pi) Real.pi, 0 ≤ density phi
  integrable : IntegrableOn density (Set.Icc (-Real.pi) Real.pi)
  mass : (∫ phi in Set.Icc (-Real.pi) Real.pi, density phi) = 1

/-- The Schur kernel, with the source's negative sign and integer difference.
Source: arXiv:2610.13854v1, PDF p.6, Eq.(20). -/
def dephasingKernel (mu : PhaseDensity) (k l : ℕ) : ℂ :=
  ∫ phi in Set.Icc (-Real.pi) Real.pi,
    (mu.density phi : ℂ) *
      Complex.exp (-Complex.I * (phi : ℂ) * ((k : ℂ) - (l : ℂ)))

/-- Coordinate action of the bosonic dephasing channel. The input and output Fock
spaces are identified, exactly as on PDF p.6. This formula can be evaluated on arbitrary
coefficient arrays; channel-map identities below restrict their domain to trace-class inputs.
Source: arXiv:2610.13854v1, PDF p.5, Eq.(19). -/
def bosonicDephasing (mu : PhaseDensity) (X : FockMatrix) : FockMatrix :=
  fun k l => X k l * dephasingKernel mu k l

/-- Complete Fock dephasing, with the same basis at input and output.
Source: arXiv:2610.13854v1, PDF p.4, Eq.(6), and p.6, Lemma 2.2. -/
def fockDephasing (X : FockMatrix) : FockMatrix :=
  fun k l => if k = l then X k l else 0

/-! Sanity examples for the local definitions. -/

example : IsFockTraceClass (0 : FockMatrix) := by
  refine ⟨0, 0, ?_, ?_⟩
  · simp
  · intro k l
    simp

example (u v : RealRegisters.Hilbert ℕ) :
    IsFockTraceClass (fun k l => u k * star (v l)) := by
  refine ⟨fun r => if r = 0 then u else 0, fun r => if r = 0 then v else 0, ?_, ?_⟩
  · have heq : (fun r : ℕ => ‖if r = 0 then u else 0‖ * ‖if r = 0 then v else 0‖) =
        (fun r : ℕ => if r = 0 then ‖u‖ * ‖v‖ else 0) := by
      funext r
      split_ifs <;> simp_all
    rw [heq]
    exact (hasSum_ite_eq (0 : ℕ) (‖u‖ * ‖v‖)).summable
  · intro k l
    have heq : (fun r : ℕ => (if r = 0 then u else 0) k * star ((if r = 0 then v else 0) l)) =
        (fun r : ℕ => if r = 0 then u k * star (v l) else 0) := by
      funext r
      split_ifs <;> simp_all
    rw [heq]
    simp

example (mu : PhaseDensity) (k : ℕ) : dephasingKernel mu k k = 1 := by
  simp only [dephasingKernel, sub_self, mul_zero, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, mu.mass]
  rfl

example (mu : PhaseDensity) : bosonicDephasing mu 0 = 0 := by
  funext k l
  simp [bosonicDephasing]

example (X : FockMatrix) : fockDephasing (fockDephasing X) = fockDephasing X := by
  funext k l
  by_cases h : k = l <;> simp [fockDephasing, h]

example (X : FockMatrix) : fockDephasing X 0 1 = 0 := by
  simp [fockDephasing]

example : (-Complex.I * (1 : ℂ) * ((0 : ℂ) - (1 : ℂ))) = Complex.I := by
  ring

end QAlgorithms.Papers.Independent.Information100.P51


