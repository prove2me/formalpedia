-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P25
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P25
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:27:02.186224+00:00
-- url     : https://prove2.me/theorems/97106f07-23c3-4f3a-b5ab-7714b75ad071
-- title:
--   Definitions for On completion of the cone of CP linear maps with respect to the energy-constrained diamond norm
-- statement:
--   The objects the formalized statements of *On completion of the cone of CP linear maps with respect to the energy-constrained diamond norm* (arXiv:1810.10922) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `EnergyObservable`: PDF pp.3–4, (5)–(6): an energy observable is encoded by its positive self-adjoint square root S, so G = S squared on its natural composition domain. Every positive self-adjoint G is represented by S = sqrt(G), and conversely. The final field says that the spectral bottom of S is zero; by spectral mapping this is exactly (5) for G. It does not require an actual zero eigenvector. No discrete-spectrum or boundedness assumption is imposed.
--   - `RelativelyBounded`: PDF p.4, (6): a linear operator defined precisely on D(sqrt(G)). It need not be closable and is not required to possess a densely defined adjoint. Equality of these linear maps is exactly the identification on that domain.
--   - `SqrtEnergyInfinitesimal`: PDF p.4, following (6): relative sqrt(G)-bound zero, with every positive candidate bound allowed. The coefficient a may depend on b, but not on x. This differs from Frontier30.P20.Infinitesimal (channel divisibility).
--   - `EnergyAdmissible`: PDF p.5, (11): countable, possibly subnormalized ensembles with energy at most E. Infinite sums are extended nonnegative sums, retaining divergence. This is the paper's mixed-state formula, not its discrete-only formula (13).
--   - `operatorEnergyMass`: PDF pp.4–5, (9),(11): squared operator E-norm via the equivalent countable-ensemble formula (11). It is finite for relatively bounded V and E>0. The extended supremum has no unbounded-real-supremum default.
--   - `operatorEnergyNorm`: PDF p.5, (11): the nonnegative square root of the preceding mass. On the theorem's relatively bounded domain this is the actual finite E-norm, embedded in the extended nonnegative reals, with no conversion of infinity to 0.
--   - `familyEnergyMass`: PDF p.17, (42): the supremum of the SUM of the output traces, with no square root. Ensemble decomposition and nonnegative Tonelli summation give exactly (42). By (5), trace-at-most-one ensembles have the same supremum as normalized states. K may be finite or countably infinite; divergence is infinity.
--   - `FamilySublinear`: PDF p.17, (43): the aggregate mass is o(E). Every positive epsilon has one eventual threshold uniform over all subsequent positive energies. This also forces finiteness at each positive energy by monotonicity.
--   - `tensorBra`: PDF p.18, (46): the bra of the simple tensor psi tensor tau evaluated on z in the COMPLETED product Hilbert space l2(N times K). The double scalar series is absolutely convergent by Cauchy–Schwarz for all three Hilbert vectors. Complex conjugation acts on the bra, in agreement with Mathlib's inner product.
-- source:
--   On completion of the cone of CP linear maps with respect to the energy-constrained diamond norm, arXiv:1810.10922v2, https://arxiv.org/abs/1810.10922v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

/-!
Paper: M. E. Shirokov, arXiv:1810.10922v2.
The system carriers are full separable infinite-dimensional complex Hilbert spaces
in countable orthonormal coordinates. The environment has any countable basis.
Only Lemma 7 and Remark 2 are drafted. Other planned results are individually
accounted for in HARD.md and GAPS.json; no map-completion result is assumed here.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakenext100.P25

open QAlgorithms.RealRegisters (Hilbert)

/-- PDF pp.3–4, (5)–(6): an energy observable is encoded by its positive
self-adjoint square root S, so G = S squared on its natural composition domain.
Every positive self-adjoint G is represented by S = sqrt(G), and conversely.
The final field says that the spectral bottom of S is zero; by spectral mapping
this is exactly (5) for G. It does not require an actual zero eigenvector.
No discrete-spectrum or boundedness assumption is imposed. -/
structure EnergyObservable where
  root : Hilbert ℕ →ₗ.[ℂ] Hilbert ℕ
  selfAdjoint : IsSelfAdjoint root
  positive : ∀ x : root.domain, 0 ≤ (inner ℂ (x : Hilbert ℕ) (root x)).re
  bottomZero : ∀ epsilon : ℝ, 0 < epsilon →
    ∃ x : root.domain, ‖(x : Hilbert ℕ)‖ = 1 ∧ ‖root x‖ < epsilon

/-- PDF p.4, (6): a linear operator defined precisely on D(sqrt(G)).
It need not be closable and is not required to possess a densely defined adjoint.
Equality of these linear maps is exactly the identification on that domain. -/
def RelativelyBounded {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (G : EnergyObservable) (V : G.root.domain →ₗ[ℂ] H) : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧ ∃ b : ℝ, 0 ≤ b ∧
    ∀ x : G.root.domain,
      ‖V x‖ ^ 2 ≤ a ^ 2 * ‖(x : Hilbert ℕ)‖ ^ 2 + b ^ 2 * ‖G.root x‖ ^ 2

/-- PDF p.4, following (6): relative sqrt(G)-bound zero, with every positive
candidate bound allowed. The coefficient a may depend on b, but not on x.
This differs from Frontier30.P20.Infinitesimal (channel divisibility). -/
def SqrtEnergyInfinitesimal {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (G : EnergyObservable) (V : G.root.domain →ₗ[ℂ] H) : Prop :=
  ∀ b : ℝ, 0 < b → ∃ a : ℝ, 0 ≤ a ∧
    ∀ x : G.root.domain,
      ‖V x‖ ^ 2 ≤ a ^ 2 * ‖(x : Hilbert ℕ)‖ ^ 2 + b ^ 2 * ‖G.root x‖ ^ 2

/-- PDF p.5, (11): countable, possibly subnormalized ensembles with energy at
most E. Infinite sums are extended nonnegative sums, retaining divergence.
This is the paper's mixed-state formula, not its discrete-only formula (13). -/
def EnergyAdmissible (G : EnergyObservable) (E : ℝ)
    (u : ℕ → G.root.domain) : Prop :=
  (∑' n : ℕ, ENNReal.ofReal (‖(u n : Hilbert ℕ)‖ ^ 2)) ≤ 1 ∧
    (∑' n : ℕ, ENNReal.ofReal (‖G.root (u n)‖ ^ 2)) ≤ ENNReal.ofReal E

/-- PDF pp.4–5, (9),(11): squared operator E-norm via the equivalent
countable-ensemble formula (11). It is finite for relatively bounded V and E>0.
The extended supremum has no unbounded-real-supremum default. -/
def operatorEnergyMass {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (G : EnergyObservable) (V : G.root.domain →ₗ[ℂ] H) (E : ℝ) : ℝ≥0∞ :=
  ⨆ u : {u : ℕ → G.root.domain // EnergyAdmissible G E u},
    ∑' n : ℕ, ENNReal.ofReal (‖V (u.val n)‖ ^ 2)

/-- PDF p.5, (11): the nonnegative square root of the preceding mass.
On the theorem's relatively bounded domain this is the actual finite E-norm,
embedded in the extended nonnegative reals, with no conversion of infinity to 0. -/
def operatorEnergyNorm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (G : EnergyObservable) (V : G.root.domain →ₗ[ℂ] H) (E : ℝ) : ℝ≥0∞ :=
  (operatorEnergyMass G V E) ^ (1 / 2 : ℝ)

/-- PDF p.17, (42): the supremum of the SUM of the output traces, with no
square root. Ensemble decomposition and nonnegative Tonelli summation give
exactly (42). By (5), trace-at-most-one ensembles have the same supremum as
normalized states. K may be finite or countably infinite; divergence is infinity. -/
def familyEnergyMass {K : Type*} [Countable K] (G : EnergyObservable)
    (V : K → (G.root.domain →ₗ[ℂ] Hilbert ℕ)) (E : ℝ) : ℝ≥0∞ :=
  ⨆ u : {u : ℕ → G.root.domain // EnergyAdmissible G E u},
    ∑' k : K, ∑' n : ℕ, ENNReal.ofReal (‖V k (u.val n)‖ ^ 2)

/-- PDF p.17, (43): the aggregate mass is o(E). Every positive epsilon has
one eventual threshold uniform over all subsequent positive energies. This also
forces finiteness at each positive energy by monotonicity. -/
def FamilySublinear {K : Type*} [Countable K] (G : EnergyObservable)
    (V : K → (G.root.domain →ₗ[ℂ] Hilbert ℕ)) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ E0 : ℝ, 0 < E0 ∧
    ∀ E : ℝ, E0 ≤ E → familyEnergyMass G V E ≤ ENNReal.ofReal (epsilon * E)

/-- PDF p.18, (46): the bra of the simple tensor psi tensor tau evaluated on z
in the COMPLETED product Hilbert space l2(N times K). The double scalar series
is absolutely convergent by Cauchy–Schwarz for all three Hilbert vectors.
Complex conjugation acts on the bra, in agreement with Mathlib's inner product. -/
def tensorBra {K : Type*} [Countable K] (psi : Hilbert ℕ) (tau : Hilbert K)
    (z : Hilbert (ℕ × K)) : ℂ :=
  ∑' b : ℕ, ∑' e : K, star (psi b * tau e) * z (b, e)

example (G : EnergyObservable) :
    RelativelyBounded G (0 : G.root.domain →ₗ[ℂ] Hilbert ℕ) := by
  refine ⟨0, le_rfl, 0, le_rfl, ?_⟩
  intro x
  simp

example (G : EnergyObservable) :
    SqrtEnergyInfinitesimal G (0 : G.root.domain →ₗ[ℂ] Hilbert ℕ) := by
  intro b hb
  refine ⟨0, le_rfl, ?_⟩
  intro x
  simpa using mul_nonneg (sq_nonneg b) (sq_nonneg ‖G.root x‖)

example (G : EnergyObservable) (E : ℝ) :
    operatorEnergyMass G (0 : G.root.domain →ₗ[ℂ] Hilbert ℕ) E = 0 := by
  simp [operatorEnergyMass]

example {K : Type*} [Countable K] (G : EnergyObservable) (E : ℝ) :
    familyEnergyMass G (fun _ : K => (0 : G.root.domain →ₗ[ℂ] Hilbert ℕ)) E = 0 := by
  simp [familyEnergyMass]

example {K : Type*} [Countable K] (psi : Hilbert ℕ) (tau : Hilbert K) :
    tensorBra psi tau (0 : Hilbert (ℕ × K)) = 0 := by
  simp [tensorBra]

end QAlgorithms.Papers.Independent.Intakenext100.P25


