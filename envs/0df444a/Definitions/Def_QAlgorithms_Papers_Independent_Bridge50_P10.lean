-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P10
-- name    : QAlgorithms_Papers_Independent_Bridge50_P10
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:21:48.755052+00:00
-- url     : https://prove2.me/theorems/524ffc7f-d251-4d1f-97c8-ee3944837144
-- title:
--   Definitions for Bosonic data hiding: power of linear vs non-linear optics
-- statement:
--   The objects the formalized statements of *Bosonic data hiding: power of linear vs non-linear optics* (arXiv:2102.01622) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sourceDisplacement`: PDF pp.2–3, (6),(8),(10): the displacement D((x+ip)/sqrt(2)). The accepted Weyl system's argument xi has D(-xi_p+i xi_x), so the conversion below fixes hbar=1 and vacuum quadrature covariance I/2. Its coefficients specify the actual full Fock representation, not a free oracle.
--   - `multimodeParitySymbol`: PDF p.3, (10): Wigner function as the displaced-parity trace, expanded in the complete number basis. For every trace-class argument the signed series is absolutely convergent, since displacement is unitary. Taking its real part agrees with the real Wigner function on self-adjoint arguments. There is no Fourier-integrability restriction or photon cutoff. The frozen Claimed50.P37.wigner instead takes coefficient matrices and uses a complex Bochner Fourier integral, with a Gaussian/integrable usage domain. It cannot supply this real, all-trace-class operator symbol. Gap48.P30 supplies only a one-mode complex-coordinate parity symbol. This multimode extension keeps the source normalization rather than changing either frozen interface.
--   - `HasBoundedResponse`: PDF pp.3–5, (11),(22): bounded real Weyl response F=(2 pi)^m W_M, characterized by the weak trace pairing on ALL self-adjoint trace-class tests whose Wigner function is L1. This is a definition of the actual symbol of M, not a pairing assumption imposed only on the pair in a target theorem. Non-L1 tests are omitted from this defining integral identity, never from the domain of the theorem. Bounded measurable symbols are identified a.e.
--   - `IsWPlus`: PDF pp.4–5, (20),(22): BOTH effects have nonnegative Wigner symbols. The common response F lies in [0,1], and the complementary effect has the actual response 1-F. This is not a positivity assumption on the input states.
--   - `wPlusDistance`: PDF pp.4–5, (20),(22): twice the optimal equal-prior trace bias. On states the real supremum is bounded by 1 before the outer factor 2. Zero is an allowed bias (e.g. a constant decision); inserting it explicitly makes nonemptiness transparent and leaves the physical optimum unchanged. This is a distance on state pairs, not a complex operator-space norm.
--   - `wignerL1`: PDF p.5, Lemma 3 and Remark 4: extended L1 Wigner size, with ordinary Lebesgue measure d^m x d^m p. Infinity is retained for nonintegrable Wigner functions, instead of a divergent Bochner integral returning zero.
-- source:
--   Bosonic data hiding: power of linear vs non-linear optics, arXiv:2102.01622v1, https://arxiv.org/abs/2102.01622v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

/-!
arXiv:2102.01622v1, bounded Wigner responses and unrestricted-input W+ lower bound.
The full completed number-space, positive trace-class states, basis trace, and
coefficient-pinned Weyl operators are accepted interfaces. Only the source's
hbar=1 coordinate conversion and bounded real Weyl responses are introduced here.
GOCC-dependent nodes and the ambiguous Corollary 12 are explicitly deferred.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P10

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeOperator PhaseVector FockWeylSystem numberBasis numberKet)
open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass operatorTrace State)
open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

/-- PDF pp.2–3, (6),(8),(10): the displacement D((x+ip)/sqrt(2)).
The accepted Weyl system's argument xi has D(-xi_p+i xi_x), so the
conversion below fixes hbar=1 and vacuum quadrature covariance I/2.
Its coefficients specify the actual full Fock representation, not a free oracle. -/
def sourceDisplacement {m : ℕ} (W : FockWeylSystem m) (z : PhaseVector m) :
    ModeOperator m :=
  W.operator (fun j => if j.2 = 0 then z (j.1, 1) / Real.sqrt 2
    else -z (j.1, 0) / Real.sqrt 2)

/-- PDF p.3, (10): Wigner function as the displaced-parity trace, expanded
in the complete number basis. For every trace-class argument the signed
series is absolutely convergent, since displacement is unitary. Taking its
real part agrees with the real Wigner function on self-adjoint arguments.
There is no Fourier-integrability restriction or photon cutoff.
The frozen Claimed50.P37.wigner instead takes coefficient matrices and uses a
complex Bochner Fourier integral, with a Gaussian/integrable usage domain.
It cannot supply this real, all-trace-class operator symbol. Gap48.P30 supplies
only a one-mode complex-coordinate parity symbol. This multimode extension
keeps the source normalization rather than changing either frozen interface. -/
def multimodeParitySymbol {m : ℕ} (W : FockWeylSystem m) (T : ModeOperator m)
    (z : PhaseVector m) : ℝ :=
  (Real.pi ^ m)⁻¹ * ∑' k : Fin m → ℕ,
    (-1 : ℝ) ^ (∑ j, k j) *
      (inner ℂ (sourceDisplacement W z (numberKet k))
        (T (sourceDisplacement W z (numberKet k)))).re

/-- PDF pp.3–5, (11),(22): bounded real Weyl response F=(2 pi)^m W_M,
characterized by the weak trace pairing on ALL self-adjoint trace-class tests
whose Wigner function is L1. This is a definition of the actual symbol of M,
not a pairing assumption imposed only on the pair in a target theorem.
Non-L1 tests are omitted from this defining integral identity, never from
the domain of the theorem. Bounded measurable symbols are identified a.e. -/
def HasBoundedResponse {m : ℕ} (W : FockWeylSystem m)
    (M : ModeOperator m) (F : PhaseVector m → ℝ) : Prop :=
  Measurable F ∧ (∃ C : ℝ, ∀ z, |F z| ≤ C) ∧
    ∀ T : ModeOperator m, IsTraceClass T → T.adjoint = T →
      Integrable (multimodeParitySymbol W T) →
      (operatorTrace (numberBasis m) (T.comp M)).re =
        ∫ z : PhaseVector m, multimodeParitySymbol W T z * F z

/-- PDF pp.4–5, (20),(22): BOTH effects have nonnegative Wigner symbols.
The common response F lies in [0,1], and the complementary effect has the
actual response 1-F. This is not a positivity assumption on the input states. -/
def IsWPlus {m : ℕ} (W : FockWeylSystem m) (M : ModeOperator m) : Prop :=
  IsBinaryEffect M ∧ ∃ F : PhaseVector m → ℝ,
    HasBoundedResponse W M F ∧
    HasBoundedResponse W (1 - M) (fun z => 1 - F z) ∧
    ∀ z, 0 ≤ F z ∧ F z ≤ 1

/-- PDF pp.4–5, (20),(22): twice the optimal equal-prior trace bias.
On states the real supremum is bounded by 1 before the outer factor 2.
Zero is an allowed bias (e.g. a constant decision); inserting it explicitly
makes nonemptiness transparent and leaves the physical optimum unchanged.
This is a distance on state pairs, not a complex operator-space norm. -/
def wPlusDistance {m : ℕ} (W : FockWeylSystem m)
    (rho0 rho1 : State (numberBasis m)) : ℝ :=
  2 * sSup (insert 0 {a : ℝ | ∃ M : ModeOperator m,
    IsWPlus W M ∧ a =
      (operatorTrace (numberBasis m) ((rho0.val.val - rho1.val.val).comp M)).re})

/-- PDF p.5, Lemma 3 and Remark 4: extended L1 Wigner size, with ordinary
Lebesgue measure d^m x d^m p. Infinity is retained for nonintegrable Wigner
functions, instead of a divergent Bochner integral returning zero. -/
def wignerL1 {m : ℕ} (W : FockWeylSystem m) (T : ModeOperator m) : ℝ≥0∞ :=
  ∫⁻ z : PhaseVector m, ENNReal.ofReal (|multimodeParitySymbol W T z|)

example {m : ℕ} (W : FockWeylSystem m) :
    sourceDisplacement W 0 = W.operator 0 := by
  unfold sourceDisplacement
  apply congrArg W.operator
  funext j
  simp

example {m : ℕ} (W : FockWeylSystem m) (z : PhaseVector m) :
    multimodeParitySymbol W 0 z = 0 := by
  simp [multimodeParitySymbol]

example {m : ℕ} (W : FockWeylSystem m) : wignerL1 W 0 = 0 := by
  simp [wignerL1, multimodeParitySymbol]

example {m : ℕ} (W : FockWeylSystem m) :
    HasBoundedResponse W 0 (fun _ => 0) := by
  refine ⟨measurable_const, ⟨0, fun z => by simp⟩, ?_⟩
  intro T hT hself hInt
  simp [operatorTrace]

example : ((2 : ℝ) ^ (1 + 1))⁻¹ = 1 / 4 := by
  norm_num

end QAlgorithms.Papers.Independent.Bridge50.P10


