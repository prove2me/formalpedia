-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_MinimizingFamily
-- name    : OAI_Analysis_Littlewood_MinimizingFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:38:25.866012+00:00
-- url     : https://prove2.me/theorems/b74f7677-e667-4913-b3a9-14df0e58a438
-- title:
--   Sup-norm minimizing Littlewood polynomials of every length
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ with normalized Haar measure $\mu$, and $e_k(t)=e^{2\pi ikt}$.
--
--   1. For signs $b\in\{\pm1\}^N$ (encoded as Booleans), the circle polynomial is
--   $$
--   P_b(t)=\sum_{k=0}^{N-1}b_k\,e_k(t),
--   $$
--      a continuous function on $\mathbb{T}$ with sup norm $\|P_b\|_\infty$.
--   2. Among the finitely many sign vectors of length $N$ there is one minimizing $\|P_b\|_\infty$; the chosen signs $\varepsilon_N$ are such a minimizer.
--   3. The normalized modulus is $f_N(t)=|P_{\varepsilon_N}(t)|/\sqrt N$.
--
--   Choosing the sup-norm minimizer at every length gives one sign family that works for all exponents at once. Ultraflat-type upper bounds then transfer to it automatically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/MinimizingFamily.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/MinimizingFamily.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LittlewoodFiniteFlatness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LittlewoodFiniteFlatness

namespace OAI

/-! A minimizing family with vanishing second error moment. -/
noncomputable section
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate

namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

def boolSign (b : Bool) : ℝ := if b then 1 else -1

abbrev μ : Measure UnitAddCircle := AddCircle.haarAddCircle

def circlePolynomial {N : ℕ} (ε : Fin N → ℝ) : C(UnitAddCircle, ℂ) :=
  ∑ k : Fin N, (ε k : ℂ) • fourier (k : ℤ)

def signVector {N : ℕ} (b : Fin N → Bool) : Fin N → ℝ := fun k => boolSign (b k)

lemma exists_minimizing_signing (N : ℕ) :
    ∃ b : Fin N → Bool, ∀ c : Fin N → Bool,
      ‖circlePolynomial (signVector b)‖ ≤ ‖circlePolynomial (signVector c)‖ := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N → Bool))
    (fun b => ‖circlePolynomial (signVector b)‖) Finset.univ_nonempty
  exact ⟨b, fun c => hb c (Finset.mem_univ c)⟩

def minimizingBits (N : ℕ) : Fin N → Bool := Classical.choose (exists_minimizing_signing N)
def chosenSigns (N : ℕ) : Fin N → ℝ := signVector (minimizingBits N)

/- An all-length upper-flatness bound for real-sign polynomials. -/
variable (hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
  ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N)

def normalized (N : ℕ) (t : UnitAddCircle) : ℝ :=
  ‖circlePolynomial (chosenSigns N) t‖ / Real.sqrt (N : ℝ)

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end

end OAI


