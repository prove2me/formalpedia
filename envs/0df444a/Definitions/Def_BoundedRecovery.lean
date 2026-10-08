-- Prove2me | Definitions.Def_BoundedRecovery
-- name    : BoundedRecovery
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.416601+00:00
-- url     : https://prove2.me/theorems/1ef9e146-2292-4f6a-bcd7-484c87b072a3
-- statement:
--   For a complex Hilbert space H, a real spectral calculus is a complex star-algebra homomorphism Φ from bounded continuous complex-valued functions on ℝ to bounded linear operators on H, with the vectors Φ(f)k for compactly supported f dense in H. Set Uₜ=Φ(u↦exp(itu)); define the half-exponential graph to consist of pairs (h,q) for which Φ(u↦exp(min(n,u)/2))h converges in norm to q as n tends to infinity. A vector h has spectral support in I if Φ(f)h=0 for every bounded continuous f vanishing on I. Standard modular data consist of a von Neumann algebra M on H, a unit vector ξ cyclic and separating for M, such a spectral calculus, and an involutive conjugate-linear isometric equivalence J of H. These data are required to satisfy the closed Tomita graph identity: the closure of {(aξ,a*ξ):a∈M} equals {(h,Jq):(h,q) belongs to the half-exponential graph}. Here cyclicity means Mξ is dense, and separation means aξ=0 with a∈M forces a=0. Define σₜ(a)=UₜaU₋ₜ; the scalar-centralizer proposition says every a∈M fixed by all σₜ is a complex scalar multiple of the identity. For real-valued f, its kth symmetric average is (2k)⁻¹∫₋ₖᵏf(t)dt, and its fixed mean relative to an arbitrary ultrafilter on ℕ is the formal filter limit of these averages, without an asserted convergence hypothesis. Finally, for a bounded complex-linear operator T, s∈ℝ and any sequence δ:ℕ→ℝ, the defined recovery conclusion requires a strictly increasing sequence nⱼ, operators vⱼ∈M, and real constants C and η>0 such that, for every j, ‖vⱼ‖≤C, ‖T(vⱼξ)‖≥η, and vⱼξ has spectral support in [s−4δ(nⱼ),s+4δ(nⱼ)]. No positivity or convergence condition on δ is built into this proposition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BoundedRecovery.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BoundedRecovery.lean; bytes 16..3457
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Nondegenerate spectral calculus, the closed Tomita graph, and bounded recovery. -/

universe u

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralCharacter (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I))
    (by fun_prop) 1 (by intro u; simp [Complex.norm_exp])

def halfExponentialCutoff (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (min (n : ℝ) u / 2) : ℂ))
    (by fun_prop) (Real.exp ((n : ℝ) / 2)) (by
      intro u
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))

structure RealSpectralCalculus (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  calculus : (BoundedContinuousFunction ℝ ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)
  nondegenerate : Dense {h : H | ∃ f : BoundedContinuousFunction ℝ ℂ,
    HasCompactSupport (f : ℝ → ℂ) ∧ ∃ k : H, calculus f k = h}

namespace RealSpectralCalculus

def unitary (D : RealSpectralCalculus H) (t : ℝ) : H →L[ℂ] H :=
  D.calculus (spectralCharacter t)

def halfGraph (D : RealSpectralCalculus H) : Set (H × H) :=
  {p | Tendsto (fun n : ℕ => D.calculus (halfExponentialCutoff n) p.1) atTop (𝓝 p.2)}

def HasSpectralSupport (D : RealSpectralCalculus H) (I : Set ℝ) (h : H) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℂ, (∀ u ∈ I, f u = 0) → D.calculus f h = 0

end RealSpectralCalculus

structure StandardModularData (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  M : VonNeumannAlgebra H
  xi : H
  norm_xi : ‖xi‖ = 1
  cyclic : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h}
  separating : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0
  D : RealSpectralCalculus H
  J : H ≃ₗᵢ⋆[ℂ] H
  conjugation : Function.Involutive J
  tomita_graph : closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ M ∧ p = (a xi, (star a) xi)} =
    {p | ∃ q : H, (p.1, q) ∈ D.halfGraph ∧ p.2 = J q}

namespace StandardModularData

def sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  S.D.unitary t * a * S.D.unitary (-t)

def ScalarCentralizer (S : StandardModularData H) : Prop :=
  ∀ a : H →L[ℂ] H, a ∈ S.M → (∀ t : ℝ, S.sigma t a = a) →
    ∃ c : ℂ, a = c • (1 : H →L[ℂ] H)

end StandardModularData

def symmetricAverage (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (2 * (k : ℝ))⁻¹ * ∫ t in -(k : ℝ)..(k : ℝ), f t

def fixedMean (omega : Ultrafilter ℕ) (f : ℝ → ℝ) : ℝ :=
  Filter.limUnder (omega : Filter ℕ) (symmetricAverage f)

def RecoveryConclusion (S : StandardModularData H) (T : H →L[ℂ] H)
    (s : ℝ) (delta : ℕ → ℝ) : Prop :=
  ∃ (nj : ℕ → ℕ) (_ : StrictMono nj) (v : ℕ → (H →L[ℂ] H)) (C eta : ℝ),
    0 < eta ∧ ∀ j : ℕ, v j ∈ S.M ∧ ‖v j‖ ≤ C ∧ eta ≤ ‖T (v j S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s - 4 * delta (nj j)) (s + 4 * delta (nj j)))
        (v j S.xi)



end BoundedRecovery
end
end OAI


