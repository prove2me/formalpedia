-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WeylForU
-- name    : Formalism_PeriodIntegrals_WeylForU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:22.295212+00:00
-- url     : https://prove2.me/theorems/e4b5d6e6-62d6-4911-9512-277f72200032
-- title:
--   Weyl For U
-- statement:
--   Definitions and structural lemmas for Weyl For U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WeylForU.lean

import Definitions.Def_Formalism_PeriodIntegrals_WeylForK
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open PI.UpqRep Formalism.BasicNotions
def WeylForU : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → IsKTypeOf (allPos N) σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b), (Λ a - Λ b + ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) /
      ∏ i ∈ Finset.range N, (i.factorial : ℝ)
def NablaDim : Prop :=
  ∀ (n : ℕ) (nu : Fin n → ℕ), Antitone nu →
    (Module.finrank ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n nu) : ℚ) =
      ∏ i : Fin n, ∏ j : Fin n,
        if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1
def ModelIso : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → IsKTypeOf (allPos N) σ Λ S →
    ∃ lam : DomWeight N, (∀ a, Λ a = ((lam.w a : ℤ) : ℝ)) ∧
      Module.finrank ℂ S = Module.finrank ℂ (nablaSq ℂ N lam)
def PolyCoef : Prop :=
  ∀ (N : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → FiniteDimensional ℂ S → IsKStableOn (allPos N) σ S →
    ∀ v ∈ S, ∀ w : H, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N),
      inner ℂ w (σ g v) * g.det ^ k = MvPolynomial.eval (fun ij => g ij.1 ij.2) P
end PI


