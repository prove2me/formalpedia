-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:22.36513+00:00
-- url     : https://prove2.me/theorems/9520890e-277b-496c-a0f1-95ec5d99c46b
-- title:
--   Iwa Core
-- statement:
--   Definitions and structural lemmas for Iwa Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder MatrixOrder
variable {n : ℕ}
def dp (p : Fin n → Fin n) (α β : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (if j = i then α i else 0) + (if j = p i then β i else 0)
structure Adapted (p : Fin n → Fin n) (b : Fin n → ℤ) (c : Fin n → ℂ) : Prop where
  invol : ∀ i, p (p i) = i
  mono : Monotone b
  neg : ∀ i, b (p i) = -b i
  fix : ∀ i, b i = 0 → p i = i
  inj : ∀ i j, b i ≠ 0 → b i = b j → i = j
  sq : ∀ i, c i * c i = 1
  star_eq : ∀ i, star (c i) = c i
  symm : ∀ i, c (p i) = c i
  mid : ∀ i j, b i = 0 → b j = 0 → c i = c j
variable {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ}
def Dec (H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * H * g = H →
    ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ s : Matrix (Fin n) (Fin n) ℂ, kᴴ * H * k = H ∧ sᴴ * H * s = H ∧
      g = k * s ∧ (Uᴴ * s * U).BlockTriangular id
end CompanionTheory.D.gk.admitted.CholeskyDecomposition


