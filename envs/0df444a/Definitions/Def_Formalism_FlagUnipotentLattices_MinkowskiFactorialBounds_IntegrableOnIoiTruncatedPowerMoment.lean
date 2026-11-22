-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:02.857627+00:00
-- url     : https://prove2.me/theorems/ac36c168-c5ae-4709-9534-f8016478e673
-- title:
--   Integrable On Ioi Truncated Power Moment
-- statement:
--   Definitions and structural lemmas for Integrable On Ioi Truncated Power Moment, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.P
section GrpL
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace
end GrpL
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GA
open Formalism.HermitianLatticeCounting.ExpansionTerms
open Finset Matrix
open scoped ComplexConjugate fwdDiff
end GA
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GG
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
end GG
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GF
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
end GF
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GH
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
def gh_G {n β K : Type*} [DecidableEq n] [Zero K] (b : n → β) (σ : n → n) (t : β → K) : Matrix n n K :=
  fun i j => if j = σ i then t (b i) else 0
section abs
variable {n β K : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [LinearOrder β] [Field K]
  {b : n → β} {σ : n → n}
end abs
lemma gh_lt {d : ℕ} (c : Composition d) (j : Fin d) :
    (j : ℕ) < c.sizeUpTo ((c.index j : ℕ) + 1) := c.lt_sizeUpTo_index_succ j
def gh_sig {d : ℕ} (c : Composition d) (i : Fin d) : Fin d :=
  ⟨c.sizeUpTo (c.index i : ℕ) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - (i : ℕ), by
    have a1 := gh_lt c i
    have a2 := c.sizeUpTo_index_le i
    have a3 := c.sizeUpTo_le ((c.index i : ℕ) + 1)
    omega⟩
end GH
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GI
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
open scoped ComplexConjugate
end GI
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GJ
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Matrix Finset
def gj_h (k r : ℕ) (p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then p i j else if i = j then 1 else 0
end GJ
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GK
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Matrix
noncomputable def gk_Q (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
  LinearMap.pi fun a =>
    if h : a.val < r then
      LinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ) (eI k r ⟨a.val, h⟩) -
        LinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ) (esI k r ⟨a.val, h⟩)
    else LinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ) ⟨r + k, by omega⟩
noncomputable def gk_E (r : ℕ) : (Option (Fin (r + 1)) → ℂ) →ₗ[ℂ] (Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :=
  LinearMap.pi fun i =>
    Sum.elim (fun a => LinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin (r + 1)) => ℂ) (some a)) (fun _ => 0) i
end GK
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GD
open Formalism.HermitianLatticeCounting.ExpansionTerms
open Finset Matrix Polynomial
open scoped ComplexConjugate TensorProduct
end GD
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GE
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix Polynomial
open scoped ComplexConjugate
end GE
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GB
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate
end GB
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
section GC
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
noncomputable def gramSchmidtUnitriangularMatrix {l : ℕ} (y : Fin l → V) : Matrix (Fin l) (Fin l) ℂ := fun a b =>
  if b = a then 1 else if b < a then
    inner ℂ (gramSchmidt ℂ y b) (y a) / ((‖gramSchmidt ℂ y b‖ : ℂ)) ^ 2 else 0
end GC
end Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
end Formalism.HermitianLatticeCounting.P


