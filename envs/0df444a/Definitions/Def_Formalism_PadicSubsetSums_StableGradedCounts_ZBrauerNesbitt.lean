-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:11.612116+00:00
-- url     : https://prove2.me/theorems/aee938b4-ccbb-4950-80bd-b391f42cfe50
-- title:
--   ZBrauer Nesbitt
-- statement:
--   Definitions and structural lemmas for ZBrauer Nesbitt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.Z.BN
def simpleCps (k A : Type) [Field k] [Ring A] [Algebra k A] : Set (A → k[X]) :=
  {F | ∃ (S : Type) (_ : AddCommGroup S) (_ : Module k S) (_ : Module A S)
    (_ : IsScalarTower k A S) (_ : FiniteDimensional k S) (_ : IsSimpleModule A S), F = cp k S}
theorem nextCoeff_cp {k A : Type} [Field k] [Ring A] [Algebra k A] (V : Type) [AddCommGroup V]
    [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V] (a : A) :
    (cp k V a).nextCoeff = - LinearMap.trace k V (Algebra.lsmul k k V a) := by
  unfold cp
  rw [← LinearMap.charpoly_toMatrix _ (Module.Free.chooseBasis k V),
    LinearMap.trace_eq_matrix_trace k (Module.Free.chooseBasis k V),
    Matrix.trace_eq_neg_charpoly_nextCoeff, neg_neg]
def Kills {K A : Type} [Field K] [Ring A] [Algebra K A] (t : Finset (A → K[X])) (a : A) : Prop :=
  ∀ F ∈ t, ∃ (S : Type) (_ : AddCommGroup S) (_ : Module K S) (_ : Module A S)
    (_ : IsScalarTower K A S) (_ : FiniteDimensional K S), F = cp K S ∧ ∀ s : S, a • s = 0
theorem Kills.nextCoeff {K A : Type} [Field K] [Ring A] [Algebra K A] {t : Finset (A → K[X])}
    {a : A} (h : Kills t a) {F : A → K[X]} (hF : F ∈ t) : (F a).nextCoeff = 0 := by
  obtain ⟨S, _, _, _, _, _, rfl, hS⟩ := h F hF
  rw [nextCoeff_cp]
  have : Algebra.lsmul K K S a = 0 := by
    ext s
    simpa using hS s
  rw [this]; simp
section group
open TensorProduct
variable {k G V W : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
def bc (K : Type) [Field K] [Algebra k K] (ρ : Representation k G V) :
    Representation K G (K ⊗[k] V) where
  toFun g := (ρ g).baseChange K
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Module.End.mul_eq_comp, LinearMap.baseChange_comp]
end group
end Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z
end Formalism.IrreducibleCountingLemmas.Z


