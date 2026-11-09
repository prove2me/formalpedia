-- Prove2me | Definitions.Def_ChapterFockStatisticsCompletion
-- name    : ChapterFockStatisticsCompletion
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T20:18:13.021218+00:00
-- url     : https://prove2.me/theorems/783167bd-5cec-4791-95c4-b7a1d804218a
-- title:
--   The Lean 4 theorem `norm_act` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFockStatisticsCompletion.lean`): generated def bundle for ChapterFockStatisticsCompletion. See BookProof/ChapterFockStatisticsCompletion.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockStatisticsCompletion.lean

import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem

import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj

import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_mem_range_avgProj_iff

import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorDom

import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_isReducingProjection_avgProj

import Theorems.Thm_BookProof_PermSector_signRep_mem_sectorDom

import Theorems.Thm_BookProof_GraphCore_pushOp_apply

import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorDom




import Theorems.Thm_BookProof_PermSector_signRep_commutes_sectorDom


import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_mul

import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_one



import Definitions.Def_ChapterFockStatisticsEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
import Theorems.Thm_BookProof_GraphCore_symmetricOn_pushOp
import Theorems.Thm_BookProof_ReducedEsa_essentiallySelfAdjointOn_red
import Theorems.Thm_BookProof_ReducedEsa_symmetricOn_redOp
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Theorems.Thm_BookProof_TensorCore_symmetricOn_sectorOp
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_apply
-- The non-vacuity witness is a PROVED node: the served Def_ChapterPermutationSectorEsa
-- is a 195-line skeleton (Good/bosonicProj/fermionicProj only), so its theorems are not
-- on the platform's import path even though the workspace bundle declares them.
import Theorems.Thm_BookProof_PermSector_exists_ne_zero_bosonic
import Theorems.Thm_BookProof_PermSector_exists_ne_zero_fermionic


/-!
# The Hilbert bosonic and fermionic Fock space

`BookProof.FockStatistics` works inside the *algebraic* tensor powers `H^{⊗n}`.  This module
repeats the construction inside their **completions** — the `n`-particle sectors
`fockSector Hs n` of `BookProof.SecondQuantizationCore` — so that the symmetric and the
antisymmetric Fock space obtained by summing over the particle number are genuine Hilbert
spaces.

## What is proved

* `UnitaryRep.completionRep` — a unitary representation of a finite group on an inner
  product space extends to its completion, with `completionRep_act_coe` the compatibility
  with the canonical embedding; `isClosed_sector_avgProj` — the invariant sector of the
  extended representation is closed, hence complete.
* `cpermRep`, `csignRep`, `cbosonicProj`, `cfermionicProj` — the permutation action, its sign
  twist and the two averages on the completed sector `fockSector Hs n`;
  `mem_cbosonicSector_iff`, `mem_cfermionicSector_iff`, and `cbosonicProj_sectorEmb` /
  `cfermionicProj_sectorEmb`: the completed projections extend the algebraic ones.
* `essentiallySelfAdjointOn_cbosonic`, `essentiallySelfAdjointOn_cfermionic` — `dΓ(A)⁽ⁿ⁾` is
  essentially self-adjoint on the symmetric and on the antisymmetric part of the *complete*
  `n`-particle sector, for a symmetric essentially self-adjoint one-particle operator.
* `hbosonicFock`, `hfermionicFock` — the two Hilbert Fock spaces (`CompleteSpace` instances
  included), `hbosonicFockDom` / `hbosonicFockOp` and their fermionic twins, and the headline
  **`hbosonicFock_esa`** / **`hfermionicFock_esa`**: `dΓ(A)` is essentially self-adjoint on
  the symmetric, respectively the antisymmetric, Fock space over `H`, with
  `hbosonicFock_symmetricOn` / `hfermionicFock_symmetricOn` the symmetry statements.
* `exists_ne_zero_cbosonic`, `exists_ne_zero_cfermionic`, `exists_ne_zero_hbosonicFockDom`,
  `exists_ne_zero_hfermionicFockDom` — non-vacuity: the `n`-th power of a nonzero vector of
  the one-particle domain and the Slater determinant of `n` pairwise orthogonal ones survive
  in the completed sectors and in the two Fock domains.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.GroupAverage.UnitaryRep

open BookProof.GroupAverage BookProof.ReducedEsa

noncomputable section

/-! ## 1. A unitary representation extends to the completion -/

section CompletionRep

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]



omit [Fintype G] in
/-- Every operator of a unitary representation is an isometry. -/
theorem norm_act (rep : UnitaryRep G F) (g : G) (x : F) : ‖rep.act g x‖ = ‖x‖ := by
  have h := rep.act_inner g x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖rep.act g x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (rep.act g x), norm_nonneg x]

/-- The operator of a unitary representation, as a continuous linear map. -/
def actL (rep : UnitaryRep G F) (g : G) : F →L[ℂ] F :=
  LinearMap.mkContinuous (rep.act g) 1 (fun x => by rw [rep.norm_act, one_mul])

omit [Fintype G] in
@[simp] theorem actL_apply (rep : UnitaryRep G F) (g : G) (x : F) :
    rep.actL g x = rep.act g x := rfl

/-- **A unitary representation of a finite group extends to the completion.** -/
def completionRep (rep : UnitaryRep G F) : UnitaryRep G (UniformSpace.Completion F) where
  act g := ((rep.actL g).completion : UniformSpace.Completion F →L[ℂ]
    UniformSpace.Completion F).toLinearMap
  act_one x := by
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq (ContinuousLinearMap.continuous _) continuous_id) (fun a => ?_)
    change (rep.actL 1).completion (a : UniformSpace.Completion F) = (a : _)
    rw [ContinuousLinearMap.completion_apply_coe]
    simp [rep.act_one a]
  act_mul g h x := by
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq (ContinuousLinearMap.continuous _)
        ((ContinuousLinearMap.continuous _).comp (ContinuousLinearMap.continuous _)))
      (fun a => ?_)
    change (rep.actL (g * h)).completion (a : UniformSpace.Completion F)
      = (rep.actL g).completion ((rep.actL h).completion (a : UniformSpace.Completion F))
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
      ContinuousLinearMap.completion_apply_coe]
    simp [rep.act_mul g h a]
  act_inner g x y := by
    refine UniformSpace.Completion.induction_on₂ x y
      (isClosed_eq (Continuous.inner
        (((ContinuousLinearMap.continuous _).comp continuous_fst))
        (((ContinuousLinearMap.continuous _).comp continuous_snd)))
        (continuous_inner)) (fun a b => ?_)
    change (inner ℂ ((rep.actL g).completion (a : UniformSpace.Completion F))
      ((rep.actL g).completion (b : UniformSpace.Completion F)) : ℂ)
      = inner ℂ (a : UniformSpace.Completion F) (b : UniformSpace.Completion F)
    rw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    rw [UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
    exact rep.act_inner g a b

omit [Fintype G] in
@[simp] theorem completionRep_act_coe (rep : UnitaryRep G F) (g : G) (x : F) :
    rep.completionRep.act g (x : UniformSpace.Completion F)
      = ((rep.act g x : F) : UniformSpace.Completion F) := by
  change (rep.actL g).completion (x : UniformSpace.Completion F) = _
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

/-- The invariant sector of the extended representation is a **closed** subspace: it is the
intersection of the fixed-point sets of the (continuous) operators of the action. -/
theorem isClosed_sector_completionRep (rep : UnitaryRep G F) :
    IsClosed (sector rep.completionRep.avgProj : Set (UniformSpace.Completion F)) := by
  have hset : (sector rep.completionRep.avgProj : Set (UniformSpace.Completion F))
      = ⋂ g : G, {x | rep.completionRep.act g x = x} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact rep.completionRep.mem_range_avgProj_iff
  rw [hset]
  refine isClosed_iInter (fun g => isClosed_eq ?_ continuous_id)
  exact (ContinuousLinearMap.continuous ((rep.actL g).completion))

instance completeSpace_sector_completionRep (rep : UnitaryRep G F) :
    CompleteSpace (sector rep.completionRep.avgProj) :=
  (rep.isClosed_sector_completionRep).completeSpace_coe



end CompletionRep
end

end BookProof.GroupAverage.UnitaryRep

namespace BookProof.FockStatistics

open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.EsaOneParticle BookProof.DirectSumEsa

noncomputable section


/-! ## 2. The permutation action on the complete `n`-particle sector -/

section Complete

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

theorem sectorEmb_apply (n : ℕ) (x : (Hs.pow n).carrier) :
    sectorEmb Hs n x = (x : fockSector Hs n) := rfl

/-- The permutation action on the completed `n`-particle sector. -/
def cpermRep (n : ℕ) : UnitaryRep (Equiv.Perm (Fin n)) (fockSector Hs n) :=
  (permRep Hs n).completionRep

/-- Its sign twist. -/
def csignRep (n : ℕ) : UnitaryRep (Equiv.Perm (Fin n)) (fockSector Hs n) :=
  (signRep Hs n).completionRep

/-- The **symmetrizer** of the completed `n`-particle sector. -/
def cbosonicProj (n : ℕ) : fockSector Hs n →ₗ[ℂ] fockSector Hs n := (cpermRep Hs n).avgProj

/-- The **antisymmetrizer** of the completed `n`-particle sector. -/
def cfermionicProj (n : ℕ) : fockSector Hs n →ₗ[ℂ] fockSector Hs n := (csignRep Hs n).avgProj

theorem isReducingProjection_cbosonicProj (n : ℕ) :
    IsReducingProjection (cbosonicProj Hs n) :=
  (cpermRep Hs n).isReducingProjection_avgProj

theorem isReducingProjection_cfermionicProj (n : ℕ) :
    IsReducingProjection (cfermionicProj Hs n) :=
  (csignRep Hs n).isReducingProjection_avgProj

/-- **The symmetric part of the complete sector is a closed subspace**, hence a Hilbert
space. -/
instance completeSpace_cbosonicSector (n : ℕ) :
    CompleteSpace (sector (cbosonicProj Hs n)) :=
  (permRep Hs n).completeSpace_sector_completionRep

/-- **The antisymmetric part of the complete sector is a closed subspace.** -/
instance completeSpace_cfermionicSector (n : ℕ) :
    CompleteSpace (sector (cfermionicProj Hs n)) :=
  (signRep Hs n).completeSpace_sector_completionRep

/-- The symmetric part of the complete sector consists of the tensors fixed by the whole
action. -/
theorem mem_cbosonicSector_iff (n : ℕ) {x : fockSector Hs n} :
    x ∈ sector (cbosonicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), (cpermRep Hs n).act σ x = x :=
  (cpermRep Hs n).mem_range_avgProj_iff

/-- The antisymmetric part of the complete sector consists of the tensors on which the
sign-twisted action is trivial. -/
theorem mem_cfermionicSector_iff (n : ℕ) {x : fockSector Hs n} :
    x ∈ sector (cfermionicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), (csignRep Hs n).act σ x = x :=
  (csignRep Hs n).mem_range_avgProj_iff

/-- The completed symmetrizer extends the symmetrizer of the algebraic tensor power. -/
theorem cbosonicProj_sectorEmb (n : ℕ) (x : (Hs.pow n).carrier) :
    cbosonicProj Hs n (sectorEmb Hs n x) = sectorEmb Hs n (bosonicProj Hs n x) := by
  rw [cbosonicProj, UnitaryRep.avgProj_apply, bosonicProj, UnitaryRep.avgProj_apply,
    map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => (permRep Hs n).completionRep_act_coe g x)

/-- The completed antisymmetrizer extends the antisymmetrizer of the algebraic tensor
power. -/
theorem cfermionicProj_sectorEmb (n : ℕ) (x : (Hs.pow n).carrier) :
    cfermionicProj Hs n (sectorEmb Hs n x) = sectorEmb Hs n (fermionicProj Hs n x) := by
  rw [cfermionicProj, UnitaryRep.avgProj_apply, fermionicProj, UnitaryRep.avgProj_apply,
    map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => (signRep Hs n).completionRep_act_coe g x)

/-! ### The action preserves the domain and commutes with the derivation -/

theorem cpermRep_mem_fockSectorDom (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : fockSector Hs n)
    (hx : x ∈ fockSectorDom Hs D n) : (cpermRep Hs n).act σ x ∈ fockSectorDom Hs D n := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨(permRep Hs n).act σ v, permRep_mem_sectorDom Hs D n σ v hv, ?_⟩
  exact ((permRep Hs n).completionRep_act_coe σ v).symm

theorem csignRep_mem_fockSectorDom (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : fockSector Hs n)
    (hx : x ∈ fockSectorDom Hs D n) : (csignRep Hs n).act σ x ∈ fockSectorDom Hs D n := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨(signRep Hs n).act σ v, signRep_mem_sectorDom Hs D n σ v hv, ?_⟩
  exact ((signRep Hs n).completionRep_act_coe σ v).symm

theorem cpermRep_commutes_fockSectorDom (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : fockSectorDom Hs D n) :
    fockSectorOp Hs D A n ⟨(cpermRep Hs n).act σ (x : fockSector Hs n),
        cpermRep_mem_fockSectorDom Hs D n σ _ x.2⟩
      = (cpermRep Hs n).act σ (fockSectorOp Hs D A n x) := by
  obtain ⟨v, hv, hvx⟩ := x.2
  set v' : sectorDom Hs D n := ⟨v, hv⟩ with hv'
  have hx : (x : fockSector Hs n) = sectorEmb Hs n (v' : (Hs.pow n).carrier) := hvx.symm
  have hact : ((cpermRep Hs n).act σ (x : fockSector Hs n))
      = sectorEmb Hs n ((permRep Hs n).act σ v) := by
    rw [hx]
    exact (permRep Hs n).completionRep_act_coe σ v
  have h1 : fockSectorOp Hs D A n ⟨(cpermRep Hs n).act σ (x : fockSector Hs n),
        cpermRep_mem_fockSectorDom Hs D n σ _ x.2⟩
      = sectorEmb Hs n (sectorOp Hs D A n
          ⟨(permRep Hs n).act σ v, permRep_mem_sectorDom Hs D n σ v hv⟩) :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs D A n) _ _ hact
  have h2 : fockSectorOp Hs D A n x = sectorEmb Hs n (sectorOp Hs D A n v') :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs D A n) x v' hx
  have h3 : (cpermRep Hs n).act σ (sectorEmb Hs n (sectorOp Hs D A n v'))
      = sectorEmb Hs n ((permRep Hs n).act σ (sectorOp Hs D A n v')) :=
    (permRep Hs n).completionRep_act_coe σ _
  rw [h1, h2, h3]
  exact congrArg (sectorEmb Hs n) (permRep_commutes_sectorDom Hs D A n σ v')

theorem csignRep_commutes_fockSectorDom (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : fockSectorDom Hs D n) :
    fockSectorOp Hs D A n ⟨(csignRep Hs n).act σ (x : fockSector Hs n),
        csignRep_mem_fockSectorDom Hs D n σ _ x.2⟩
      = (csignRep Hs n).act σ (fockSectorOp Hs D A n x) := by
  obtain ⟨v, hv, hvx⟩ := x.2
  set v' : sectorDom Hs D n := ⟨v, hv⟩ with hv'
  have hx : (x : fockSector Hs n) = sectorEmb Hs n (v' : (Hs.pow n).carrier) := hvx.symm
  have hact : ((csignRep Hs n).act σ (x : fockSector Hs n))
      = sectorEmb Hs n ((signRep Hs n).act σ v) := by
    rw [hx]
    exact (signRep Hs n).completionRep_act_coe σ v
  have h1 : fockSectorOp Hs D A n ⟨(csignRep Hs n).act σ (x : fockSector Hs n),
        csignRep_mem_fockSectorDom Hs D n σ _ x.2⟩
      = sectorEmb Hs n (sectorOp Hs D A n
          ⟨(signRep Hs n).act σ v, signRep_mem_sectorDom Hs D n σ v hv⟩) :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs D A n) _ _ hact
  have h2 : fockSectorOp Hs D A n x = sectorEmb Hs n (sectorOp Hs D A n v') :=
    pushOp_apply (sectorEmb Hs n) (sectorOp Hs D A n) x v' hx
  have h3 : (csignRep Hs n).act σ (sectorEmb Hs n (sectorOp Hs D A n v'))
      = sectorEmb Hs n ((signRep Hs n).act σ (sectorOp Hs D A n v')) :=
    (signRep Hs n).completionRep_act_coe σ _
  rw [h1, h2, h3]
  exact congrArg (sectorEmb Hs n) (signRep_commutes_sectorDom Hs D A n σ v')

/-- `dΓ(A)⁽ⁿ⁾` reduced to the symmetric part of the complete `n`-particle sector. -/
def cbosonicSectorOp (n : ℕ) :
    redDom (cbosonicProj Hs n) (fockSectorDom Hs D n) →ₗ[ℂ] sector (cbosonicProj Hs n) :=
  redOp (fockSectorOp Hs D A n) (isReducingProjection_cbosonicProj Hs n)
    ((cpermRep Hs n).commutes_avgProj
      (hD := cpermRep_mem_fockSectorDom Hs D n)
      (cpermRep_commutes_fockSectorDom Hs D A n))

/-- `dΓ(A)⁽ⁿ⁾` reduced to the antisymmetric part of the complete `n`-particle sector. -/
def cfermionicSectorOp (n : ℕ) :
    redDom (cfermionicProj Hs n) (fockSectorDom Hs D n) →ₗ[ℂ] sector (cfermionicProj Hs n) :=
  redOp (fockSectorOp Hs D A n) (isReducingProjection_cfermionicProj Hs n)
    ((csignRep Hs n).commutes_avgProj
      (hD := csignRep_mem_fockSectorDom Hs D n)
      (csignRep_commutes_fockSectorDom Hs D A n))

end Complete


/-! ## 3. Essential self-adjointness on the complete sectors -/

section CompleteEsa

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)

omit [CompleteSpace Hs.carrier] in
include hsym in
/-- `dΓ(A)⁽ⁿ⁾` is symmetric on the symmetric part of the complete `n`-particle sector. -/
theorem symmetricOn_cbosonic (n : ℕ) :
    SymmetricOn (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n))
      (cbosonicSectorOp Hs D A n) :=
  symmetricOn_redOp _ _
    (symmetricOn_pushOp (sectorEmb Hs n) (sectorOp Hs D A n)
      (symmetricOn_sectorOp Hs D A hsym n))

omit [CompleteSpace Hs.carrier] in
include hsym in
/-- `dΓ(A)⁽ⁿ⁾` is symmetric on the antisymmetric part of the complete `n`-particle sector. -/
theorem symmetricOn_cfermionic (n : ℕ) :
    SymmetricOn (redDom (cfermionicProj Hs n) (fockSectorDom Hs D n))
      (cfermionicSectorOp Hs D A n) :=
  symmetricOn_redOp _ _
    (symmetricOn_pushOp (sectorEmb Hs n) (sectorOp Hs D A n)
      (symmetricOn_sectorOp Hs D A hsym n))

include hdense hsym hesa in
/-- **`dΓ(A)⁽ⁿ⁾` is essentially self-adjoint on the symmetric part of the complete
`n`-particle sector.** -/
theorem essentiallySelfAdjointOn_cbosonic (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n))
      (cbosonicSectorOp Hs D A n) :=
  essentiallySelfAdjointOn_red _ _
    (essentiallySelfAdjointOn_fockSectorDom_esa A hdense hsym hesa n)

include hdense hsym hesa in
/-- **`dΓ(A)⁽ⁿ⁾` is essentially self-adjoint on the antisymmetric part of the complete
`n`-particle sector.** -/
theorem essentiallySelfAdjointOn_cfermionic (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (cfermionicProj Hs n) (fockSectorDom Hs D n))
      (cfermionicSectorOp Hs D A n) :=
  essentiallySelfAdjointOn_red _ _
    (essentiallySelfAdjointOn_fockSectorDom_esa A hdense hsym hesa n)

end CompleteEsa

/-! ## 4. The two Hilbert Fock spaces -/

section HilbertFock

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

/-- **The bosonic Fock space** over `H`, as a Hilbert space: the `ℓ²` direct sum over the
particle number of the symmetric part of the complete `n`-particle sector. -/
abbrev hbosonicFock : Type := lp (fun n : ℕ => ↥(sector (cbosonicProj Hs n))) 2

/-- **The fermionic Fock space** over `H`, as a Hilbert space. -/
abbrev hfermionicFock : Type := lp (fun n : ℕ => ↥(sector (cfermionicProj Hs n))) 2

instance completeSpace_hbosonicFock : CompleteSpace (hbosonicFock Hs) := by
  infer_instance

instance completeSpace_hfermionicFock : CompleteSpace (hfermionicFock Hs) := by
  infer_instance

/-- The domain of `dΓ(A)` on the bosonic Fock space. -/
def hbosonicFockDom : Submodule ℂ (hbosonicFock Hs) :=
  dsCore (fun n : ℕ => redDom (cbosonicProj Hs n) (fockSectorDom Hs D n))

/-- The domain of `dΓ(A)` on the fermionic Fock space. -/
def hfermionicFockDom : Submodule ℂ (hfermionicFock Hs) :=
  dsCore (fun n : ℕ => redDom (cfermionicProj Hs n) (fockSectorDom Hs D n))

/-- **`dΓ(A)` on the bosonic Fock space.** -/
def hbosonicFockOp : hbosonicFockDom Hs D →ₗ[ℂ] hbosonicFock Hs :=
  dsOp (fun n : ℕ => cbosonicSectorOp Hs D A n)

/-- **`dΓ(A)` on the fermionic Fock space.** -/
def hfermionicFockOp : hfermionicFockDom Hs D →ₗ[ℂ] hfermionicFock Hs :=
  dsOp (fun n : ℕ => cfermionicSectorOp Hs D A n)

end HilbertFock

section HilbertFockEsa

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)

omit [CompleteSpace Hs.carrier] in
include hsym in
/-- `dΓ(A)` is symmetric on the bosonic Fock space. -/
theorem hbosonicFock_symmetricOn :
    SymmetricOn (hbosonicFockDom Hs D) (hbosonicFockOp Hs D A) :=
  dsOp_symmetricOn _ (fun n => symmetricOn_cbosonic A hsym n)

omit [CompleteSpace Hs.carrier] in
include hsym in
/-- `dΓ(A)` is symmetric on the fermionic Fock space. -/
theorem hfermionicFock_symmetricOn :
    SymmetricOn (hfermionicFockDom Hs D) (hfermionicFockOp Hs D A) :=
  dsOp_symmetricOn _ (fun n => symmetricOn_cfermionic A hsym n)

include hdense hsym hesa in
/-- **`dΓ(A)` is essentially self-adjoint on the bosonic Fock space** — the Hilbert space
direct sum over all particle numbers of the symmetric sectors. -/
theorem hbosonicFock_esa :
    EssentiallySelfAdjointOn (hbosonicFockDom Hs D) (hbosonicFockOp Hs D A) :=
  dsOp_essentiallySelfAdjointOn _
    (fun n => essentiallySelfAdjointOn_cbosonic A hdense hsym hesa n)

include hdense hsym hesa in
/-- **`dΓ(A)` is essentially self-adjoint on the fermionic Fock space.** -/
theorem hfermionicFock_esa :
    EssentiallySelfAdjointOn (hfermionicFockDom Hs D) (hfermionicFockOp Hs D A) :=
  dsOp_essentiallySelfAdjointOn _
    (fun n => essentiallySelfAdjointOn_cfermionic A hdense hsym hesa n)

end HilbertFockEsa

/-! ## 5. Non-vacuity -/

section NonVacuous

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier)

/-- A symmetric tensor of the algebraic power is a symmetric tensor of the complete
sector. -/
theorem sectorEmb_mem_cbosonicSector (n : ℕ) {x : (Hs.pow n).carrier}
    (hx : x ∈ sector (bosonicProj Hs n)) : sectorEmb Hs n x ∈ sector (cbosonicProj Hs n) :=
  ⟨sectorEmb Hs n x, by
    rw [cbosonicProj_sectorEmb]
    exact congrArg (sectorEmb Hs n) ((isReducingProjection_bosonicProj Hs n).apply_of_mem_range hx)⟩

/-- An antisymmetric tensor of the algebraic power is an antisymmetric tensor of the
complete sector. -/
theorem sectorEmb_mem_cfermionicSector (n : ℕ) {x : (Hs.pow n).carrier}
    (hx : x ∈ sector (fermionicProj Hs n)) :
    sectorEmb Hs n x ∈ sector (cfermionicProj Hs n) :=
  ⟨sectorEmb Hs n x, by
    rw [cfermionicProj_sectorEmb]
    exact congrArg (sectorEmb Hs n)
      ((isReducingProjection_fermionicProj Hs n).apply_of_mem_range hx)⟩

/-- **The bosonic statement is not vacuous**: the `n`-th power `a ⊗ ⋯ ⊗ a` of a nonzero
vector of the one-particle domain is a nonzero vector of the symmetric part of the complete
`n`-particle sector. -/
theorem exists_ne_zero_cbosonic (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) :
    ∃ x : redDom (cbosonicProj Hs n) (fockSectorDom Hs D n), x ≠ 0 := by
  obtain ⟨y, hy0⟩ := exists_ne_zero_bosonic Hs D D n le_rfl haD ha0
  set v : (Hs.pow n).carrier := ((y : sector (bosonicProj Hs n)) : (Hs.pow n).carrier) with hv
  have hvsec : v ∈ sector (bosonicProj Hs n) := (y : sector (bosonicProj Hs n)).2
  have hvdom : v ∈ sectorDom Hs D n := sectorCore_le_sectorDom Hs D D n y.2
  have hv0 : v ≠ 0 := by
    intro h
    exact hy0 (Subtype.ext (Subtype.ext h))
  refine ⟨⟨⟨sectorEmb Hs n v, sectorEmb_mem_cbosonicSector Hs n hvsec⟩,
    ⟨v, hvdom, rfl⟩⟩, ?_⟩
  intro h
  refine hv0 ((sectorEmb Hs n).injective ?_)
  have := congrArg Subtype.val (congrArg Subtype.val h)
  simpa using this

/-- **The fermionic statement is not vacuous**: the Slater determinant of `n` pairwise
orthogonal nonzero vectors of the one-particle domain is a nonzero vector of the
antisymmetric part of the complete `n`-particle sector. -/
theorem exists_ne_zero_cfermionic (n : ℕ) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D)
    (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) :
    ∃ x : redDom (cfermionicProj Hs n) (fockSectorDom Hs D n), x ≠ 0 := by
  obtain ⟨y, hy0⟩ := exists_ne_zero_fermionic Hs D D n le_rfl f hfD hf0 hortho
  set v : (Hs.pow n).carrier := ((y : sector (fermionicProj Hs n)) : (Hs.pow n).carrier) with hv
  have hvsec : v ∈ sector (fermionicProj Hs n) := (y : sector (fermionicProj Hs n)).2
  have hvdom : v ∈ sectorDom Hs D n := sectorCore_le_sectorDom Hs D D n y.2
  have hv0 : v ≠ 0 := by
    intro h
    exact hy0 (Subtype.ext (Subtype.ext h))
  refine ⟨⟨⟨sectorEmb Hs n v, sectorEmb_mem_cfermionicSector Hs n hvsec⟩,
    ⟨v, hvdom, rfl⟩⟩, ?_⟩
  intro h
  refine hv0 ((sectorEmb Hs n).injective ?_)
  have := congrArg Subtype.val (congrArg Subtype.val h)
  simpa using this





end NonVacuous

end

end BookProof.FockStatistics


