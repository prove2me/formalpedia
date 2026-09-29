-- Prove2me | solution 1 for AutomorphicForm.TransversalMeasure.archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/94334ec7-5bdb-5d73-b830-c164c192f421

import Mathlib
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TransversalMeasure_archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace R1S83ArchBridge

open M4aHerbrand M4aHerbrand.Bridge M4aHerbrand.GenuineDescent M4aHerbrand.ArchSemilocal FLT.InfiniteAdeleBaseChange

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local instance instAdeleAlgebra : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  (genuineβ K L).toAlgebra

abbrev congrA (σ : L ≃ₐ[K] L) :
    ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] ((AdeleRing (𝓞 K) K) ⊗[K] L) :=
  Algebra.TensorProduct.congr AlgEquiv.refl σ

abbrev congrV (σ : L ≃ₐ[K] L) (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) ≃ₐ[v.Completion] (v.Completion ⊗[K] L) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[v.Completion] v.Completion) σ

def splitA : ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[K]
    ((InfiniteAdeleRing K ⊗[K] L) × (FiniteAdeleRing (𝓞 K) K ⊗[K] L)) :=
  prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L

omit [NumberField L] in
theorem splitA_tmul_fst (a : AdeleRing (𝓞 K) K) (l : L) : (splitA K L (a ⊗ₜ[K] l)).1 = a.1 ⊗ₜ[K] l :=
  congrArg Prod.fst (prodTensorAlgEquiv_tmul K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L a l)

theorem act_genuineRingEquiv (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    (genuineDescentDatum K L).act σ (genuineRingEquiv K L z) = genuineRingEquiv K L (congrA K L σ z) := by
  show genuineRingEquiv K L (congrA K L σ ((genuineRingEquiv K L).symm (genuineRingEquiv K L z))) = _
  rw [RingEquiv.symm_apply_apply]

open scoped NumberField.LiesOver

attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver

theorem genuineRingEquiv_fst_apply (z : (AdeleRing (𝓞 K) K) ⊗[K] L) (w : InfinitePlace L) :
    (genuineRingEquiv K L z).1 w =
      (genuineInfinitePlaceData (K := K) (L := L)).placeEquiv (w.comap (algebraMap K L))
        (tensorPiAlgEquiv K L (splitA K L z).1 (w.comap (algebraMap K L))) ⟨w, rfl⟩ := rfl

theorem placeEquiv_reindex (v : InfinitePlace K) (w : v.Extension L)
    (F : ∀ u : InfinitePlace K, u.Completion ⊗[K] L) :
    (genuineInfinitePlaceData (K := K) (L := L)).placeEquiv (w.1.comap (algebraMap K L))
        (F (w.1.comap (algebraMap K L))) ⟨w.1, rfl⟩ =
      placeEquivAlg (K := K) (L := L) v (F v) w := by
  obtain ⟨w, rfl⟩ := w
  rfl

theorem tensorPi_congr (σ : L ≃ₐ[K] L) (v : InfinitePlace K) (z : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    tensorPiAlgEquiv K L (splitA K L (congrA K L σ z)).1 v =
      congrV K L σ v (tensorPiAlgEquiv K L (splitA K L z).1 v) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.fst_zero, Pi.zero_apply]
  | tmul a l =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, splitA_tmul_fst, splitA_tmul_fst,
      tensorPiAlgEquiv_tmul_apply, tensorPiAlgEquiv_tmul_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy =>
    simp only [map_add, Prod.fst_add, Pi.add_apply, hx, hy]

theorem genuine_act_fst_apply (σ : L ≃ₐ[K] L) (v : InfinitePlace K) (x : AdeleRing (𝓞 L) L)
    (w : v.Extension L) :
    ((genuineDescentDatum K L).act σ x).1 w.1 =
      placeEquivAlg (K := K) (L := L) v (congrV K L σ v
        ((placeEquivAlg (K := K) (L := L) v).symm (fun w' : v.Extension L => x.1 w'.1))) w := by
  obtain ⟨z, rfl⟩ : ∃ z, x = genuineRingEquiv K L z := ⟨(genuineRingEquiv K L).symm x, by simp⟩
  have hx : (fun w' : v.Extension L => (genuineRingEquiv K L z).1 w'.1) =
      placeEquivAlg (K := K) (L := L) v (tensorPiAlgEquiv K L (splitA K L z).1 v) := by
    funext w'
    rw [genuineRingEquiv_fst_apply]
    exact placeEquiv_reindex K L v w' _
  rw [hx, AlgEquiv.symm_apply_apply, act_genuineRingEquiv, genuineRingEquiv_fst_apply,
    placeEquiv_reindex K L v w, tensorPi_congr]

end R1S83ArchBridge

end

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (v : InfinitePlace K)
    (t : (AdeleRing (𝓞 L) L)ˣ) :
    ((AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) :
        ((w : v.Extension L) → w.1.Completion)ˣ) : (w : v.Extension L) → w.1.Completion) =
      M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[v.Completion] v.Completion) σ)
          ((M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v).symm
            ((AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t : ((w : v.Extension L) → w.1.Completion)ˣ) :
              (w : v.Extension L) → w.1.Completion))) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  funext w
  exact R1S83ArchBridge.genuine_act_fst_apply K L σ v (t : AdeleRing (𝓞 L) L) w

end S_AutomorphicForm_TransversalMeasure_archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm
end P2MW
export P2MW.S_AutomorphicForm_TransversalMeasure_archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm (solution)
