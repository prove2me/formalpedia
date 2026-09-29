-- Prove2me | solution 1 for AutomorphicForm.exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/46dc6d62-2722-5857-b563-342d986ff766

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped TensorProduct in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : GL (Fin 2) (InfiniteAdeleRing L))
    (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ g : GL (Fin 2) (AdeleRing (𝓞 L) L),
      AdelicLevel.glArch (𝓞 L) L g = a ∧
      (∀ v ∈ S, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) = x v) ∧
      ∀ v ∉ S, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) ∈
        AutomorphicForm.semiLocalIntegralSet K L v := by
  classical

  obtain ⟨z, hzS, hznS⟩ : ∃ z : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (∀ v ∈ S, z v = x v) ∧ (∀ v ∉ S, z v = 1) :=
    ⟨fun v => if v ∈ S then x v else 1, fun v hv => if_pos hv, fun v hv => if_neg hv⟩

  let und : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 K) := fun w => w.under (𝓞 K)
  let e : ∀ v : HeightOneSpectrum (𝓞 K),
      L ⊗[K] v.adicCompletion K ≃ₐ[L] (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
    fun v => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

  let ρ : ∀ w : HeightOneSpectrum (𝓞 L), L ⊗[K] (und w).adicCompletion K →+* w.adicCompletion L :=
    fun w => (Pi.evalRingHom (fun w' : (und w).Extension (𝓞 L) => w'.1.adicCompletion L) ⟨w, rfl⟩).comp
      (e (und w)).toRingEquiv.toRingHom
  have hρ : ∀ (w : HeightOneSpectrum (𝓞 L)) (t : L ⊗[K] (und w).adicCompletion K),
      ρ w t = (e (und w) t) ⟨w, rfl⟩ := fun w t => rfl

  have hint : ∀ w : HeightOneSpectrum (𝓞 L), und w ∉ S → ∀ i j : Fin 2,
      ρ w (((z (und w) : GL (Fin 2) (L ⊗[K] (und w).adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] (und w).adicCompletion K)) i j) ∈ w.adicCompletionIntegers L := by
    intro w hw i j
    rw [hznS _ hw, Units.val_one, Matrix.one_apply]
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  have hint' : ∀ w : HeightOneSpectrum (𝓞 L), und w ∉ S → ∀ i j : Fin 2,
      ρ w ((((z (und w))⁻¹ : GL (Fin 2) (L ⊗[K] (und w).adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] (und w).adicCompletion K)) i j) ∈ w.adicCompletionIntegers L := by
    intro w hw i j
    rw [hznS _ hw, inv_one, Units.val_one, Matrix.one_apply]
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _

  have hfin : (und ⁻¹' (S : Set (HeightOneSpectrum (𝓞 K)))).Finite := by
    refine S.finite_toSet.preimage' fun v _ => ?_
    haveI : Finite (v.Extension (𝓞 L)) :=
      IsDedekindDomain.HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
    refine Set.Finite.subset (Set.finite_range fun w' : v.Extension (𝓞 L) => w'.1) ?_
    intro w hw
    exact ⟨⟨w, hw⟩, rfl⟩

  let fe : Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 L) L := fun i j =>
    ⟨fun w => ρ w (((z (und w) : GL (Fin 2) (L ⊗[K] (und w).adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] (und w).adicCompletion K)) i j),
      Filter.eventually_cofinite.mpr (hfin.subset fun w hw => by
        by_contra hwS
        exact hw (hint w hwS i j))⟩
  let fe' : Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 L) L := fun i j =>
    ⟨fun w => ρ w ((((z (und w))⁻¹ : GL (Fin 2) (L ⊗[K] (und w).adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] (und w).adicCompletion K)) i j),
      Filter.eventually_cofinite.mpr (hfin.subset fun w hw => by
        by_contra hwS
        exact hw (hint' w hwS i j))⟩

  let M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) := fun i j =>
    (((a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j, fe i j) : AdeleRing (𝓞 L) L)
  let M' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) := fun i j =>
    ((((a⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j, fe' i j) :
      AdeleRing (𝓞 L) L)

  set πa := AdelicLevel.adeleArch (𝓞 L) L with hπa
  set πw : ∀ w : HeightOneSpectrum (𝓞 L), AdeleRing (𝓞 L) L →+* w.adicCompletion L :=
    fun w => (AdelicLevel.finAdeleEval (𝓞 L) L w).comp (AdelicLevel.adeleFin (𝓞 L) L) with hπw

  have key : ∀ P Q : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L),
      P.map πa = Q.map πa → (∀ w, P.map (πw w) = Q.map (πw w)) → P = Q := by
    intro P Q h1 h2
    ext i j
    apply Prod.ext
    · have := congr_fun (congr_fun h1 i) j
      simpa [Matrix.map_apply, hπa, AdelicLevel.adeleArch_apply] using this
    · refine Subtype.ext (funext fun w => ?_)
      have := congr_fun (congr_fun (h2 w) i) j
      simp [Matrix.map_apply, hπw, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply] at this
      exact this
  have hMa : M.map πa = (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) := by
    ext i j; rfl
  have hM'a : M'.map πa = ((a⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) := by
    ext i j; rfl
  have hMw : ∀ w, M.map (πw w) =
      ((z (und w) : GL (Fin 2) (L ⊗[K] (und w).adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] (und w).adicCompletion K)).map (ρ w) := by
    intro w; ext i j; rfl
  have hM'w : ∀ w, M'.map (πw w) =
      (((z (und w))⁻¹ : GL (Fin 2) (L ⊗[K] (und w).adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] (und w).adicCompletion K)).map (ρ w) := by
    intro w; ext i j; rfl
  have hMM' : M * M' = 1 := by
    apply key
    · rw [Matrix.map_mul, hMa, hM'a, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · intro w
      rw [Matrix.map_mul, hMw, hM'w, ← Matrix.map_mul, Units.mul_inv,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  have hM'M : M' * M = 1 := by
    apply key
    · rw [Matrix.map_mul, hMa, hM'a, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · intro w
      rw [Matrix.map_mul, hMw, hM'w, ← Matrix.map_mul, Units.inv_mul,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin 2) (AdeleRing (𝓞 L) L) := ⟨M, M', hMM', hM'M⟩

  have hcomp : ∀ v, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) = z v := by
    intro v
    refine Units.ext ?_
    ext i j
    show (e v).symm (fun w' : v.Extension (𝓞 L) => (fe i j : FiniteAdeleRing (𝓞 L) L) w'.1) =
      ((z v : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j
    have hfun : (fun w' : v.Extension (𝓞 L) => (fe i j : FiniteAdeleRing (𝓞 L) L) w'.1) =
        e v (((z v : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) := by
      funext w'
      obtain ⟨w, hw⟩ := w'
      subst hw
      rfl
    rw [hfun, AlgEquiv.symm_apply_apply]
  refine ⟨g, ?_, ?_, ?_⟩
  · refine Units.ext ?_
    ext i j
    rfl
  · intro v hv
    rw [hcomp, hzS v hv]
  · intro v hv
    rw [hcomp, hznS v hv]
    exact AutomorphicForm.one_mem_semiLocalIntegralSet K L v

end S_AutomorphicForm_exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet
end P2MW
export P2MW.S_AutomorphicForm_exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet (solution)
