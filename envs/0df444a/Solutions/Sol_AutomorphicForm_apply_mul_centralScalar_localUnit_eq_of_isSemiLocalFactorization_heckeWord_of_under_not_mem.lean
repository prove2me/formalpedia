-- Prove2me | solution 1 for AutomorphicForm.apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/beeb962f-81b0-5411-8ef9-e7f37d038891

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace HurInvL

section GLPart
variable {A B : Type} [CommRing A] [CommRing B]

theorem val_mul_scalar (γ : GL (Fin 2) A) (u : Aˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      (u : A) • (γ : Matrix (Fin 2) (Fin 2) A) := by
  rw [Units.val_mul]
  change (γ : Matrix (Fin 2) (Fin 2) A) * Matrix.scalar (Fin 2) (u : A) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]

private theorem _root_.HurInvL.scalar_commute (u : Aˣ) (g : GL (Fin 2) A) : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) u) g := by
  change Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (u : A) (fun r' => mul_comm _ r') _).eq

p2m_export "HurInvL" "scalar_commute"
theorem map_scalar (f : A →+* B) (u : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : A →* B) u) := by
  ext i j
  change f ((Matrix.scalar (Fin 2) (u : A)) i j) = (Matrix.scalar (Fin 2) (f (u : A))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem mul_scalar_mem_integralUnitsSet_iff {U : Set A} (hU : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
    (u : Aˣ) (hu : (u : A) ∈ U) (hu' : ((u⁻¹ : Aˣ) : A) ∈ U) (g : GL (Fin 2) A) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ AutomorphicForm.integralUnitsSet U ↔
      g ∈ AutomorphicForm.integralUnitsSet U := by
  have key : ∀ (w : Aˣ), (w : A) ∈ U → ((w⁻¹ : Aˣ) : A) ∈ U → ∀ g : GL (Fin 2) A,
      g ∈ AutomorphicForm.integralUnitsSet U →
        g * Matrix.GeneralLinearGroup.scalar (Fin 2) w ∈ AutomorphicForm.integralUnitsSet U := by
    intro w hw hw' g hg
    rw [AutomorphicForm.mem_integralUnitsSet] at hg ⊢
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [val_mul_scalar, Matrix.smul_apply, smul_eq_mul, mul_comm]
      exact hU _ (hg.1 i j) _ hw
    · rw [mul_inv_rev, ← map_inv, (scalar_commute _ _).eq, val_mul_scalar, Matrix.smul_apply, smul_eq_mul,
        mul_comm]
      exact hU _ (hg.2 i j) _ hw'
  refine ⟨fun h => ?_, key u hu hu' g⟩
  have h2 := key u⁻¹ hu' (by rw [inv_inv]; exact hu) _ h
  rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h2

end GLPart

section SemiLocal
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem mul_mem_semiLocalIntegers (v : HeightOneSpectrum (𝓞 K)) :
    ∀ a ∈ AutomorphicForm.semiLocalIntegers K L v, ∀ b ∈ AutomorphicForm.semiLocalIntegers K L v,
      a * b ∈ AutomorphicForm.semiLocalIntegers K L v := by
  rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩
  exact ⟨x * y, map_mul _ x y⟩

theorem semiLocalEval_localUnit_mem (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (s : (w.adicCompletion L)ˣ) (hs : Valued.v (s : w.adicCompletion L) ≤ 1) :
    AutomorphicForm.semiLocalEval K L v ((localUnit (𝓞 L) L w s : (FiniteAdeleRing (𝓞 L) L)ˣ) :
        FiniteAdeleRing (𝓞 L) L) ∈ AutomorphicForm.semiLocalIntegers K L v := by
  classical
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.semiLocalHomeomorph_eq,
    AutomorphicForm.semiLocalEval_eq, AlgEquiv.apply_symm_apply, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  intro w'
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  by_cases hw' : w'.1 = w
  · rw [hw', localUnit_apply_self]; exact hs
  · rw [localUnit_apply_of_ne (𝓞 L) L w s hw', map_one]

theorem semiLocalEval_localUnit_of_ne (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hv : HeightOneSpectrum.under (𝓞 K) w ≠ v) (s : (w.adicCompletion L)ˣ) :
    AutomorphicForm.semiLocalEval K L v ((localUnit (𝓞 L) L w s : (FiniteAdeleRing (𝓞 L) L)ˣ) :
        FiniteAdeleRing (𝓞 L) L) = 1 := by
  classical
  rw [AutomorphicForm.semiLocalEval_eq]
  have : (fun w' : v.Extension (𝓞 L) =>
      ((localUnit (𝓞 L) L w s : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w'.1) = 1 := by
    funext w'
    have hw' : w'.1 ≠ w := fun h => hv (by rw [← h]; exact w'.2)
    rw [localUnit_apply_of_ne (𝓞 L) L w s hw', Pi.one_apply]
  rw [this, map_one]

end SemiLocal

end HurInvL

end

open HurInvL AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K)))
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
    (hϖs0 : ∀ v ∈ T,
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrTs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (φL : AdelicGL2 (𝓞 L) L → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hSLF : AutomorphicForm.IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (ns v),
          (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
        else φS v))
    (w : HeightOneSpectrum (𝓞 L)) (hw : HeightOneSpectrum.under (𝓞 K) w ∉ SK)
    (s : (w.adicCompletion L)ˣ) (hs : Valued.v (s : w.adicCompletion L) = 1)
    (g : AdelicGL2 (𝓞 L) L) :
    φL (g * AutomorphicForm.centralScalar (𝓞 L) L
      (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w s))) = φL g := by
  classical
  obtain ⟨_, _, _, hprod, hzero, hφ⟩ := hSLF

  set u : (FiniteAdeleRing (𝓞 L) L)ˣ := localUnit (𝓞 L) L w s with hu
  have hsO : Valued.v (s : w.adicCompletion L) ≤ 1 := le_of_eq hs
  have hsO' : Valued.v (((s⁻¹ : (w.adicCompletion L)ˣ)) : w.adicCompletion L) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]

  have hcA : AdelicLevel.glArch (𝓞 L) L
      (AutomorphicForm.centralScalar (𝓞 L) L (Units.map (finIncl (𝓞 L) L) u)) = 1 := by
    show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 L) L)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (finIncl (𝓞 L) L) u)) = 1
    rw [map_scalar]
    have : Units.map (AdelicLevel.adeleArch (𝓞 L) L : AdeleRing (𝓞 L) L →* InfiniteAdeleRing L)
        (Units.map (finIncl (𝓞 L) L) u) = 1 := Units.ext rfl
    rw [this, map_one]
  have hcF : AdelicLevel.glFin (𝓞 L) L
      (AutomorphicForm.centralScalar (𝓞 L) L (Units.map (finIncl (𝓞 L) L) u)) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    show Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 L) L)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (finIncl (𝓞 L) L) u)) = _
    rw [map_scalar]
    have hfu : Units.map (AdelicLevel.adeleFin (𝓞 L) L : AdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 L) L)
        (Units.map (finIncl (𝓞 L) L) u) = u := Units.ext rfl
    rw [hfu]

  have hcomp : ∀ (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      AutomorphicForm.semiLocalComponent K L v (h * Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
        AutomorphicForm.semiLocalComponent K L v h *
          Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.map (AutomorphicForm.semiLocalEval K L v : FiniteAdeleRing (𝓞 L) L →* L ⊗[K] v.adicCompletion K) u) := by
    intro v h
    rw [map_mul]
    congr 1
    exact map_scalar (AutomorphicForm.semiLocalEval K L v) u
  have hdv : ∀ v : HeightOneSpectrum (𝓞 K),
      ((Units.map (AutomorphicForm.semiLocalEval K L v : FiniteAdeleRing (𝓞 L) L →* L ⊗[K] v.adicCompletion K) u :
        (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v :=
    fun v => semiLocalEval_localUnit_mem K L v w s hsO
  have hdv' : ∀ v : HeightOneSpectrum (𝓞 K),
      (((Units.map (AutomorphicForm.semiLocalEval K L v : FiniteAdeleRing (𝓞 L) L →* L ⊗[K] v.adicCompletion K) u)⁻¹ :
        (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v := by
    intro v
    rw [← map_inv, hu, ← map_inv]
    exact semiLocalEval_localUnit_mem K L v w s⁻¹ hsO'
  have hinv : ∀ (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      y * Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AutomorphicForm.semiLocalEval K L v : FiniteAdeleRing (𝓞 L) L →* L ⊗[K] v.adicCompletion K) u) ∈
        AutomorphicForm.semiLocalIntegralSet K L v ↔ y ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
    fun v y => mul_scalar_mem_integralUnitsSet_iff (mul_mem_semiLocalIntegers K L v) _ (hdv v) (hdv' v) y
  have hd1 : ∀ v : HeightOneSpectrum (𝓞 K), HeightOneSpectrum.under (𝓞 K) w ≠ v →
      Units.map (AutomorphicForm.semiLocalEval K L v : FiniteAdeleRing (𝓞 L) L →* L ⊗[K] v.adicCompletion K) u = 1 := by
    intro v hv
    apply Units.ext
    rw [Units.coe_map, Units.val_one]
    exact semiLocalEval_localUnit_of_ne K L v w hv s

  rw [hφ, hφ g, map_mul, map_mul, hcA, mul_one, hcF]
  congr 1
  set h := AdelicLevel.glFin (𝓞 L) L g with hh
  by_cases hint : ∀ v ∉ SK ∪ T, AutomorphicForm.semiLocalComponent K L v h ∈ AutomorphicForm.semiLocalIntegralSet K L v
  · have hint' : ∀ v ∉ SK ∪ T, AutomorphicForm.semiLocalComponent K L v
        (h * Matrix.GeneralLinearGroup.scalar (Fin 2) u) ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
      intro v hv
      rw [hcomp]
      exact (hinv v _).mpr (hint v hv)
    rw [hprod _ hint', hprod _ hint]
    refine Finset.prod_congr rfl (fun v hv => ?_)
    by_cases hvw : HeightOneSpectrum.under (𝓞 K) w = v
    ·
      have hvT : v ∈ T := by
        rcases Finset.mem_union.mp hv with h1 | h1
        · exact absurd h1 (hvw ▸ hw)
        · exact h1
      simp only [hvT, if_true]
      rw [hcomp]
      refine Finset.sum_congr rfl (fun ι _ => ?_)
      simp only [Set.indicator_apply, ← mul_assoc, hinv]
    · rw [hcomp, hd1 v hvw, map_one, mul_one]
  · push Not at hint
    obtain ⟨v, hv, hnot⟩ := hint
    have hnot' : AutomorphicForm.semiLocalComponent K L v (h * Matrix.GeneralLinearGroup.scalar (Fin 2) u) ∉
        AutomorphicForm.semiLocalIntegralSet K L v := by
      rw [hcomp]
      exact fun hmem => hnot ((hinv v _).mp hmem)
    rw [hzero _ ⟨v, hv, hnot'⟩, hzero _ ⟨v, hv, hnot⟩]

end S_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem
end P2MW
export P2MW.S_AutomorphicForm_apply_mul_centralScalar_localUnit_eq_of_isSemiLocalFactorization_heckeWord_of_under_not_mem (solution)
