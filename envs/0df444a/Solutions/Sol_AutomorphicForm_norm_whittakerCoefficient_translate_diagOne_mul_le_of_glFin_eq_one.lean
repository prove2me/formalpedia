-- Prove2me | solution 1 for AutomorphicForm.norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/bf1913e2-7f0d-537b-82b3-de3bb8b513e8

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_AutomorphicForm_exists_uniform_iwasawa_mul_of_glFin_eq_one
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

noncomputable section

namespace IWTRANSFER43

open MeasureTheory NumberField.StandardAddChar

variable (K : Type) [Field K] [NumberField K]

theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K g = glArch (𝓞 K) K h)
    (h₂ : glFin (𝓞 K) K g = glFin (𝓞 K) K h) : g = h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) h₁) i) j
    rwa [glArch_apply, glArch_apply] at this
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) h₂) i) j
    rwa [glFin_apply, glFin_apply] at this

theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one {g h : AdelicGL2 (𝓞 K) K}
    (hg : glArch (𝓞 K) K g = 1) (hh : glFin (𝓞 K) K h = 1) : g * h = h * g :=
  gl_ext K (by rw [map_mul, map_mul, hg, one_mul, mul_one]) (by rw [map_mul, map_mul, hh, one_mul, mul_one])

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  apply Units.ext
  show Matrix.scalar (Fin 2) ((z : (AdeleRing (𝓞 K) K))) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) ((z : (AdeleRing (𝓞 K) K)))
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem diagOne_mul_unipotentGL2 (a : (AdeleRing (𝓞 K) K)ˣ) (ν : (AdeleRing (𝓞 K) K)) :
    diagOne a * unipotentGL2 ν = unipotentGL2 ((a : (AdeleRing (𝓞 K) K)) * ν) * diagOne a := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem snd_units_mul (a b : (AdeleRing (𝓞 K) K)ˣ) : (((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).2 = ((a : (AdeleRing (𝓞 K) K))).2 * ((b : (AdeleRing (𝓞 K) K))).2 := rfl

theorem fst_units_mul_apply (a b : (AdeleRing (𝓞 K) K)ˣ) (pl : InfinitePlace K) :
    (((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl = ((a : (AdeleRing (𝓞 K) K))).1 pl * ((b : (AdeleRing (𝓞 K) K))).1 pl := rfl

theorem norm_stdAddChar_of_snd_eq_zero (u : (AdeleRing (𝓞 K) K)) (hu : u.2 = 0) :
    ‖NumberField.StandardAddChar.stdAddChar K u‖ = 1 := by
  show ‖(adelicTraceData K).psiK u‖ = 1
  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply, hu, map_zero,
    AddChar.map_zero_eq_one, mul_one, psiArch_apply]
  refine finprod_induction (fun c : ℂ => ‖c‖ = 1) norm_one
    (fun x y hx hy => by rw [norm_mul, hx, hy, mul_one]) ?_
  intro v
  dsimp only
  rw [psiArchPlace_apply]
  set r : ℝ := (InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)
    (((adelicTraceData K).traceInf u.1) v) : ℝ)
  rw [show (2 * (Real.pi : ℂ) * Complex.I) * (r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem whittakerCoefficient_translate (D₀ : Set (AdelicGL2 (𝓞 K) K)) (x : AdelicGL2 (𝓞 K) K → ℂ)
    (h X : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g' => x (g' * h)) 1
          (X) =
      whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (X * h) := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

theorem whittakerCoefficient_centralScalar_mul (D₀ : Set (AdelicGL2 (𝓞 K) K)) (x : AdelicGL2 (𝓞 K) K → ℂ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * x g)
    (z : (AdeleRing (𝓞 K) K)ˣ) (X : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (centralScalar (𝓞 K) K z * X) =
      ((ω z : ℂˣ) : ℂ) * whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (X) := by
  unfold whittakerCoefficient
  have hx : ∀ t : (AdeleRing (𝓞 K) K), x (unipotentGL2 t * (centralScalar (𝓞 K) K z * X)) =
      ((ω z : ℂˣ) : ℂ) * x (unipotentGL2 t * X) := by
    intro t
    rw [← mul_assoc, ← centralScalar_mul_comm, mul_assoc, hZ]
  simp_rw [hx, mul_assoc]
  exact integral_const_mul _ _

theorem whittakerCoefficient_unipotent (D₀ : Set (AdelicGL2 (𝓞 K) K)) (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hper : ∀ (β : K) (u : (AdeleRing (𝓞 K) K)) (g : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = x (unipotentGL2 u * g))
    (u : (AdeleRing (𝓞 K) K)) (X : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (unipotentGL2 u * X) =
      NumberField.StandardAddChar.stdAddChar K u * whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (X) := by
  have hψ : IsPrincipalInvariantAddChar K (NumberField.StandardAddChar.stdAddChar K) :=
    fun α => (NumberField.StandardAddChar.adelicTraceData K).psiK_algebraMap α
  rw [AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D₀
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (NumberField.StandardAddChar.stdAddChar K) hψ x X (fun β u' => hper β u' X) 1 u, map_one, one_mul]

theorem rpow_le_max {m M t : ℝ} (hm : 0 < m) (hmt : m ≤ t) (htM : t ≤ M) (e : ℝ) :
    t ^ e ≤ max (m ^ e) (M ^ e) := by
  rcases le_or_gt 0 e with he | he
  · exact le_max_of_le_right (Real.rpow_le_rpow (hm.le.trans hmt) htM he)
  · exact le_max_of_le_left (Real.rpow_le_rpow_of_nonpos hm hmt he.le)

theorem max_rpow_nonneg {m M : ℝ} (hm : 0 < m) (e : ℝ) : 0 ≤ max (m ^ e) (M ^ e) :=
  le_max_of_le_left (Real.rpow_nonneg hm.le e)

theorem factor_small_le {m M t s : ℝ} (hm : 0 < m) (hms : m ≤ s) (hsM : s ≤ M) (ht : 0 ≤ t)
    (e δ : ℝ) (hδ : 0 < δ) :
    (t * s) ^ e * (min 1 (t * s)) ^ δ ≤
      (max (m ^ e) (M ^ e) * (max 1 M) ^ δ) * (t ^ e * (min 1 t) ^ δ) := by
  have hs : 0 ≤ s := hm.le.trans hms
  have hc : (1 : ℝ) ≤ max 1 M := le_max_left 1 M
  have hc0 : (0 : ℝ) ≤ max 1 M := zero_le_one.trans hc
  have h1 : (t * s) ^ e = t ^ e * s ^ e := Real.mul_rpow ht hs
  have h2 : s ^ e ≤ max (m ^ e) (M ^ e) := rpow_le_max hm hms hsM e
  have h3 : min 1 (t * s) ≤ max 1 M * min 1 t := by
    rw [mul_min_of_nonneg _ _ hc0, mul_one]
    refine le_min ((min_le_left _ _).trans hc) ((min_le_right _ _).trans ?_)
    rw [mul_comm (max 1 M) t]
    exact mul_le_mul_of_nonneg_left (hsM.trans (le_max_right 1 M)) ht
  have h4 : (min 1 (t * s)) ^ δ ≤ (max 1 M) ^ δ * (min 1 t) ^ δ := by
    rw [← Real.mul_rpow hc0 (le_min zero_le_one ht)]
    exact Real.rpow_le_rpow (le_min zero_le_one (mul_nonneg ht hs)) h3 hδ.le
  rw [h1]
  calc t ^ e * s ^ e * (min 1 (t * s)) ^ δ = t ^ e * (s ^ e * (min 1 (t * s)) ^ δ) := by ring
    _ ≤ t ^ e * (max (m ^ e) (M ^ e) * ((max 1 M) ^ δ * (min 1 t) ^ δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h2 h4 (Real.rpow_nonneg (le_min zero_le_one (mul_nonneg ht hs)) δ)
          (max_rpow_nonneg hm e)) (Real.rpow_nonneg ht e)
    _ = (max (m ^ e) (M ^ e) * (max 1 M) ^ δ) * (t ^ e * (min 1 t) ^ δ) := by ring

theorem factor_large_le {m M t s : ℝ} (hm : 0 < m) (hms : m ≤ s) (hsM : s ≤ M) (ht : 0 ≤ t) (e : ℝ) :
    (t * s) ^ e ≤ max (m ^ e) (M ^ e) * t ^ e := by
  rw [Real.mul_rpow ht (hm.le.trans hms), mul_comm]
  exact mul_le_mul_of_nonneg_right (rpow_le_max hm hms hsM e) (Real.rpow_nonneg ht e)

theorem ideleNorm_rpow_le {m M : ℝ} (hm : 0 < m) (z : (AdeleRing (𝓞 K) K)ˣ) (hz : ((z : (AdeleRing (𝓞 K) K))).2 = 1)
    (hb : ∀ pl : InfinitePlace K, m ≤ ‖((z : (AdeleRing (𝓞 K) K))).1 pl‖ ∧ ‖((z : (AdeleRing (𝓞 K) K))).1 pl‖ ≤ M) (e : ℝ) :
    NumberField.TateGlobal.ideleNorm K z ^ e ≤
      max ((∏ pl : InfinitePlace K, m ^ pl.mult) ^ e) ((∏ pl : InfinitePlace K, M ^ pl.mult) ^ e) := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K z hz]
  refine rpow_le_max (Finset.prod_pos fun pl _ => pow_pos hm _) ?_ ?_ e
  · exact Finset.prod_le_prod (fun pl _ => (pow_pos hm _).le) fun pl _ => pow_le_pow_left₀ hm.le (hb pl).1 _
  · exact Finset.prod_le_prod (fun pl _ => pow_nonneg (norm_nonneg _) _) fun pl _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hb pl).2 _

theorem main
    (K : Type) [Field K] [NumberField K]
    (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (hω : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = x (unipotentGL2 u * g))
    (hZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * x g)
    (hsmall : (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ)))
    (hlarge : (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))))
    (h : AdelicGL2 (𝓞 K) K) (hh : glFin (𝓞 K) K h = 1) :
    (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g' => x (g' * h)) 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ)) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g' => x (g' * h)) 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))) := by
  classical

  obtain ⟨m, M, hm, hmM, hIW⟩ := AutomorphicForm.exists_uniform_iwasawa_mul_of_glFin_eq_one K h hh

  set Zb : ℝ → ℝ := fun e => max ((∏ pl : InfinitePlace K, m ^ pl.mult) ^ e) ((∏ pl : InfinitePlace K, M ^ pl.mult) ^ e)
    with hZb
  have hZb0 : ∀ e, 0 ≤ Zb e := fun e => max_rpow_nonneg (Finset.prod_pos fun pl _ => pow_pos hm _) e

  have key : ∀ (g : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K g = 1 →
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∃ (z b : (AdeleRing (𝓞 K) K)ˣ) (k' : AdelicGL2 (𝓞 K) K),
          ((z : (AdeleRing (𝓞 K) K))).2 = 1 ∧ ((b : (AdeleRing (𝓞 K) K))).2 = 1 ∧ glFin (𝓞 K) K k' = 1 ∧
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k'))) ∧
          (∀ pl : InfinitePlace K, m ≤ ‖((z : (AdeleRing (𝓞 K) K))).1 pl‖ ∧ ‖((z : (AdeleRing (𝓞 K) K))).1 pl‖ ≤ M ∧
            m ≤ ‖((b : (AdeleRing (𝓞 K) K))).1 pl‖ ∧ ‖((b : (AdeleRing (𝓞 K) K))).1 pl‖ ≤ M) ∧
          ∀ a : (AdeleRing (𝓞 K) K)ˣ,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g' => x (g' * h)) 1
          (diagOne a * k * g)‖ =
              NumberField.TateGlobal.ideleNorm K z ^ w *
                ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne (a * b) * k' * g)‖ := by
    intro g hg k hk hkiso
    obtain ⟨ν, z, b, k', hν, hz, hb, hk', hk'iso, hkh, hbd⟩ := hIW k hk hkiso
    refine ⟨z, b, k', hz, hb, hk', hk'iso, hbd, fun a => ?_⟩
    have hgh : g * h = h * g := mul_comm_of_glArch_eq_one_of_glFin_eq_one K hg hh
    have hdec : diagOne a * k * g * h =
        unipotentGL2 (((a : (AdeleRing (𝓞 K) K))) * ν) * (centralScalar (𝓞 K) K z * (diagOne (a * b) * k' * g)) := by
      calc diagOne a * k * g * h = diagOne a * k * (g * h) := mul_assoc _ _ _
        _ = diagOne a * k * (h * g) := by rw [hgh]
        _ = diagOne a * (k * h) * g := by simp only [mul_assoc]
        _ = diagOne a * (unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne b * k') * g := by rw [hkh]
        _ = (diagOne a * unipotentGL2 ν) * centralScalar (𝓞 K) K z * diagOne b * k' * g := by
            simp only [mul_assoc]
        _ = unipotentGL2 (((a : (AdeleRing (𝓞 K) K))) * ν) * (diagOne a * centralScalar (𝓞 K) K z) * diagOne b * k' * g := by
            rw [diagOne_mul_unipotentGL2]; simp only [mul_assoc]
        _ = unipotentGL2 (((a : (AdeleRing (𝓞 K) K))) * ν) * (centralScalar (𝓞 K) K z * (diagOne (a * b) * k' * g)) := by
            rw [← centralScalar_mul_comm, map_mul]; simp only [mul_assoc]
    have hu : ((((a : (AdeleRing (𝓞 K) K))) * ν)).2 = 0 := by
      show ((a : (AdeleRing (𝓞 K) K))).2 * ν.2 = 0
      rw [hν, mul_zero]
    rw [whittakerCoefficient_translate, hdec, whittakerCoefficient_unipotent K D₀ x hper,
      whittakerCoefficient_centralScalar_mul K D₀ x ω hZ, norm_mul, norm_mul,
      norm_stdAddChar_of_snd_eq_zero K _ hu, one_mul, hω]
  refine ⟨fun g hg => ?_, fun g hg Mexp => ?_⟩
  ·
    obtain ⟨δ, hδ, Cg, hCg⟩ := hsmall g hg
    refine ⟨δ, hδ, Zb w * max Cg 0 * ∏ pl : InfinitePlace K,
      (max (m ^ ((pl.mult : ℝ) * w / 2)) (M ^ ((pl.mult : ℝ) * w / 2)) * (max 1 M) ^ δ), ?_⟩
    intro k hk hkiso a ha
    obtain ⟨z, b, k', hz, hb, hk', hk'iso, hbd, hkey⟩ := key g hg k hk hkiso
    have hab : (((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).2 = 1 := by rw [snd_units_mul, ha, hb, one_mul]
    have hW := hCg k' hk' hk'iso (a * b) hab
    set F : ℝ → ℝ → ℝ := fun e t => t ^ e * (min 1 t) ^ δ with hF
    have hF0 : ∀ e t, 0 ≤ t → 0 ≤ F e t := fun e t ht =>
      mul_nonneg (Real.rpow_nonneg ht e) (Real.rpow_nonneg (le_min zero_le_one ht) δ)

    have hprod : (∏ pl : InfinitePlace K, (‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
        (min 1 ‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖) ^ δ)) ≤
        (∏ pl : InfinitePlace K, (max (m ^ ((pl.mult : ℝ) * w / 2)) (M ^ ((pl.mult : ℝ) * w / 2)) * (max 1 M) ^ δ)) *
        ∏ pl : InfinitePlace K, (‖((a : (AdeleRing (𝓞 K) K))).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
          (min 1 ‖((a : (AdeleRing (𝓞 K) K))).1 pl‖) ^ δ) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun pl _ => ?_) (fun pl _ => ?_)
      · exact hF0 _ _ (norm_nonneg _)
      · rw [fst_units_mul_apply, norm_mul]
        exact factor_small_le hm (hbd pl).2.2.1 (hbd pl).2.2.2 (norm_nonneg _) _ δ hδ
    have hS0 : 0 ≤ ∏ pl : InfinitePlace K, (‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
        (min 1 ‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖) ^ δ) :=
      Finset.prod_nonneg fun pl _ => hF0 _ _ (norm_nonneg _)
    rw [hkey a]
    calc NumberField.TateGlobal.ideleNorm K z ^ w * ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne (a * b) * k' * g)‖
        ≤ Zb w * (max Cg 0 * ∏ pl : InfinitePlace K, (‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
            (min 1 ‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖) ^ δ)) := by
          refine mul_le_mul (ideleNorm_rpow_le K hm z hz (fun pl => ⟨(hbd pl).1, (hbd pl).2.1⟩) w)
            (hW.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS0)) (norm_nonneg _) (hZb0 w)
      _ ≤ Zb w * (max Cg 0 * ((∏ pl : InfinitePlace K, (max (m ^ ((pl.mult : ℝ) * w / 2)) (M ^ ((pl.mult : ℝ) * w / 2)) *
            (max 1 M) ^ δ)) * ∏ pl : InfinitePlace K, (‖((a : (AdeleRing (𝓞 K) K))).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : (AdeleRing (𝓞 K) K))).1 pl‖) ^ δ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (le_max_right _ _)) (hZb0 w)
      _ = _ := by ring
  ·
    obtain ⟨Cg, hCg⟩ := hlarge g hg Mexp
    refine ⟨Zb w * max Cg 0 * Zb (w / 2) * max (m ^ (-(Mexp : ℝ))) (M ^ (-(Mexp : ℝ))), ?_⟩
    intro k hk hkiso a ha pl
    obtain ⟨z, b, k', hz, hb, hk', hk'iso, hbd, hkey⟩ := key g hg k hk hkiso
    have hab : (((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).2 = 1 := by rw [snd_units_mul, ha, hb, one_mul]
    have hW := hCg k' hk' hk'iso (a * b) hab pl
    have hNab : NumberField.TateGlobal.ideleNorm K (a * b) ^ (w / 2) =
        NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * NumberField.TateGlobal.ideleNorm K b ^ (w / 2) := by
      rw [NumberField.TateGlobal.ideleNorm_mul, Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos a).le
        (NumberField.TateGlobal.ideleNorm_pos b).le]
    have hNb : NumberField.TateGlobal.ideleNorm K b ^ (w / 2) ≤ Zb (w / 2) :=
      ideleNorm_rpow_le K hm b hb (fun pl => ⟨(hbd pl).2.2.1, (hbd pl).2.2.2⟩) (w / 2)
    have hpl : ‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖ ^ (-(Mexp : ℝ)) ≤
        max (m ^ (-(Mexp : ℝ))) (M ^ (-(Mexp : ℝ))) * ‖((a : (AdeleRing (𝓞 K) K))).1 pl‖ ^ (-(Mexp : ℝ)) := by
      rw [fst_units_mul_apply, norm_mul]
      exact factor_large_le hm (hbd pl).2.2.1 (hbd pl).2.2.2 (norm_nonneg _) _
    have hNa0 : 0 ≤ NumberField.TateGlobal.ideleNorm K a ^ (w / 2) :=
      Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos a).le _
    have ha0 : 0 ≤ ‖((a : (AdeleRing (𝓞 K) K))).1 pl‖ ^ (-(Mexp : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hS0 : 0 ≤ NumberField.TateGlobal.ideleNorm K (a * b) ^ (w / 2) * ‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖ ^ (-(Mexp : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _) (Real.rpow_nonneg (norm_nonneg _) _)
    rw [hkey a]
    calc NumberField.TateGlobal.ideleNorm K z ^ w * ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne (a * b) * k' * g)‖
        ≤ Zb w * (max Cg 0 * (NumberField.TateGlobal.ideleNorm K (a * b) ^ (w / 2) *
            ‖(((a * b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))).1 pl‖ ^ (-(Mexp : ℝ)))) := by
          refine mul_le_mul (ideleNorm_rpow_le K hm z hz (fun pl => ⟨(hbd pl).1, (hbd pl).2.1⟩) w)
            (hW.trans ?_) (norm_nonneg _) (hZb0 w)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
      _ ≤ Zb w * (max Cg 0 * ((NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * Zb (w / 2)) *
            (max (m ^ (-(Mexp : ℝ))) (M ^ (-(Mexp : ℝ))) * ‖((a : (AdeleRing (𝓞 K) K))).1 pl‖ ^ (-(Mexp : ℝ))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)) (hZb0 w)
          rw [hNab]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hNb hNa0) hpl (Real.rpow_nonneg (norm_nonneg _) _)
            (mul_nonneg hNa0 (hZb0 _))
      _ = _ := by ring

end IWTRANSFER43

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (_hω : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (_hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = x (unipotentGL2 u * g))
    (_hZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * x g)
    (_hsmall : (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ)))
    (_hlarge : (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))))
    (h : AdelicGL2 (𝓞 K) K) (_hh : glFin (𝓞 K) K h = 1) :
    (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g' => x (g' * h)) 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ)) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g' => x (g' * h)) 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))) :=
  IWTRANSFER43.main K D₀ ω w _hω x _hper _hZ _hsmall _hlarge h _hh

end S_AutomorphicForm_norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one
end P2MW
export P2MW.S_AutomorphicForm_norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one (solution)
