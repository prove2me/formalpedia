-- Prove2me | Definitions.Def_LanglandsTunnell_TorusTransform
-- name    : LanglandsTunnell_TorusTransform
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/87540ecf-22cd-59f8-8c10-35f2a935bdd5
-- title:
--   Idèle components, norm-one torus classes, dual Whittaker series
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal O_K$ and adele ring $\mathbb A$. A first group of declarations extracts local data from an idèle. For a finite place $v$ and $z \in \mathbb A^{\times}$, `unitAt v z` is the unit of the completion $K_v$ whose value is the $v$-component of $z$ and whose inverse is the $v$-component of $z^{-1}$; the two auxiliary lemmas `val_mul_inv_snd_apply` and `val_inv_mul_snd_apply` supply the two unit identities, and `unitAt_mul`, `unitAt_one`, `unitAt_inv` record multiplicativity. At an infinite place $w$, `expAt w s` is the element of $K_w$ corresponding to $e^{s} \in \mathbb R$ or to $\exp(s) \in \mathbb C$ under the identification of $K_w$ with $\mathbb R$ or $\mathbb C$; `norm_expAt` gives $\|{\rm expAt}\,w\,s\| = e^{s}$, whence `expAt_ne_zero` and the unit `expUnitAt`. With `archProd` forming the product over a finite set of infinite places of the images of one-place units under `archUnitHom`, the idèle `archScale K t` has component $e^{t/[K:\mathbb Q]}$ at every infinite place, so that its idèle norm scales by $e^{t}$.
--
--   Next, `unitIdelesAt S` is the subgroup of $\mathbb A^{\times}$ consisting of idèles whose component at each $v \in S$ has valuation exactly $1$, for $S$ a finite set of finite places. `NormOneQuot K` is the quotient of the norm-one idèles by the principal idèles lying in them, and `torusClass S` is the image in this quotient of the norm-one idèles belonging to `unitIdelesAt S`; `mem_torusClass_iff` characterises membership by the existence of such a representative, and `torusLift` chooses one, so that constructions using it depend on that choice only up to a principal norm-one idèle. `torusBorel S` is the Borel $\sigma$-algebra of `torusClass S`, with `borelSpace_torusBorel` asserting the corresponding Borel-space property (neither is installed as an instance). For a base point $g \in \mathrm{GL}_2(\mathbb A)$, `torusPoint g (c,t)` is $\mathrm{diag}(\tilde c\,\cdot\,\mathrm{archScale}\,K\,t,\,1)\,g$, where $\tilde c$ is the chosen lift of the class $c$: a parametrisation of the split-torus directions through $g$ by $\mathrm{torusClass}\,S \times \mathbb R$.
--
--   Finally, a dual Whittaker expansion. `weylGL2 K` is the element of $\mathrm{GL}_2(K)$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, and for $d$ a `JLData` over $K$, $S$, local characters `epsS` and central character $\omega$, `weylA d` is `weylGL2 K` times $\mathrm{diag}(-d.A,1)$, whose matrix is $\begin{pmatrix}0&1\\ d.A&0\end{pmatrix}$ (`weylA_coe`). For archimedean parameters `archR`, `archC` with data `dR`, `dC` at the real and complex places, a finite Whittaker datum `dF` for a Hecke eigensystem, a point $g$ and $\alpha \in K^{\times}$, `dualSeriesTerm` is the product of $d.ad\,\alpha$, the value $d.{\rm epsChar}\,g$ (the product over $v \in S$ of extended local characters of the lower-right and the ratio of diagonal entries, when $g$ lies in the prescribed local sets, and $0$ otherwise), and the archimedean factor `archW'` and the finite Whittaker function `dF.Wf`, both evaluated at $\mathrm{diag}(\alpha,1)\,({\rm weylA}\,d)\,g$ with the rational matrix embedded into the adelic group. `dualSeries'` is the sum of these terms over $\alpha \in K^{\times}$, taken as an unconditional sum; it is the Weyl-twisted counterpart of the Whittaker series used to build the automorphic form.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring and its units, the finite and infinite completions with their identifications with $\mathbb R$ and $\mathbb C$, quotient groups and the Borel construction; the component map at a finite place, the unit-at-$S$ subgroup, the norm-one idèle class quotient with its torus subgroup, and the dual Whittaker series are the project's own.
--
--   **Where it is used.** These objects belong to the converse-theorem half of the Langlands–Tunnell input: the torus classes and the archimedean scaling line parametrise the directions along which growth and cuspidality of a candidate automorphic function are tested, while the dual series is the Weyl-reflected Whittaker expansion compared with the original one in the functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_TorusTransform.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_JLSynthesis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell.Converse

noncomputable section

section
open scoped WithZero
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology
namespace LanglandsTunnell.Converse.Ideles
variable {K : Type} [Field K] [NumberField K]
local notation "𝔸" => AdeleRing (𝓞 K) K
theorem val_mul_inv_snd_apply (z : 𝔸ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (z : 𝔸).2 v * ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v = 1 :=
  congrArg (fun x : 𝔸 => x.2 v) z.mul_inv
end LanglandsTunnell.Converse.Ideles
end
end

section
open scoped WithZero
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology
namespace LanglandsTunnell.Converse.Ideles
variable {K : Type} [Field K] [NumberField K]
local notation "𝔸" => AdeleRing (𝓞 K) K
theorem val_inv_mul_snd_apply (z : 𝔸ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v * (z : 𝔸).2 v = 1 :=
  congrArg (fun x : 𝔸 => x.2 v) z.inv_mul
end LanglandsTunnell.Converse.Ideles
end
end

section
open scoped WithZero
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology
namespace LanglandsTunnell.Converse.Ideles
variable {K : Type} [Field K] [NumberField K]
local notation "𝔸" => AdeleRing (𝓞 K) K

def archProd (a : ∀ w : InfinitePlace K, (w.Completion)ˣ) (T : Finset (InfinitePlace K)) : 𝔸ˣ :=
  ∏ w ∈ T, archUnitHom w (a w)
end LanglandsTunnell.Converse.Ideles
end
end

section
open scoped WithZero
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology
namespace LanglandsTunnell.Converse.Ideles
variable {K : Type} [Field K] [NumberField K]
local notation "𝔸" => AdeleRing (𝓞 K) K

def unitAt (v : HeightOneSpectrum (𝓞 K)) (z : 𝔸ˣ) : (v.adicCompletion K)ˣ where
  val := (z : 𝔸).2 v
  inv := ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v
  val_inv := val_mul_inv_snd_apply z v
  inv_val := val_inv_mul_snd_apply z v
end LanglandsTunnell.Converse.Ideles
end
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]

noncomputable def expAt (w : InfinitePlace K) (s : ℝ) : w.Completion :=
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm (Real.exp s)
  else (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (Complex.exp s)
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]
theorem norm_expAt (w : InfinitePlace K) (s : ℝ) : ‖expAt w s‖ = Real.exp s := by
  unfold expAt
  split_ifs with hw
  · have h := (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)
      ((ringEquivRealOfIsReal hw).symm (Real.exp s))
    rw [← h]
    change ‖ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm (Real.exp s))‖ = _
    rw [RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  · set hc := not_isReal_iff_isComplex.mp hw
    have h := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
      ((ringEquivComplexOfIsComplex hc).symm (Complex.exp s))
    rw [← h]
    change ‖ringEquivComplexOfIsComplex hc ((ringEquivComplexOfIsComplex hc).symm (Complex.exp s))‖ = _
    rw [RingEquiv.apply_symm_apply, Complex.norm_exp_ofReal]
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]
theorem expAt_ne_zero (w : InfinitePlace K) (s : ℝ) : expAt w s ≠ 0 := by
  intro h
  have := norm_expAt w s
  rw [h, norm_zero] at this
  exact (Real.exp_pos s).ne this
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]

noncomputable def expUnitAt (w : InfinitePlace K) (s : ℝ) : (w.Completion)ˣ := Units.mk0 _ (expAt_ne_zero w s)
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
namespace LanglandsTunnell.Converse.Ideles
section ScalingLine
variable {K : Type} [Field K]
variable [NumberField K]
variable (K) in

noncomputable def archScale (t : ℝ) : (AdeleRing (𝓞 K) K)ˣ :=
  archProd (fun w => expUnitAt w (t / Module.finrank ℚ K)) Finset.univ
end ScalingLine
end LanglandsTunnell.Converse.Ideles
end

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles
theorem unitAt_mul (v : HeightOneSpectrum (𝓞 K)) (a b : (AdeleRing (𝓞 K) K)ˣ) :
    unitAt v (a * b) = unitAt v a * unitAt v b := Units.ext rfl
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles
theorem unitAt_one (v : HeightOneSpectrum (𝓞 K)) : unitAt v (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := Units.ext rfl
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles
theorem unitAt_inv (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ) : unitAt v a⁻¹ = (unitAt v a)⁻¹ :=
  Units.ext rfl
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles

def unitIdelesAt (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (AdeleRing (𝓞 K) K)ˣ where
  carrier := {a | ∀ v : ↥S, Valued.v (unitAt v.1 a : v.1.adicCompletion K) = 1}
  mul_mem' {a b} ha hb v := by
    show Valued.v (unitAt v.1 (a * b) : v.1.adicCompletion K) = 1
    rw [unitAt_mul, Units.val_mul, map_mul, ha v, hb v, one_mul]
  one_mem' v := by
    show Valued.v (unitAt v.1 1 : v.1.adicCompletion K) = 1
    rw [unitAt_one, Units.val_one, map_one]
  inv_mem' {a} ha v := by
    show Valued.v (unitAt v.1 a⁻¹ : v.1.adicCompletion K) = 1
    rw [unitAt_inv, Units.val_inv_eq_inv_val, map_inv₀, ha v, inv_one]
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusModel
open LanglandsTunnell.Converse.Ideles
variable (K) in

abbrev NormOneQuot : Type :=
  ↥(normOneIdeles K) ⧸ (M4aHerbrand.principalIdeles (𝓞 K) K).subgroupOf (normOneIdeles K)
end TorusModel
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

noncomputable def torusClass (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (NormOneQuot K) :=
  ((unitIdelesAt S).subgroupOf (normOneIdeles K)).map (QuotientGroup.mk' _)
end TorusClass
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal
theorem mem_torusClass_iff {S : Finset (HeightOneSpectrum (𝓞 K))} {q : NormOneQuot K} :
    q ∈ torusClass S ↔
      ∃ x : ↥(normOneIdeles K), (x : (AdeleRing (𝓞 K) K)ˣ) ∈ unitIdelesAt S ∧ QuotientGroup.mk x = q := by
  simp only [torusClass, Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply]
end TorusClass
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell.Converse.CuspSynthesis
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

noncomputable def torusLift {S : Finset (HeightOneSpectrum (𝓞 K))} (q : ↥(torusClass (K := K) S)) :
    ↥(normOneIdeles K) :=
  Classical.choose (mem_torusClass_iff.1 q.2)
end TorusClass
end
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section
namespace LanglandsTunnell.Converse.CuspSynthesis
open MeasureTheory Topology
section TorusMeasure
variable {K : Type} [Field K] [NumberField K]

@[reducible] def torusBorel (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSpace ↥(torusClass (K := K) S) :=
  borel _
end TorusMeasure
end LanglandsTunnell.Converse.CuspSynthesis
end

noncomputable section
namespace LanglandsTunnell.Converse.CuspSynthesis
open MeasureTheory Topology
section TorusMeasure
variable {K : Type} [Field K] [NumberField K]
theorem borelSpace_torusBorel (S : Finset (HeightOneSpectrum (𝓞 K))) :
    @BorelSpace ↥(torusClass (K := K) S) _ (torusBorel S) :=
  @BorelSpace.mk _ _ (torusBorel S) rfl
end TorusMeasure
end LanglandsTunnell.Converse.CuspSynthesis
end

noncomputable section
namespace LanglandsTunnell.Converse.CuspSynthesis
open MeasureTheory Topology
section TorusMeasure
variable {K : Type} [Field K] [NumberField K]

def torusPoint {S : Finset (HeightOneSpectrum (𝓞 K))} (g : AdelicGL2 (𝓞 K) K)
    (p : ↥(torusClass (K := K) S) × ℝ) : AdelicGL2 (𝓞 K) K :=
  diagOne (((torusLift p.1 : ↥(normOneIdeles K)) : (AdeleRing (𝓞 K) K)ˣ) * Ideles.archScale K p.2) * g
end TorusMeasure
end LanglandsTunnell.Converse.CuspSynthesis
end

namespace LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

section DualSeries

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
variable {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

open scoped Classical
open scoped WithZero
open LanglandsTunnell.TateLocal NumberField.StandardAddChar NumberField.InfinitePlace UnramifiedWhittaker

variable (K) in

def weylGL2 : GL (Fin 2) K where
  val := !![0, 1; -1, 0]
  inv := !![0, -1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NumberField K] in
theorem weylGL2_coe : ((weylGL2 K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

def weylA (d : JLData K S epsS ω) : GL (Fin 2) K := weylGL2 K * diagOne (-d.A)

theorem weylA_coe (d : JLData K S epsS ω) :
    ((weylA d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; (d.A : K), 0] := by
  refine Matrix.ext fun i j => ?_
  simp only [weylA, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, weylGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

def dualSeriesTerm (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) (α : Kˣ) : ℂ :=
  d.ad α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α * weylA d) * g)
    * dF.Wf (globalPoints (𝓞 K) K (diagOne α * weylA d) * g)

def dualSeries' (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∑' α : Kˣ, dualSeriesTerm d archR archC dR dC dF g α

end DualSeries

end

end LanglandsTunnell.Converse.CuspSynthesis


