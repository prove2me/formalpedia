-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
-- name    : OAI_Analysis_SegmentLenses_LawRecovery
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:56:42.353402+00:00
-- url     : https://prove2.me/theorems/f85e1838-2ab2-4c0d-8614-7faa26a58c66
-- title:
--   Vector-valued expectations, product and pooled laws, and coefficient laws with normalized atoms
-- statement:
--   Let $\Omega$ and $\Omega'$ be finite sets carrying finite laws, i.e. probability weight functions, $\mu$ and $\nu$. On the segment side, $V$ carries a segment system and $J_V^{*}$ is the dual of the segment-norm completion. The segment functionals are $\sigma_S=\sum_{v\in S}e_v^{*}$, the unit vectors are $e_g$, and a representation $(\mathcal F,c)$ is a segment family $\mathcal F$ with coefficients $c\in\ell_2(\mathcal F)$, value $\sum_Sc_S\sigma_S$ and energy $\sum_Sc_S^2$.
--
--   1. **Expectation.** For $f:\Omega\to E$ with values in a real vector space $E$,
--   $$
--   \mathbb{E}_\mu f=\sum_{\omega\in\Omega}\mu(\omega)\,f(\omega).
--   $$
--   It has the expected algebraic properties:
--      - it is normalized on constants and additive, compatible with subtraction (when $E$ is a group), and homogeneous: $\mathbb{E}_\mu(af)=a\,\mathbb{E}_\mu f$;
--      - it commutes with every linear map: $\mathbb{E}_\mu(T\circ f)=T(\mathbb{E}_\mu f)$;
--      - for real-valued $f$ it is the mean, and the mean of a finite sum $\sum_i f_i$ is the sum of the means.
--   2. **Product and pooled laws.** The product law on $\Omega\times\Omega'$ has weights $\mu(\omega)\nu(\omega')$. The pooled law on the disjoint union $\Omega\sqcup\Omega'$ has weights $\mu(\omega)/2$ and $\nu(\omega')/2$, i.e. it is the equal mixture.
--   3. **Representations from coefficients.** For a segment family $\mathcal F$ and $c\in\ell_2(\mathcal F)$, the representation $(\mathcal F,c)$ has value $\Lambda_{\mathcal F}c=\sum_Sc_S\sigma_S$ and energy $\|c\|_2^2$.
--   4. **Coefficient law and atoms.** Let $K\subseteq V$ be finite (with decidable equality on $V$). Let $c=(c_{\mathcal F})$ be local coefficients on $K$, one vector $c_{\mathcal F}\in\ell_2(\mathcal F)$ for each local family $\mathcal F$ of $K$, with budget $\beta_K(c)=\sum_{\mathcal F}\|c_{\mathcal F}\|_2\le1$. The coefficient law is the finite law on $\{\ast\}\cup\{\text{local families of }K\}$ given by
--   $$
--   \mu_c(\ast)=1-\beta_K(c),\qquad \mu_c(\mathcal F)=\|c_{\mathcal F}\|_2 .
--   $$
--   The atoms are $A_\ast$, the zero representation on the empty family, and $A_{\mathcal F}=(\mathcal F,\ c_{\mathcal F}/\|c_{\mathcal F}\|_2)$, which is taken to be $0$ when $c_{\mathcal F}=0$.
--   5. **Values at unit vectors.** $\sigma_S(e_g)=1$ if $g\in S$ and $0$ otherwise. Consequently the value of a representation satisfies $\big(\sum_Sc_S\sigma_S\big)(e_g)=\sum_{S\in\mathcal F,\ g\in S}c_S$.
--
--   Since $\|c_{\mathcal F}\|_2\cdot c_{\mathcal F}/\|c_{\mathcal F}\|_2=c_{\mathcal F}$, the expectation of the atom values under $\mu_c$ is exactly $\sum_{\mathcal F}\Lambda_{\mathcal F}c_{\mathcal F}$, and every atom has energy at most $1$. This turns membership in an atomic body into a statement about the average of finitely many low-energy representations.
--
--   **Formalization Note** The extra point $\ast$ is `none` in `Option (LocalFamily K)`, and the atom normalization uses Lean's convention $0^{-1}=0$. The definitions are `expect`, `product`, `pooled`, `representation`, `coefficientLaw` (which takes the budget hypothesis as an argument) and `coefficientAtoms`. The lemmas are `expect_const`, `expect_add`, `expect_sub`, `expect_smul`, `expect_map`, `expect_scalar`, `mean_sum`, `representation_value`, `representation_energy`, `segmentFunctional_unitVector` and `Representation.apply_unitVector`. The last two are stated with the tree-order and interval-segment assumptions in scope.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/LawRecovery.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/LawRecovery.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls

namespace OAI

/-!
# Exact finite-law recovery and coefficient representations
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def expect (μ : FiniteLaw Ω) {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : Ω → E) : E :=
  ∑ ω, μ.weight ω • f ω

@[simp] theorem expect_const (μ : FiniteLaw Ω) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (c : E) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_smul, μ.total, one_smul]

@[simp] theorem expect_add (μ : FiniteLaw Ω) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f g : Ω → E) : μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp only [expect, smul_add, Finset.sum_add_distrib]

@[simp] theorem expect_sub (μ : FiniteLaw Ω) {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f g : Ω → E) : μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp only [expect, smul_sub, Finset.sum_sub_distrib]

@[simp] theorem expect_smul (μ : FiniteLaw Ω) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a : ℝ) (f : Ω → E) : μ.expect (fun ω => a • f ω) = a • μ.expect f := by
  simp only [expect, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  exact smul_comm _ _ _

@[simp] theorem expect_map (μ : FiniteLaw Ω) {E F : Type*} [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F] (T : E →ₗ[ℝ] F) (f : Ω → E) :
    μ.expect (fun ω => T (f ω)) = T (μ.expect f) := by
  simp only [expect, map_sum, map_smul]

@[simp] theorem expect_scalar (μ : FiniteLaw Ω) (f : Ω → ℝ) : μ.expect f = μ.mean f := rfl

@[simp] theorem mean_sum (μ : FiniteLaw Ω) {ι : Type*} [Fintype ι] (f : Ω → ι → ℝ) :
    μ.mean (fun ω => ∑ i, f ω i) = ∑ i, μ.mean (fun ω => f ω i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

def product {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') :
    FiniteLaw (Ω × Ω') where
  weight ω := μ.weight ω.1 * ν.weight ω.2
  nonneg ω := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, μ.total, ν.total]

def pooled {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') :
    FiniteLaw (Ω ⊕ Ω') where
  weight := Sum.elim (fun ω => μ.weight ω / 2) (fun ω => ν.weight ω / 2)
  nonneg := fun ω => by cases ω <;> apply div_nonneg <;> first | exact μ.nonneg _ | exact ν.nonneg _ | norm_num
  total := by norm_num [Fintype.sum_sum_type, ← Finset.sum_div, μ.total, ν.total]

end FiniteLaw

section LawRecovery
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

def representation (F : SegmentFamily V) (c : FamilyCoefficients F) : Representation V := ⟨F, c⟩

@[simp] theorem representation_value (F : SegmentFamily V) (c : FamilyCoefficients F) :
    (representation F c).value = familyValue F c := by
  have _ := decidableEqV
  exact rfl

@[simp] theorem representation_energy (F : SegmentFamily V) (c : FamilyCoefficients F) :
    (representation F c).energy = ‖c‖ ^ 2 := by
  have _ := decidableEqV
  change (∑ S : F.sets, c S ^ 2) = ‖c‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

def coefficientLaw (K : Finset V) (c : LocalCoefficients K) (hc : coefficientBudget K c ≤ 1) :
    FiniteLaw (Option (LocalFamily K)) where
  weight ω := ω.elim (1 - coefficientBudget K c) (fun F => ‖c F‖)
  nonneg ω := by cases ω with
    | none => exact sub_nonneg.mpr hc
    | some F => exact norm_nonneg _
  total := by simp [Fintype.sum_option, coefficientBudget]

def coefficientAtoms (K : Finset V) (c : LocalCoefficients K) :
    Option (LocalFamily K) → Representation V :=
  fun ω => ω.elim (representation default 0)
    (fun F => representation F.val (‖c F‖⁻¹ • c F))

end LawRecovery

namespace FiniteLaw
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end FiniteLaw

section RepresentationGates
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

@[simp] theorem segmentFunctional_unitVector (S : Finset V) (g : V) :
    segmentFunctional S (unitVector g) = if g ∈ S then 1 else 0 := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  simp [segmentFunctional, coordinate_unitVector, eq_comm]

@[simp] theorem Representation.apply_unitVector (A : Representation V) (g : V) :
    A.value (unitVector g) = ∑ S : A.family.sets, if g ∈ S.val then A.coeff S else 0 := by
  simp [Representation.value, segmentFunctional_unitVector, mul_ite]

end RepresentationGates

end SegmentLenses

end

end OAI


