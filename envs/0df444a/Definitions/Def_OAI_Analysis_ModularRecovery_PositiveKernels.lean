-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_PositiveKernels
-- name    : OAI_Analysis_ModularRecovery_PositiveKernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:24:31.282953+00:00
-- url     : https://prove2.me/theorems/e0502006-b10b-49f9-99c9-e281c80c56e7
-- title:
--   Modular kernels from the commutant into the algebra
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Weighted matrix functional.** For a functional $\phi$ and weights $w_i$, the functional $(a_{ij})\mapsto\sum_iw_i\phi(a_{ii})$ on matrices over a C*-algebra.
--   2. **State and commuting pairing.** $\phi(c)=\langle\xi,c\xi\rangle$ on $M$, and for $b\in M'$ the functional $c\mapsto\langle\xi,bc\xi\rangle$ on $M$.
--   3. **Modular kernel.** For $r\in\mathbb R$ and $b\in M'$, the element $K_r(b)=e^{r/2}a\in M$, where $a\xi=(e^r+\Delta)^{-1}b\xi$. It is characterized by the weak equation
--   $$
--   e^r\phi\bigl(cK_r(b)\bigr)+\phi\bigl(K_r(b)c\bigr)=e^{r/2}\langle\xi,bc\xi\rangle\qquad(c\in M).
--   $$
--   4. **Kernel scalar and matrices.** $\kappa(r)=e^{r/2}/(e^r+1)=1/(2\cosh(r/2))$, the Gram matrices $\bigl(K_{r_i-r_j}(b_j^*b_i)\bigr)_{ij}$ and $\bigl(K_{r_i-r_j}(b)\bigr)_{ij}$. These are positive, which bounds $\|K_r(b)\|$ by a multiple of $\|b\|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/PositiveKernels.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/PositiveKernels.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAI_Analysis_ModularRecovery_Model
import Definitions.Def_OAI_Analysis_ModularRecovery_SpectralCalculus
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaResolvent
import Definitions.Def_OAI_Analysis_ModularRecovery_PolarCutoff
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaFundamental
import Definitions.Def_OAI_Analysis_ModularRecovery_RealGraph
import Definitions.Def_OAI_Analysis_ModularRecovery_Commutant

-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

namespace OAI

/-! Positive operator kernels, matrix pairings, and norm bounds. -/

universe u uA uM uN

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open scoped ComplexConjugate
namespace BoundedRecovery

section Lyapunov
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma nonneg_of_jordan_pairing (φ : A →ₗ[ℂ] ℂ)
    (hp : ∀ a : A, 0 ≤ (φ (star a * a)).re)
    (hf : ∀ a : A, (φ (star a * a)).re = 0 → a = 0)
    (x : A) (hx : IsSelfAdjoint x)
    (ht : ∀ y : A, 0 ≤ y → 0 ≤ (φ (x*y+y*x)).re) : 0 ≤ x := by
  have hn : IsSelfAdjoint x⁻ := (CFC.negPart_nonneg x).isSelfAdjoint
  have h1 : x * x⁻ = -(x⁻ * x⁻) := by
    calc
      x * x⁻ = (x⁺-x⁻) * x⁻ := congrArg (fun y : A => y*x⁻) (CFC.posPart_sub_negPart x hx).symm
      _ = _ := by simp [sub_mul]
  have h2 : x⁻ * x = -(x⁻ * x⁻) := by
    calc
      x⁻ * x = x⁻ * (x⁺-x⁻) := congrArg (fun y : A => x⁻*y) (CFC.posPart_sub_negPart x hx).symm
      _ = _ := by simp [mul_sub]
  have hh := ht x⁻ (CFC.negPart_nonneg x)
  rw [h1,h2] at hh
  simp only [map_add,map_neg,Complex.add_re,Complex.neg_re] at hh
  have hc := hp x⁻
  rw [hn.star_eq] at hc
  have he : (φ (star x⁻ * x⁻)).re = 0 := by
    rw [hn.star_eq]
    linarith
  exact (CFC.negPart_eq_zero_iff x hx).mp (hf x⁻ he)

end Lyapunov

section Matrices
variable {A : Type uA} {n : Type uN} [CStarAlgebra A] [Fintype n]

def weightedMatrixFunctional (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ) :
    CStarMatrix n n A →ₗ[ℂ] ℂ where
  toFun a := ∑ i, (w i : ℂ) * φ (a i i)
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [CStarMatrix.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

lemma weightedMatrixFunctional_star_mul (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ)
    (a : CStarMatrix n n A) :
    (weightedMatrixFunctional φ w (star a*a)).re =
      ∑ i, w i * ∑ j, (φ (star (a j i) * a j i)).re := by
  simp [weightedMatrixFunctional, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
    CStarMatrix.conjTranspose_apply, Complex.mul_re]

lemma weightedMatrixFunctional_nonneg (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ a : A, 0 ≤ (φ (star a*a)).re)
    (a : CStarMatrix n n A) :
    0 ≤ (weightedMatrixFunctional φ w (star a*a)).re := by
  rw [weightedMatrixFunctional_star_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Finset.sum_nonneg (fun j _ => hp _)))

lemma weightedMatrixFunctional_faithful (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ)
    (hw : ∀ i, 0 < w i) (hp : ∀ a : A, 0 ≤ (φ (star a*a)).re)
    (hf : ∀ a : A, (φ (star a*a)).re = 0 → a = 0)
    (a : CStarMatrix n n A) (ha : (weightedMatrixFunctional φ w (star a*a)).re = 0) : a = 0 := by
  rw [weightedMatrixFunctional_star_mul] at ha
  have hh (i : n) : ∑ j, (φ (star (a j i)*a j i)).re = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hw k).le
      (Finset.sum_nonneg (fun j _ => hp (a j k))))).mp ha i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hs).resolve_left (hw i).ne'
  ext i j
  apply hf
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hp (a k j))).mp (hh j) i (Finset.mem_univ i)

end Matrices
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vonNeumannAlgebra_complete (M : VonNeumannAlgebra H) : CompleteSpace M.toStarSubalgebra :=
  (vonNeumannAlgebra_isClosed M).completeSpace_coe

namespace StandardModularData

def phi (S : StandardModularData H) : S.M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun a := inner ℂ S.xi ((a : H →L[ℂ] H) S.xi)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma phi_star_mul (S : StandardModularData H) (a : S.M.toStarSubalgebra) :
    (S.phi (star a*a)).re = ‖(a : H →L[ℂ] H) S.xi‖^2 := by
  change ((vectorStateLM S.xi) (star (a:H →L[ℂ] H)*(a:H →L[ℂ] H))).re = _
  rw [vectorState_star_mul]
  rfl

lemma phi_nonneg (S : StandardModularData H) (a : S.M.toStarSubalgebra) :
    0 ≤ (S.phi (star a*a)).re := by rw [S.phi_star_mul]; positivity

lemma phi_faithful (S : StandardModularData H) (a : S.M.toStarSubalgebra)
    (ha : (S.phi (star a*a)).re = 0) : a = 0 := by
  apply Subtype.ext
  apply S.separating a a.property
  rw [S.phi_star_mul] at ha
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp ha)

lemma phi_star (S : StandardModularData H) (a : S.M.toStarSubalgebra) :
    S.phi (star a) = star (S.phi a) := by
  change inner ℂ S.xi ((star (a : H →L[ℂ] H)) S.xi) = star (inner ℂ S.xi ((a : H →L[ℂ] H) S.xi))
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

def commutingPairing (S : StandardModularData H) (b : S.M.commutant.toStarSubalgebra) :
    S.M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun c := inner ℂ S.xi ((b : H →L[ℂ] H) ((c : H →L[ℂ] H) S.xi))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma commutingPairing_star (S : StandardModularData H)
    (b : S.M.commutant.toStarSubalgebra) (c : S.M.toStarSubalgebra) :
    S.commutingPairing (star b) (star c) = star (S.commutingPairing b c) := by
  change inner ℂ S.xi (((star (b:H →L[ℂ] H)) * star (c:H →L[ℂ] H)) S.xi) = _
  rw [← star_mul]
  change inner ℂ S.xi (star ((c:H →L[ℂ] H)*(b:H →L[ℂ] H)) S.xi) = _
  rw [VonNeumannAlgebra.mem_commutant_iff.mp b.property c c.property]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

def modularLift (S : StandardModularData H) (r : ℝ) (b : S.M.commutant.toStarSubalgebra) :
    S.M.toStarSubalgebra :=
  ⟨Classical.choose (S.fundamental_resolvent_lift r b b.property),
    (Classical.choose_spec (S.fundamental_resolvent_lift r b b.property)).1⟩

lemma modularLift_xi (S : StandardModularData H) (r : ℝ) (b : S.M.commutant.toStarSubalgebra) :
    (S.modularLift r b : H →L[ℂ] H) S.xi = S.D.calculus (modularResolvent r) ((b:H →L[ℂ] H) S.xi) :=
  (Classical.choose_spec (S.fundamental_resolvent_lift r b b.property)).2.2

lemma eq_of_xi (S : StandardModularData H) (a c : S.M.toStarSubalgebra)
    (he : (a:H →L[ℂ] H) S.xi = (c:H →L[ℂ] H) S.xi) : a = c := by
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply S.separating (↑(a-c)) (a-c).property
  change (a:H →L[ℂ] H) S.xi - (c:H →L[ℂ] H) S.xi = 0
  exact sub_eq_zero.mpr he

lemma modularLift_add (S : StandardModularData H) (r : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.modularLift r (b+c) = S.modularLift r b + S.modularLift r c := by
  apply S.eq_of_xi
  rw [S.modularLift_xi]
  change S.D.calculus (modularResolvent r) ((b:H →L[ℂ] H) S.xi+(c:H →L[ℂ] H) S.xi) =
    (S.modularLift r b:H →L[ℂ] H) S.xi+(S.modularLift r c:H →L[ℂ] H) S.xi
  rw [map_add,S.modularLift_xi,S.modularLift_xi]

lemma modularLift_smul (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : ℂ) :
    S.modularLift r (c • b) = c • S.modularLift r b := by
  apply S.eq_of_xi
  rw [S.modularLift_xi]
  change S.D.calculus (modularResolvent r) (c • (b:H →L[ℂ] H) S.xi) =
    c • (S.modularLift r b:H →L[ℂ] H) S.xi
  rw [map_smul,S.modularLift_xi]

lemma modularLift_weakEquation (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : S.M.toStarSubalgebra) :
    (Real.exp r:ℂ) * S.phi (c*S.modularLift r b) + S.phi (S.modularLift r b*c) =
      S.commutingPairing b c := by
  let a := S.modularLift r b
  have ha : (a:H →L[ℂ] H) S.xi = S.D.calculus (modularResolvent r) ((b:H →L[ℂ] H) S.xi) :=
    S.modularLift_xi r b
  have hq : S.D.calculus (modularMixedResolvent r) ((b:H →L[ℂ] H) S.xi) =
      S.J ((star (a:H →L[ℂ] H)) S.xi) := by
    apply S.D.halfGraph_unique
    · exact S.D.modularResolvent_halfGraph r ((b:H →L[ℂ] H) S.xi)
    · rw [← ha]
      exact S.core_halfGraph a a.property
  have hc := S.core_halfGraph (star (c:H →L[ℂ] H)) (star_mem c.property)
  simp only [star_star] at hc
  have hh := S.D.halfGraph_symmetric hc
    (S.D.modularMixedResolvent_halfGraph r ((b:H →L[ℂ] H) S.xi))
  rw [hq,antiunitary_inner] at hh
  change (starRingEnd ℂ) (inner ℂ ((c:H →L[ℂ] H) S.xi) ((star (a:H →L[ℂ] H)) S.xi)) = _ at hh
  rw [inner_conj_symm, inner_sub_right, inner_smul_right, ← ha] at hh
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] at hh
  have hcomm := congrArg (fun A : H →L[ℂ] H => A S.xi)
    (VonNeumannAlgebra.mem_commutant_iff.mp b.property c c.property)
  change (c:H →L[ℂ] H) ((b:H →L[ℂ] H) S.xi) = (b:H →L[ℂ] H) ((c:H →L[ℂ] H) S.xi) at hcomm
  rw [hcomm] at hh
  change (Real.exp r:ℂ)*inner ℂ S.xi ((c:H →L[ℂ] H) ((a:H →L[ℂ] H) S.xi)) +
    inner ℂ S.xi ((a:H →L[ℂ] H) ((c:H →L[ℂ] H) S.xi)) =
      inner ℂ S.xi ((b:H →L[ℂ] H) ((c:H →L[ℂ] H) S.xi))
  linear_combination hh

lemma weakEquation_zero (S : StandardModularData H) (r : ℝ) (a : S.M.toStarSubalgebra)
    (ha : ∀ c : S.M.toStarSubalgebra,
      (Real.exp r:ℂ)*S.phi (c*a) + S.phi (a*c) = 0) : a = 0 := by
  have hh := congrArg Complex.re (ha (star a))
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re] at hh
  have hp := S.phi_nonneg a
  have hq := S.phi_nonneg (star a)
  rw [star_star] at hq
  apply S.phi_faithful
  nlinarith [Real.exp_pos r]

lemma eq_of_weakEquation (S : StandardModularData H) (r : ℝ)
    (a d : S.M.toStarSubalgebra)
    (he : ∀ c : S.M.toStarSubalgebra,
      (Real.exp r:ℂ)*S.phi (c*a) + S.phi (a*c) =
        (Real.exp r:ℂ)*S.phi (c*d) + S.phi (d*c)) : a = d := by
  apply sub_eq_zero.mp
  apply S.weakEquation_zero r
  intro c
  simp only [mul_sub, sub_mul, map_sub]
  linear_combination he c

def modularKernel (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  (Real.exp (r/2):ℂ) • S.modularLift r b

lemma modularKernel_add (S : StandardModularData H) (r : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.modularKernel r (b+c) = S.modularKernel r b + S.modularKernel r c := by
  simp only [modularKernel,modularLift_add,smul_add]

lemma modularKernel_smul (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : ℂ) :
    S.modularKernel r (c • b) = c • S.modularKernel r b := by
  unfold modularKernel
  rw [modularLift_smul]
  exact smul_comm _ _ _

lemma modularKernel_weakEquation (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : S.M.toStarSubalgebra) :
    (Real.exp r:ℂ) * S.phi (c*S.modularKernel r b) + S.phi (S.modularKernel r b*c) =
      (Real.exp (r/2):ℂ) * S.commutingPairing b c := by
  simp only [modularKernel,mul_smul_comm,smul_mul_assoc,map_smul,smul_eq_mul]
  linear_combination (Real.exp (r/2):ℂ) * S.modularLift_weakEquation r b c

lemma modularKernel_star (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    star (S.modularKernel r b) = S.modularKernel (-r) (star b) := by
  apply S.eq_of_weakEquation (-r)
  intro c
  rw [S.modularKernel_weakEquation]
  have hh := congrArg star (S.modularKernel_weakEquation r b (star c))
  simp only [star_add, star_mul, ← S.phi_star, star_star,
    ← S.commutingPairing_star] at hh
  simp only [Complex.star_def, Complex.conj_ofReal] at hh
  have he : (Real.exp (-r):ℂ)*(Real.exp r:ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have heh : (Real.exp (-r):ℂ)*(Real.exp (r/2):ℂ) = (Real.exp (-r/2):ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  linear_combination (Real.exp (-r):ℂ)*hh -
    S.phi (star (S.modularKernel r b)*c)*he + S.commutingPairing (star b) c*heh

lemma modularKernel_one (S : StandardModularData H) (r : ℝ) :
    S.modularKernel r 1 = ((Real.exp (r/2)/(Real.exp r+1):ℝ):ℂ) • 1 := by
  apply S.eq_of_weakEquation r
  intro c
  rw [S.modularKernel_weakEquation]
  have hc : S.commutingPairing 1 c = S.phi c := rfl
  rw [hc]
  simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,map_smul,smul_eq_mul]
  have hn : (Real.exp r:ℂ)+1 ≠ 0 := by exact_mod_cast (ne_of_gt (add_pos (Real.exp_pos r) zero_lt_one))
  rw [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one]
  field_simp

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

section MatrixPairing
variable {A : Type uA} {n : Type uN} [CStarAlgebra A] [Fintype n]

lemma weightedMatrixFunctional_jordan (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ)
    (X Y : CStarMatrix n n A) :
    weightedMatrixFunctional φ w (X*Y+Y*X) =
      ∑ i, ∑ j, ((w i:ℂ)*φ (X i j*Y j i)+(w j:ℂ)*φ (Y j i*X i j)) := by
  simp only [weightedMatrixFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    CStarMatrix.mul_apply, map_add, map_sum,
    Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end MatrixPairing

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
instance vonNeumannAlgebra_cstar (M : VonNeumannAlgebra H) : CStarAlgebra M.toStarSubalgebra :=
  StarSubalgebra.cstarAlgebra _ (h_closed := vonNeumannAlgebra_isClosed M)

lemma vonNeumannAlgebra_sqrt_mem (M : VonNeumannAlgebra H) {a : H →L[ℂ] H}
    (ha : a ∈ M) (hp : 0 ≤ a) : CFC.sqrt a ∈ M := by
  let _ : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumannAlgebra_isClosed M
  change CFC.sqrt a ∈ M.toStarSubalgebra
  rw [CFC.sqrt_eq_real_sqrt _ hp]
  exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt (show a ∈ M.toStarSubalgebra from ha)

lemma sqrt_factor_eq (x y : H →L[ℂ] H) (h : x ≤ y) :
    y = x+star (CFC.sqrt (y-x))*CFC.sqrt (y-x) := by
  rw [(CFC.sqrt_nonneg (y-x)).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr h)]
  abel

instance vonNeumannAlgebra_starOrdered (M : VonNeumannAlgebra H) : StarOrderedRing M.toStarSubalgebra := by
  apply StarOrderedRing.of_le_iff
  intro x y
  constructor
  · intro h
    have hp : 0 ≤ (y:H →L[ℂ] H)-(x:H →L[ℂ] H) := sub_nonneg.mpr h
    refine ⟨⟨CFC.sqrt ((y:H →L[ℂ] H)-(x:H →L[ℂ] H)),
      vonNeumannAlgebra_sqrt_mem M (sub_mem y.property x.property) hp⟩, ?_⟩
    exact Subtype.ext (sqrt_factor_eq (x:H →L[ℂ] H) (y:H →L[ℂ] H) h)
  · rintro ⟨z,rfl⟩
    change (x:H →L[ℂ] H) ≤ (x:H →L[ℂ] H)+star (z:H →L[ℂ] H)*(z:H →L[ℂ] H)
    exact le_add_of_nonneg_right (star_mul_self_nonneg _)

namespace StandardModularData

lemma commuting_apply (S : StandardModularData H)
    (b : S.M.commutant.toStarSubalgebra) (a : S.M.toStarSubalgebra) (h : H) :
    (b:H →L[ℂ] H) ((a:H →L[ℂ] H) h) = (a:H →L[ℂ] H) ((b:H →L[ℂ] H) h) :=
  (congrArg (fun A : H →L[ℂ] H => A h)
    (VonNeumannAlgebra.mem_commutant_iff.mp b.property a a.property)).symm

lemma commutingPairing_gram (S : StandardModularData H)
    (b d : S.M.commutant.toStarSubalgebra) (a c : S.M.toStarSubalgebra) :
    S.commutingPairing (star d*b) (star c*a) =
      inner ℂ ((d:H →L[ℂ] H) ((c:H →L[ℂ] H) S.xi))
        ((b:H →L[ℂ] H) ((a:H →L[ℂ] H) S.xi)) := by
  change inner ℂ S.xi ((star (d:H →L[ℂ] H))
    ((b:H →L[ℂ] H) ((star (c:H →L[ℂ] H)) ((a:H →L[ℂ] H) S.xi)))) = _
  change inner ℂ S.xi ((↑(star d):H →L[ℂ] H)
    ((b:H →L[ℂ] H) ((↑(star c):H →L[ℂ] H) ((a:H →L[ℂ] H) S.xi)))) = _
  rw [S.commuting_apply b (star c), S.commuting_apply (star d) (star c)]
  change inner ℂ S.xi ((star (c:H →L[ℂ] H))
    ((star (d:H →L[ℂ] H)) ((b:H →L[ℂ] H) ((a:H →L[ℂ] H) S.xi)))) = _
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

def modularGram {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) : CStarMatrix n n S.M.toStarSubalgebra :=
  CStarMatrix.ofMatrix (fun i j => S.modularKernel (r i-r j) (star (b j)*b i))

@[simp] lemma modularGram_apply {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) (i j : n) :
    S.modularGram r b i j = S.modularKernel (r i-r j) (star (b j)*b i) := rfl

lemma modularGram_selfAdjoint {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) : IsSelfAdjoint (S.modularGram r b) := by
  apply CStarMatrix.ext
  intro i j
  change star (S.modularKernel (r j-r i) (star (b i)*b j)) = _
  rw [S.modularKernel_star,star_mul,star_star,neg_sub]
  rfl

lemma modularGram_equation {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) (i j : n) (c : S.M.toStarSubalgebra) :
    (Real.exp (-r i):ℂ)*S.phi (S.modularGram r b i j*c) +
      (Real.exp (-r j):ℂ)*S.phi (c*S.modularGram r b i j) =
    (Real.exp (-r i/2):ℂ)*(Real.exp (-r j/2):ℂ) *
      S.commutingPairing (star (b j)*b i) c := by
  have he : (Real.exp (-r i):ℂ)*(Real.exp (r i-r j):ℂ) = (Real.exp (-r j):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  have heh : (Real.exp (-r i):ℂ)*(Real.exp ((r i-r j)/2):ℂ) =
      (Real.exp (-r i/2):ℂ)*(Real.exp (-r j/2):ℂ) := by
    rw [← Complex.ofReal_mul,← Complex.ofReal_mul,← Real.exp_add,← Real.exp_add]
    congr 2
    ring
  change (Real.exp (-r i):ℂ)*S.phi (S.modularKernel (r i-r j) (star (b j)*b i)*c) +
    (Real.exp (-r j):ℂ)*S.phi (c*S.modularKernel (r i-r j) (star (b j)*b i)) = _
  linear_combination (Real.exp (-r i):ℂ)*S.modularKernel_weakEquation (r i-r j) (star (b j)*b i) c -
    S.phi (c*S.modularKernel (r i-r j) (star (b j)*b i))*he +
    S.commutingPairing (star (b j)*b i) c*heh

lemma modularGram_pairing {n : Type uN} [Fintype n] (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) (Z : CStarMatrix n n S.M.toStarSubalgebra) :
    weightedMatrixFunctional S.phi (fun i => Real.exp (-r i))
      (S.modularGram r b*(star Z*Z)+(star Z*Z)*S.modularGram r b) =
    ∑ k, inner ℂ (∑ i, (Real.exp (-r i/2):ℂ) • (b i:H →L[ℂ] H) ((Z k i:H →L[ℂ] H) S.xi))
      (∑ i, (Real.exp (-r i/2):ℂ) • (b i:H →L[ℂ] H) ((Z k i:H →L[ℂ] H) S.xi)) := by
  rw [weightedMatrixFunctional_jordan]
  simp only [S.modularGram_equation]
  simp only [CStarMatrix.mul_apply,CStarMatrix.star_eq_conjTranspose,
    CStarMatrix.conjTranspose_apply,map_sum,Finset.mul_sum,S.commutingPairing_gram]
  simp only [inner_sum, sum_inner, inner_smul_left,inner_smul_right,
    Complex.conj_ofReal,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma modularGram_nonneg {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ) (b : n → S.M.commutant.toStarSubalgebra) :
    0 ≤ S.modularGram r b := by
  apply nonneg_of_jordan_pairing (weightedMatrixFunctional S.phi (fun i => Real.exp (-r i)))
    (weightedMatrixFunctional_nonneg S.phi _ (fun i => (Real.exp_pos _).le) S.phi_nonneg)
    (weightedMatrixFunctional_faithful S.phi _ (fun i => Real.exp_pos _) S.phi_nonneg S.phi_faithful)
    _ (S.modularGram_selfAdjoint r b)
  intro Y hY
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix n n S.M.toStarSubalgebra) IsSelfAdjoint :=
    (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
      (A := CStarMatrix n n S.M.toStarSubalgebra)).toNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix n n S.M.toStarSubalgebra) :=
    CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨Z, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY
  rw [S.modularGram_pairing]
  simp only [Complex.re_sum]
  exact Finset.sum_nonneg (fun k _ => @inner_self_nonneg ℂ H _ _ _ _)

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

section MatrixNorm
variable {A : Type uA} {m : Type uM} {n : Type uN} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Fintype m] [Fintype n]
open CStarMatrix WithCStarModule
lemma cstarMatrix_norm_le_sum (M : CStarMatrix m n A) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum, Finset.sum_mul]
  apply pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v j
end MatrixNorm

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vonNeumannAlgebra_realCFC (M : VonNeumannAlgebra H) :
    NonUnitalContinuousFunctionalCalculus ℝ M.toStarSubalgebra IsSelfAdjoint :=
  (IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
    (A := M.toStarSubalgebra)).toNonUnitalContinuousFunctionalCalculus

instance vonNeumannAlgebra_nonnegSpectrum (M : VonNeumannAlgebra H) :
    NonnegSpectrumClass ℝ M.toStarSubalgebra := CStarAlgebra.instNonnegSpectrumClass'

def kernelScalar (r : ℝ) : ℝ := Real.exp (r/2)/(Real.exp r+1)

lemma kernelScalar_pos (r : ℝ) : 0 < kernelScalar r := by unfold kernelScalar; positivity
lemma kernelScalar_le (r : ℝ) : kernelScalar r ≤ 1/2 := by
  unfold kernelScalar
  rw [div_le_iff₀ (by positivity)]
  have he : Real.exp r = Real.exp (r/2)^2 := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [he]
  nlinarith [sq_nonneg (Real.exp (r/2)-1)]

namespace StandardModularData

def kernelMatrix {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : S.M.commutant.toStarSubalgebra) : CStarMatrix n n S.M.toStarSubalgebra :=
  CStarMatrix.ofMatrix (fun i j => S.modularKernel (r i-r j) b)

@[simp] lemma kernelMatrix_apply {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : S.M.commutant.toStarSubalgebra) (i j : n) :
    S.kernelMatrix r b i j = S.modularKernel (r i-r j) b := rfl

lemma kernelMatrix_nonneg {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ)
    (b : S.M.commutant.toStarSubalgebra) (hb : 0 ≤ b) : 0 ≤ S.kernelMatrix r b := by
  obtain ⟨d, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
  exact S.modularGram_nonneg r (fun _ => d)

lemma kernelMatrix_add {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.kernelMatrix r (b+c) = S.kernelMatrix r b+S.kernelMatrix r c := by
  apply CStarMatrix.ext
  intro i j
  exact S.modularKernel_add _ b c

lemma kernelMatrix_smul {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : ℂ) :
    S.kernelMatrix r (c • b) = c • S.kernelMatrix r b := by
  apply CStarMatrix.ext
  intro i j
  exact S.modularKernel_smul _ b c

lemma kernelMatrix_mono {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ)
    {b c : S.M.commutant.toStarSubalgebra} (hbc : b ≤ c) :
    S.kernelMatrix r b ≤ S.kernelMatrix r c := by
  have he : S.kernelMatrix r (c-b)+S.kernelMatrix r b = S.kernelMatrix r c := by
    rw [← S.kernelMatrix_add, sub_add_cancel]
  exact he ▸ le_add_of_nonneg_left (S.kernelMatrix_nonneg r _ (sub_nonneg.mpr hbc))

lemma modularKernel_one' (S : StandardModularData H) (r : ℝ) :
    S.modularKernel r 1 = (kernelScalar r:ℂ) • 1 := by
  rw [S.modularKernel_one]
  simp only [kernelScalar, Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one]

lemma norm_kernelMatrix_one_le {n : Type uN} [Fintype n] [DecidableEq n]
    (S : StandardModularData H) (r : n → ℝ) :
    ‖S.kernelMatrix r 1‖ ≤ (Fintype.card n:ℝ)^2/2 := by
  apply (cstarMatrix_norm_le_sum _).trans
  calc
    (∑ j, ∑ i, ‖S.kernelMatrix r 1 i j‖) ≤ ∑ _j : n, ∑ _i : n, (1/2:ℝ) := by
      gcongr with j _ i _
      rw [S.kernelMatrix_apply,S.modularKernel_one',norm_smul,Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (kernelScalar_pos _)]
      exact (mul_le_of_le_one_right (kernelScalar_pos _).le ContinuousLinearMap.norm_id_le).trans (kernelScalar_le _)
    _ = _ := by simp; ring

lemma norm_modularKernel_of_nonneg (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (hb : 0 ≤ b) :
    ‖S.modularKernel r b‖ ≤ 2*‖b‖ := by
  let rs : Fin 2 → ℝ := ![r,0]
  have heq : algebraMap ℝ S.M.commutant.toStarSubalgebra ‖b‖ =
      (‖b‖:ℂ) • (1:S.M.commutant.toStarSubalgebra) := by
    apply Subtype.ext
    ext h
    simp [Algebra.algebraMap_eq_smul_one]
  have hle : b ≤ (‖b‖:ℂ) • (1:S.M.commutant.toStarSubalgebra) := by
    rw [← heq]
    exact hb.isSelfAdjoint.le_algebraMap_norm_self
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg (S.kernelMatrix_mono rs hle)
    (S.kernelMatrix_nonneg rs b hb)
  have he : ‖S.modularKernel r b‖ ≤ ‖S.kernelMatrix rs b‖ := by
    simpa only [kernelMatrix_apply,rs,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
      sub_zero] using (CStarMatrix.norm_entry_le_norm (M := S.kernelMatrix rs b) (i := 0) (j := 1))
  refine he.trans (hn.trans ?_)
  rw [S.kernelMatrix_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
  have hk := S.norm_kernelMatrix_one_le rs
  norm_num at hk
  nlinarith [norm_nonneg b]

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI


