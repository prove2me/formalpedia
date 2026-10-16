-- Prove2me | Definitions.Def_OAI_Analysis_QuantumTrace_Basic
-- name    : OAI_Analysis_QuantumTrace_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:00:53.385318+00:00
-- url     : https://prove2.me/theorems/e7b62733-cb24-4da5-9a54-9c64750fda31
-- title:
--   Diagonal operators, Gibbs weights and Parseval identities for operator sandwiches on $\ell^2$ spaces
-- statement:
--   This file collects Hilbert-space tools used to compute traces and entropies of quantum states on sequence spaces: diagonal operators in a given orthonormal basis, thermal and Gibbs weight distributions, and Parseval-type identities for quadratic forms of operators of the shape $A + cX^2$.
--
--   Throughout, $E$ is a complex Hilbert space, $(b_i)_{i\in\iota}$ is a Hilbert basis (complete orthonormal family) of $E$, and $\ell^2(\iota)$ is the Hilbert space of square-summable complex families with standard basis $(e_i)$. Sums $\sum$ denote unconditional sums.
--
--   1. **Basis traces and quadratic forms.** The diagonal trace of a bounded operator $T$ is $\operatorname{tr}_b T = \sum_i \max(\operatorname{Re}\langle b_i, T b_i\rangle, 0) \in [0,\infty]$. Parseval's identity $\sum_i |\langle b_i,x\rangle|^2 = \|x\|^2$ holds, and for a positive operator $T$, $\operatorname{Re}\langle x,Tx\rangle = \|\sqrt{T}\,x\|^2$. If $T b_j = p_j b_j$ with real $p_j$, then
--   $$
--   \sum_j p_j\,|\langle b_j, x\rangle|^2 = \operatorname{Re}\langle x, T x\rangle \qquad (x \in E),
--   $$
--   the series converging. The finite-rank truncation $T_S = \sum_{i \in S} |T b_i\rangle\langle b_i|$ for a finite set $S$ sends $b_j$ to $T b_j$ if $j\in S$ and to $0$ otherwise. The entropy operator of $T$ is $-T\log T$, defined by continuous functional calculus with the function $t\mapsto -t\log t$.
--
--   2. **Thermal weights.** For weights $w:\mathbb{N}\to[0,\infty]$ one has $\sum_{k\in\mathbb{N}^n}\prod_j w(k_j) = (\sum_m w(m))^n$. For $r>0$ the $n$-mode thermal weight $\tau_r(k) = \prod_{j=1}^n \frac{1}{r+1}\bigl(\frac{r}{r+1}\bigr)^{k_j}$ is positive for every $k\in\mathbb{N}^n$ and $\sum_{k} \tau_r(k) = 1$.
--
--   3. **Diagonal operators on $\ell^2(\iota)$.** For a bounded family $a:\iota\to\mathbb{C}$, the multiplication operator $D_a x = (a_i x_i)_i$ is bounded and $D_a e_i$ is $a_i e_i$; for real $a$ it is symmetric and for nonnegative real $a$ it is positive. One has $\langle e_i, x\rangle = x_i$ and $\sum_i |x_i|^2 = \|x\|^2$. More generally, for real bounded $p$ the operator diagonal in the basis $b$ is $b_i \mapsto p_i b_i$.
--
--   4. **Inverse powers and the Gibbs factor.** For $s:\iota\to\mathbb{R}$ with all $s_i \ge 1$ and $p\in\mathbb{N}$, $S^{-p}$ is the diagonal operator with entries $s_i^{-p}$; it is positive and self-adjoint, and $S^{0}=1$. For $k\in\mathbb{R}$ and a bounded operator $B$ define
--   $$
--   G_k(B) = k\cdot 1 + S^{-3} B\, S^{-3}, \qquad G_k(B)^{\sharp} = S^{-4}\,G_k(B)^{-1}\,S^{-4},
--   $$
--   and if $k>0$ and $B$ is positive, then $G_k(B)$ is strictly positive (a positive invertible operator). The number weights on $\mathbb{N}^n$ are $\nu(i) = 1+\sum_j i_j \ge 1$ and $\sqrt{\nu(i)} \ge 1$, with $\sqrt{\nu(i)}^{\,4} = \nu(i)^2$.
--
--   5. **Gibbs weights.** For $u:\iota\to\mathbb{R}$ put $Z(u)=\sum_i e^{-u_i}$ and $\gamma_u(i) = e^{-u_i}/Z(u)$. If $\iota$ is nonempty and $\sum_i e^{-u_i}$ converges, then $Z(u)>0$, every $\gamma_u(i)$ lies in $(0,1]$, $\sum_i\gamma_u(i) = 1$, and $-\log\gamma_u(i) = u_i + \log Z(u)$. The spectral Gibbs operator is the operator diagonal in $b$ with eigenvalues $\gamma_u(i)$.
--
--   6. **Polar eigenbasis and sandwich identities.** If $M$ is bounded, $M^*$ is injective, $u_j>0$ and $M^*M b_j = u_j^{-1} b_j$ for all $j$, then $(\sqrt{u_j}\,M b_j)_j$ is again a Hilbert basis. Consequently, let $A$ be strictly positive, $X$ symmetric and injective, $u_j > 0$, and suppose $(X A^{-1} X) b_j = u_j^{-1} b_j$ for all $j$. Then for every $y\in E$ and $c \in \mathbb{R}$
--   $$
--   \sum_j (u_j + c)\,|\langle b_j, X y\rangle|^2 = \operatorname{Re}\bigl\langle y, (A + cX^2)\,y\bigr\rangle ,
--   $$
--   the case $c=0$ reading $\sum_j u_j|\langle b_j,Xy\rangle|^2 = \operatorname{Re}\langle y,Ay\rangle$. If moreover the index set is nonempty and $\sum_j e^{-u_j}$ converges, then $\sum_j (-\log\gamma_u(j))\,|\langle b_j,Xy\rangle|^2 = \operatorname{Re}\langle y,(A+\log Z(u)\,X^2)y\rangle$. Under the same eigen-relation (without completeness or symmetry of $X$), if $Xv = t\,b_j$ then $Av = u_j\,X(t b_j)$ and $(A+cX^2)v = (u_j+c)\,X(t b_j)$.
--
--   7. **Weighted spectral vectors.** Let $T$ act on $\ell^2(\iota)$ with a Hilbert basis $(b_j)$ of eigenvectors, $T b_j = p_j b_j$, $p_j \ge 0$, and let $w:\iota\to\mathbb{R}$ satisfy $\sum_i w_i^2\operatorname{Re}\langle e_i,Te_i\rangle<\infty$ (summable). Then the families $y_j = (w_i\sqrt{p_j}\,b_j(i))_i$ lie in $\ell^2(\iota)$, $\sum_j\|y_j\|^2$ converges, and $\sum_j \|y_j\|^2 = \sum_i w_i^2\operatorname{Re}\langle e_i,Te_i\rangle$.
--
--   These identities express weighted traces and relative-entropy-type quantities of a state as sums over an eigenbasis; the sandwich identity of item 6 is the tool for evaluating $\operatorname{Re}\langle y,(A+cX^2)y\rangle$ when $X A^{-1}X$ has known spectrum.
--
--   **Formalization Note** The inverse in $G_k(B)^{\sharp}$ and in item 6 is `Ring.inverse`, which equals the true inverse for units and is $0$ otherwise; strict positivity (`IsStrictlyPositive`) supplies invertibility. `diagonalMap` takes the boundedness witness as an argument and uses a chosen bound. `diagonalTrace` uses `ENNReal.ofReal`, so negative real parts contribute $0$. Sums are `HasSum`/`tsum` over arbitrary index types. Two private `if`-rewriting lemmas are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam

-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

def diagonalTrace (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (inner ℂ (b i) (T (b i))).re

omit [CompleteSpace E] in
theorem basis_hasSum_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (b.hasSum_inner_mul_inner x x).mapL Complex.reCLM
  convert! h using 1
  · ext i
    simp only [Complex.reCLM_apply]
    conv_rhs => rw [← inner_conj_symm x (b i), Complex.conj_mul']
    simp [← Complex.ofReal_pow]
  · simp [← Complex.ofReal_pow]

theorem sqrt_inner_eq {T : E →L[ℂ] E} (hT : T.IsPositive) (x : E) :
    (inner ℂ x (T x)).re = ‖CFC.sqrt T x‖ ^ 2 := by
  have hn : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hT
  have hs : (CFC.sqrt T).IsSymmetric :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)).isSymmetric
  have he : CFC.sqrt T (CFC.sqrt T x) = T x := by
    simpa [pow_two] using congrArg (fun A : E →L[ℂ] E => A x) (CFC.sq_sqrt T hn)
  have hr : inner ℂ x (CFC.sqrt T (CFC.sqrt T x)) =
      inner ℂ (CFC.sqrt T x) (CFC.sqrt T x) := by
    exact (hs x (CFC.sqrt T x)).symm
  rw [← he, hr]
  simp [← Complex.ofReal_pow]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

def basisApprox (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F) (s : Finset ι) : E →L[ℂ] F :=
  ∑ i ∈ s, rankOne ℂ (T (b i)) (b i)

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisApprox_apply_basis (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (s : Finset ι) (j : ι) [Decidable (j ∈ s)] : basisApprox b T s (b j) = if j ∈ s then T (b j) else 0 := by
  classical
  simp only [basisApprox, sum_apply, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]
  simp

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def entropyOperator (T : E →L[ℂ] E) : E →L[ℂ] E := cfc Real.negMulLog T

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

omit [CompleteSpace E] in

theorem hasSum_quadratic_eigenbasis (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (p : ι → ℝ) (he : ∀ j, T (b j) = (p j : ℂ) • b j) (x : E) :
    HasSum (fun j => p j * ‖inner ℂ (b j) x‖ ^ 2) (inner ℂ x (T x)).re := by
  have hh := ((T.hasSum (b.hasSum_repr x)).mapL (innerSL ℂ x)).mapL Complex.reCLM
  convert! hh using 1
  ext j
  simp only [Complex.reCLM_apply, innerSL_apply_apply, b.repr_apply_apply,
    ContinuousLinearMap.map_smul, he, smul_eq_mul]
  rw [← inner_conj_symm x (b j)]
  have hn := Complex.mul_conj (inner ℂ (b j) x)
  rw [← mul_assoc, mul_right_comm, hn]
  simp [Complex.normSq_eq_norm_sq, -Complex.ofReal_pow, mul_comm]

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

theorem tsum_finite_product (n : ℕ) (w : ℕ → ℝ≥0∞) :
    (∑' k : Fin n → ℕ, ∏ j, w (k j)) = (∑' m, w m) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod' ]
    simp only [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right, pow_succ']

def thermalWeight (n : ℕ) (r : ℝ) (k : Fin n → ℕ) : ℝ :=
  ∏ j, ((r + 1)⁻¹ * (r / (r + 1)) ^ (k j))

theorem thermalWeight_pos (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n → ℕ) :
    0 < thermalWeight n r k := by
  apply Finset.prod_pos
  intro j _
  positivity

theorem hasSum_thermalWeight (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasSum (thermalWeight n r) 1 := by
  have hr1 : 0 < r + 1 := by linarith
  have hz : r / (r + 1) < 1 := (div_lt_one hr1).mpr (by linarith)
  have hw : HasSum (fun m : ℕ => (r + 1)⁻¹ * (r / (r + 1)) ^ m) 1 := by
    convert! (hasSum_geometric_of_lt_one (div_nonneg hr.le hr1.le) hz).mul_left (r + 1)⁻¹ using 1
    field_simp
    ring
  have he : (∑' m : ℕ, ENNReal.ofReal ((r + 1)⁻¹ * (r / (r + 1)) ^ m)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hw.summable, hw.tsum_eq]
    simp
  have ht : (∑' k : Fin n → ℕ, ENNReal.ofReal (thermalWeight n r k)) = 1 := by
    calc
      _ = ∑' k : Fin n → ℕ, ∏ j, ENNReal.ofReal ((r + 1)⁻¹ * (r / (r + 1)) ^ k j) := by
        congr 1; ext k
        exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)
      _ = 1 := by rw [tsum_finite_product n (fun m => ENNReal.ofReal ((r + 1)⁻¹ * (r / (r + 1)) ^ m)), he, one_pow]
  have hf : (∑' k : Fin n → ℕ, ENNReal.ofReal (thermalWeight n r k)) ≠ ⊤ := by
    rw [ht]; exact ENNReal.one_ne_top
  have hs := ENNReal.hasSum_toReal hf
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), ht] at hs
  simpa only [ENNReal.toReal_ofReal (thermalWeight_pos n hr _).le, ENNReal.toReal_one] using hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
abbrev SequenceHilbert (ι : Type*) : Type _ := ↥(lp (fun _ : ι => ℂ) 2)

def diagonalMap (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) :
    SequenceHilbert ι →L[ℂ] SequenceHilbert ι := by
  let C := |ha.choose|
  have hC : 0 ≤ C := abs_nonneg _
  have hab (i : ι) : ‖a i‖ ≤ C := (ha.choose_spec i).trans (le_abs_self _)
  let f : SequenceHilbert ι →ₗ[ℂ] SequenceHilbert ι :=
    { toFun := fun x => ⟨fun i => a i*x i, ((lp.memℓp x).norm.const_mul C).mono (by
        intro i
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hab i) (norm_nonneg _))⟩
      map_add' := by intro x y; ext i; exact mul_add _ _ _
      map_smul' := by intro c x; ext i; exact mul_left_comm _ _ _ }
  refine f.mkContinuous C (fun x => ?_)
  have h := lp.norm_mono (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (x := f x) (y := (C : ℂ) • x) (fun i => by
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hab i) (norm_nonneg _))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h

@[simp] theorem diagonalMap_apply (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (x : SequenceHilbert ι) (i : ι) : diagonalMap a ha x i = a i*x i := rfl

theorem diagonalMap_single [DecidableEq ι] (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (i : ι) (z : ℂ) : diagonalMap a ha (lp.single 2 i z) = lp.single 2 i (a i*z) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem diagonalMap_symmetric (a : ι → ℝ) (ha : ∃ C : ℝ, ∀ i, ‖(a i : ℂ)‖ ≤ C) :
    (diagonalMap (fun i => (a i : ℂ)) ha).IsSymmetric := by
  intro x y
  change (∑' i, inner ℂ (((a i : ℂ)*x i)) (y i)) =
    ∑' i, inner ℂ (x i) ((a i : ℂ)*y i)
  congr 1
  funext i
  change inner ℂ ((a i : ℂ) • x i) (y i) = inner ℂ (x i) ((a i : ℂ) • y i)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem diagonalMap_positive (a : ι → ℝ) (ha : ∃ C : ℝ, ∀ i, ‖(a i : ℂ)‖ ≤ C)
    (hp : ∀ i, 0 ≤ a i) : (diagonalMap (fun i => (a i : ℂ)) ha).IsPositive := by
  refine ⟨diagonalMap_symmetric a ha, ?_⟩
  intro x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  have hsym : inner ℂ (diagonalMap (fun i => (a i : ℂ)) ha x) x =
      inner ℂ x (diagonalMap (fun i => (a i : ℂ)) ha x) := diagonalMap_symmetric a ha x x
  rw [hsym]
  change 0 ≤ (∑' i, inner ℂ (x i) ((a i : ℂ)*x i)).re
  have ht : Summable (fun i => inner ℂ (x i) ((a i : ℂ)*x i)) := by
    simpa only [diagonalMap_apply] using lp.summable_inner x (diagonalMap (fun i => (a i : ℂ)) ha x)
  rw [Complex.re_tsum ht]
  apply tsum_nonneg
  intro i
  have he : (inner ℂ (x i) ((a i : ℂ)*x i)).re = a i*‖x i‖^2 := by
    rw [show (a i : ℂ)*x i = (a i : ℂ) • x i from rfl, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [he]
  exact mul_nonneg (hp i) (sq_nonneg _)

end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

def sequenceBasis (ι : Type*) : HilbertBasis ι ℂ (SequenceHilbert ι) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem sequenceBasis_apply (i : ι) : sequenceBasis ι i = lp.single 2 i 1 := rfl

end

section
open Filter Topology
variable {ι : Type*}

theorem inversePower_bounded (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    ∃ C : ℝ, ∀ i, ‖(((s i^p)⁻¹ : ℝ) : ℂ)‖ ≤ C := by
  refine ⟨1, fun i => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [hs i])]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (hs i))

def inversePower (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    SequenceHilbert ι →L[ℂ] SequenceHilbert ι :=
  diagonalMap (fun i => (((s i^p)⁻¹ : ℝ) : ℂ)) (inversePower_bounded s hs p)

@[simp] theorem inversePower_apply (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ)
    (x : SequenceHilbert ι) (i : ι) : inversePower s hs p x i = ((s i^p)⁻¹ : ℝ)*x i := rfl

theorem inversePower_positive (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    (inversePower s hs p).IsPositive := by
  exact diagonalMap_positive _ _ (fun i => inv_nonneg.mpr (pow_nonneg (by linarith [hs i]) _))

theorem inversePower_adjoint (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    (inversePower s hs p).adjoint = inversePower s hs p :=
  (inversePower_positive s hs p).isSelfAdjoint

@[simp] theorem inversePower_zero (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) :
    inversePower s hs 0 = 1 := by
  ext x i
  simp

def gibbsFactor (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (k : ℝ)
    (B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) :
    SequenceHilbert ι →L[ℂ] SequenceHilbert ι :=
  k • (1 : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) +
    inversePower s hs 3 * B * inversePower s hs 3

theorem gibbsFactor_strictPositive (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k : ℝ} (hk : 0 < k) {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι}
    (hB : B.IsPositive) : IsStrictlyPositive (gibbsFactor s hs k B) := by
  have hpos := hB.adjoint_conj (inversePower s hs 3)
  rw [inversePower_adjoint] at hpos
  have hb : 0 ≤ inversePower s hs 3 * B * inversePower s hs 3 :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hpos
  have hsc : IsStrictlyPositive (k • (1 : SequenceHilbert ι →L[ℂ] SequenceHilbert ι)) := by
    apply IsStrictlyPositive.iff_of_unital.mpr
    constructor
    · apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      have he : k • (1 : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) =
          diagonalMap (fun _ : ι => (k : ℂ)) ⟨|k|, fun _ => by simp⟩ := by
        ext x i
        simp
      rw [he]
      exact diagonalMap_positive _ _ (fun _ => hk.le)
    · change IsUnit (algebraMap ℝ (SequenceHilbert ι →L[ℂ] SequenceHilbert ι) k)
      exact (isUnit_iff_ne_zero.mpr hk.ne').map _
  exact hsc.add_nonneg hb

def gibbsInverse (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (k : ℝ)
    (B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) :
    SequenceHilbert ι →L[ℂ] SequenceHilbert ι :=
  inversePower s hs 4 * Ring.inverse (gibbsFactor s hs k B) * inversePower s hs 4

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

@[simp] theorem sequenceBasis_inner (i : ι) (x : SequenceHilbert ι) :
    inner ℂ (sequenceBasis ι i) x = x i := by
  classical
  rw [sequenceBasis_apply, lp.inner_single_left]
  simp

theorem sequence_hasSum_norm_sq (x : SequenceHilbert ι) :
    HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [sequenceBasis_inner] using basis_hasSum_norm_sq (sequenceBasis ι) x

end

section
open Filter Topology

def numberWeight {n : ℕ} (i : Fin n → ℕ) : ℝ := 1+∑ j, (i j : ℝ)

def rootNumberWeight {n : ℕ} (i : Fin n → ℕ) : ℝ := Real.sqrt (numberWeight i)

theorem numberWeight_one_le {n : ℕ} (i : Fin n → ℕ) : 1 ≤ numberWeight i := by
  unfold numberWeight
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem rootNumberWeight_one_le {n : ℕ} (i : Fin n → ℕ) : 1 ≤ rootNumberWeight i := by
  exact (Real.le_sqrt (by norm_num) (by linarith [numberWeight_one_le i])).mpr (by
    simpa only [one_pow] using numberWeight_one_le i)

theorem rootNumberWeight_pow_four {n : ℕ} (i : Fin n → ℕ) :
    rootNumberWeight i^4 = numberWeight i^2 := by
  rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, rootNumberWeight, Real.sq_sqrt (by linarith [numberWeight_one_le i])]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

def basisDiagonal (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) : E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((diagonalMap (fun i => (p i : ℂ)) hb).comp
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem basisDiagonal_eigen (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) (i : ι) :
    basisDiagonal b p hb (b i) = (p i : ℂ) • b i := by
  classical
  change b.repr.symm (diagonalMap _ hb (b.repr (b i))) = _
  rw [b.repr_self, diagonalMap_single, mul_one]
  have he : (lp.single 2 i (p i : ℂ) : SequenceHilbert ι) = (p i : ℂ) • (lp.single 2 i (1 : ℂ) : SequenceHilbert ι) := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : ι => ℂ) 2 i (p i : ℂ) (1 : ℂ))
  rw [he, map_smul, b.repr_symm_single]

def heatPartition (u : ι → ℝ) : ℝ := ∑' i, Real.exp (-u i)

def gibbsWeight (u : ι → ℝ) (i : ι) : ℝ := Real.exp (-u i) / heatPartition u

theorem heatPartition_pos [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) :
    0 < heatPartition u := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact hs.tsum_pos (fun _ => Real.exp_nonneg _) i (Real.exp_pos _)

theorem gibbsWeight_pos [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) (i : ι) :
    0 < gibbsWeight u i := div_pos (Real.exp_pos _) (heatPartition_pos u hs)

theorem gibbsWeight_hasSum [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) :
    HasSum (gibbsWeight u) 1 := by
  have hh := hs.hasSum.div_const (heatPartition u)
  change HasSum (gibbsWeight u) (heatPartition u / heatPartition u) at hh
  rwa [div_self (heatPartition_pos u hs).ne'] at hh

theorem gibbsWeight_bounded [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) :
    ∃ C : ℝ, ∀ i, ‖(gibbsWeight u i : ℂ)‖ ≤ C := by
  refine ⟨1, fun i => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gibbsWeight_pos u hs i)]
  have hh := (gibbsWeight_hasSum u hs).summable.le_tsum i (fun j _ => (gibbsWeight_pos u hs j).le)
  rwa [(gibbsWeight_hasSum u hs).tsum_eq] at hh

def spectralGibbs [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) : E →L[ℂ] E :=
  basisDiagonal b (gibbsWeight u) (gibbsWeight_bounded u hs)

theorem spectralGibbs_eigen [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) (i : ι) :
    spectralGibbs b u hs (b i) = (gibbsWeight u i : ℂ) • b i :=
  basisDiagonal_eigen b _ _ i

theorem log_gibbsWeight [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) (i : ι) :
    -Real.log (gibbsWeight u i) = u i + Real.log (heatPartition u) := by
  rw [gibbsWeight, Real.log_div (Real.exp_ne_zero _) (heatPartition_pos u hs).ne', Real.log_exp]
  ring

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

theorem polar_eigenbasis (b : HilbertBasis J ℂ E) (M : E →L[ℂ] E)
    (hi : Function.Injective M.adjoint) (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, M.adjoint (M (b j)) = (((u j)⁻¹ : ℝ) : ℂ) • b j) :
    ∃ c : HilbertBasis J ℂ E, ∀ j, c j = (Real.sqrt (u j) : ℂ) • M (b j) := by
  classical
  let v : J → E := fun j => (Real.sqrt (u j) : ℂ) • M (b j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [v, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [← ContinuousLinearMap.adjoint_inner_right, he, inner_smul_right]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
      have hs := Real.sq_sqrt (hu i).le
      calc
        _ = ((Real.sqrt (u i)^2*(u i)⁻¹ : ℝ) : ℂ) := by push_cast; ring
        _ = 1 := by rw [hs, mul_inv_cancel₀ (hu i).ne']; norm_num
    · rw [ite_eq_right hij, b.orthonormal.inner_eq_zero hij]
      simp
  have hc : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply hi
    rw [map_zero]
    apply b.repr.injective
    apply lp.ext
    funext j
    rw [map_zero]
    rw [b.repr_apply_apply]
    change inner ℂ (b j) (M.adjoint x) = 0
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hh := (Submodule.mem_orthogonal _ x).mp hx (v j) (Submodule.subset_span ⟨j, rfl⟩)
    change inner ℂ ((Real.sqrt (u j) : ℂ) • M (b j)) x = 0 at hh
    rw [inner_smul_left, Complex.conj_ofReal] at hh
    exact (mul_eq_zero.mp hh).resolve_left (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hu j)).ne')
  exact ⟨HilbertBasis.mkOfOrthogonalEqBot hv hc, fun j => by
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]⟩

theorem inverse_factor_form_parseval (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hX : X.IsSymmetric)
    (hiX : Function.Injective X) (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (y : E) :
    HasSum (fun j => u j*‖inner ℂ (b j) (X y)‖^2) (inner ℂ y (A y)).re := by
  let S := CFC.sqrt A
  have hSpos : S.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg A)
  have hSu : IsUnit S := (CFC.isUnit_sqrt_iff A hA.nonneg).mpr hA.isUnit
  have hSq : S*S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  let R := Ring.inverse S
  have hRS : R*S = 1 := Ring.inverse_mul_cancel S hSu
  have hSR : S*R = 1 := Ring.mul_inverse_cancel S hSu
  have hRa : R.adjoint = R := hSpos.isSelfAdjoint.ringInverse
  have hXa : X.adjoint = X := hX.isSelfAdjoint
  have hRR : R*R = Ring.inverse A := by
    apply hA.isUnit.mul_left_cancel
    rw [Ring.mul_inverse_cancel A hA.isUnit, ← hSq]
    calc
      S*S*(R*R) = S*(S*R)*R := by noncomm_ring
      _ = 1 := by rw [hSR, mul_one, hSR]
  let M := R*X
  have hMa : M.adjoint = X*R := by
    change star (R*X) = X*R
    rw [star_mul]
    change X.adjoint*R.adjoint = X*R
    rw [hRa, hXa]
  have hiR : Function.Injective R := by
    intro x y h
    have hh := congrArg S h
    simpa only [← mul_apply_eq_comp, hSR, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply] using hh
  have hiM : Function.Injective M.adjoint := by
    rw [hMa]
    exact hiX.comp hiR
  have hMM : M.adjoint*M = X*Ring.inverse A*X := by
    rw [hMa]
    dsimp [M]
    calc
      X*R*(R*X) = X*(R*R)*X := by noncomm_ring
      _ = _ := by rw [hRR]
  obtain ⟨c, hc⟩ := polar_eigenbasis b M hiM u hu (fun j => by
    simpa only [← mul_apply_eq_comp, hMM] using he j)
  have hcoeff (j : J) : inner ℂ (c j) (S y) =
      (Real.sqrt (u j) : ℂ)*inner ℂ (b j) (X y) := by
    rw [hc, inner_smul_left, Complex.conj_ofReal, ← ContinuousLinearMap.adjoint_inner_right, hMa]
    congr 1
    rw [← mul_apply_eq_comp, mul_assoc, hRS, mul_one]
  have hsum := basis_hasSum_norm_sq c (S y)
  have heq : (fun j => ‖inner ℂ (c j) (S y)‖^2) =
      (fun j => u j*‖inner ℂ (b j) (X y)‖^2) := by
    funext j
    rw [hcoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (hu j).le]
  rwa [heq, ← sqrt_inner_eq ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hA.nonneg)] at hsum

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def logarithmSandwich (A X : E →L[ℂ] E) (c : ℝ) : E →L[ℂ] E :=
  A + (c : ℂ) • (X * X)

theorem logarithmSandwich_parseval (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hX : X.IsSymmetric)
    (hiX : Function.Injective X) (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (c : ℝ) (y : E) :
    HasSum (fun j => (u j+c)*‖inner ℂ (b j) (X y)‖^2)
      (inner ℂ y (logarithmSandwich A X c y)).re := by
  have hh := (inverse_factor_form_parseval b A X hA hX hiX u hu he y).add
    ((basis_hasSum_norm_sq b (X y)).mul_left c)
  have hn : (inner ℂ y ((X*X) y)).re = ‖X y‖^2 := by
    have hx := hX y (X y)
    change inner ℂ (X y) (X y) = inner ℂ y (X (X y)) at hx
    rw [mul_apply_eq_comp, ← hx]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (X y)
  convert! hh using 1
  · ext j
    ring
  · simp only [logarithmSandwich, add_apply,
      smul_apply, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hn]

theorem gibbs_logarithmSandwich_parseval [Nonempty J] (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hX : X.IsSymmetric)
    (hiX : Function.Injective X) (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (hs : Summable (fun j => Real.exp (-u j))) (y : E) :
    HasSum (fun j => -Real.log (gibbsWeight u j)*‖inner ℂ (b j) (X y)‖^2)
      (inner ℂ y (logarithmSandwich A X (Real.log (heatPartition u)) y)).re := by
  convert! logarithmSandwich_parseval b A X hA hX hiX u hu he
    (Real.log (heatPartition u)) y using 1
  ext j
  rw [log_gibbsWeight u hs j]

omit [CompleteSpace E] in

theorem inverse_factor_eigen_preimage (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hiX : Function.Injective X)
    (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (j : J) (v : E) (t : ℂ) (hv : X v = t • b j) :
    A v = (u j : ℂ) • X (t • b j) := by
  have hi : Ring.inverse A (X (t • b j)) = (((u j)⁻¹ : ℝ) : ℂ) • v := by
    apply hiX
    calc
      X (Ring.inverse A (X (t • b j))) = t • ((X*Ring.inverse A*X) (b j)) := by
        simp only [mul_apply_eq_comp, map_smul]
      _ = t • ((((u j)⁻¹ : ℝ) : ℂ) • b j) := by rw [he]
      _ = X ((((u j)⁻¹ : ℝ) : ℂ) • v) := by
        simp only [map_smul, hv, smul_smul]
        congr 1
        ring
  have hAi (z : E) : A (Ring.inverse A z) = z := by
    change (A*Ring.inverse A) z = z
    rw [Ring.mul_inverse_cancel A hA.isUnit]
    rfl
  have hh : X (t • b j) = (((u j)⁻¹ : ℝ) : ℂ) • A v := by
    calc
      _ = A (Ring.inverse A (X (t • b j))) := (hAi _).symm
      _ = _ := by rw [hi, map_smul]
  rw [hh, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (hu j).ne', Complex.ofReal_one, one_smul]

omit [CompleteSpace E] in
theorem logarithmSandwich_eigen_preimage (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hiX : Function.Injective X)
    (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (c : ℝ) (j : J) (v : E) (t : ℂ) (hv : X v = t • b j) :
    logarithmSandwich A X c v = ((u j+c : ℝ) : ℂ) • X (t • b j) := by
  simp only [logarithmSandwich, add_apply,
    smul_apply, mul_apply_eq_comp]
  rw [inverse_factor_eigen_preimage b A X hA hiX u hu he j v t hv, hv,
    ← add_smul, ← Complex.ofReal_add]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

theorem weighted_spectral_vectors (b : HilbertBasis J ℂ (SequenceHilbert ι))
    (T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (he : ∀ j, T (b j) = (p j : ℂ) • b j)
    (w : ι → ℝ)
    (hm : Summable (fun i => w i^2*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re)) :
    ∃ y : J → SequenceHilbert ι,
      (∀ j i, y j i = (w i : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) ∧
      Summable (fun j => ‖y j‖^2) ∧
      (∑' j, ‖y j‖^2) = ∑' i, w i^2*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re := by
  let f : ι × J → ℝ := fun a => w a.1^2*(p a.2*‖b a.2 a.1‖^2)
  have hf0 (a : ι × J) : 0 ≤ f a := mul_nonneg (sq_nonneg _) (mul_nonneg (hp _) (sq_nonneg _))
  have hcol (i : ι) : HasSum (fun j => f (i,j))
      (w i^2*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by
    have hh := (hasSum_quadratic_eigenbasis b T p he (sequenceBasis ι i)).mul_left (w i^2)
    simpa only [f, norm_inner_symm, sequenceBasis_inner] using hh
  have hf : Summable f := by
    apply (summable_prod_of_nonneg hf0).mpr
    refine ⟨fun i => (hcol i).summable, ?_⟩
    simpa only [(hcol _).tsum_eq] using hm
  have hnorm (j : J) (i : ι) : ‖(w i : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)‖^2 = f (i,j) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (hp j), f]
  have hmem (j : J) : Memℓp (fun i => (w i : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) 2 := by
    apply memℓp_gen
    have hh : Summable (fun i => f (i,j)) := hf.prod_symm.prod_factor j
    convert! hh using 1
    funext i
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, hnorm]
  let y : J → SequenceHilbert ι := fun j => ⟨_, hmem j⟩
  have hy (j : J) : HasSum (fun i => f (i,j)) (‖y j‖^2) := by
    have hh := sequence_hasSum_norm_sq (y j)
    simpa only [y, hnorm] using hh
  refine ⟨y, fun _ _ => rfl, ?_, ?_⟩
  · have hh : Summable (fun j => ∑' i, f (i,j)) := hf.prod_symm.prod
    simpa only [(hy _).tsum_eq] using hh
  · calc
      _ = ∑' j, ∑' i, f (i,j) := tsum_congr (fun j => (hy j).tsum_eq.symm)
      _ = ∑' i, ∑' j, f (i,j) := Summable.tsum_comm (f := fun i j => f (i,j)) hf
      _ = _ := tsum_congr (fun i => (hcol i).tsum_eq)

end QuantumTrace

end

end OAI


