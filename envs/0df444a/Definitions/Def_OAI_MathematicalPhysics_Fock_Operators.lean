-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
-- name    : OAI_MathematicalPhysics_Fock_Operators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:02:28.200387+00:00
-- url     : https://prove2.me/theorems/9ddf608f-ef30-408a-be8b-1e993e3bfb24
-- title:
--   Number-weighted ladder operators, rank-one ensembles and the weighted thermal-noise generator on multimode Fock space
-- statement:
--   This file builds bounded versions of the bosonic creation and annihilation operators on the untruncated $n$-mode Fock space by sandwiching them between powers of the inverse number weight, and uses them to define a weighted form of the thermal-noise (Lindblad) generator acting on ensembles of vectors.
--
--   Notation: $\mathcal F_n = \ell^2(\mathbb{N}^n;\mathbb{C})$ is the $n$-mode Fock space with number basis $|k\rangle$, $k \in \mathbb{N}^n$; $\nu(k) = 1 + \sum_j k_j \ge 1$ is the number weight; $e_j\in\mathbb{N}^n$ is the $j$-th unit vector. For a family $x$ indexed by $\mathbb{N}^n$ write $x_k$ for its $k$-th coordinate. Formally the operators below are $N^{a}\,a_j\,N^{-b}$ and $N^{a}\,a_j^\dagger\,N^{-b}$, where $a_j$, $a_j^\dagger$ are the annihilation and creation operators of mode $j$ and $N$ is multiplication by $\nu$; the file defines them directly by their bounded coordinate formulas.
--
--   1. **Weighted pullbacks.** For an injective map $f:I\to J$ and coefficients $c:I\to\mathbb{C}$ with $|c_i|\le C$ ($C\ge 0$), the operator $P:\ell^2(J)\to\ell^2(I)$, $(Px)_i = c_i\,x_{f(i)}$, is bounded with $\|P\|\le C$. It maps $e_{f(i)}$ to $c_i e_i$ and kills $e_j$ for $j\notin f(I)$; its adjoint satisfies $(P^*x)_{f(i)} = \overline{c_i}\,x_i$ and $(P^*x)_j = 0$ for $j\notin f(I)$. Also $\sum_i |x_i|^2 = \|x\|^2$.
--
--   2. **Index shifts.** $\operatorname{up}_j(k) = k+e_j$ is injective with $\nu(k+e_j) = \nu(k)+1$; $\operatorname{down}_j(k)$ lowers the $j$-th coordinate by one (truncated at $0$), $\operatorname{down}_j(k+e_j)=k$, and $\operatorname{down}_j(k)+e_j = k$ if $k_j>0$. Every $k$ has $k_j=0$ or $k=l+e_j$ for some $l$. Moreover $k_j+1\le\nu(k)$ and $\sqrt{k_j+1}\le\nu(k)\le\nu(k+e_j)$.
--
--   3. **Sandwiched ladder operators.** For $a,b\in\mathbb{N}$ with $a+1\le b$ and a mode $j$:
--   $$
--   (A^{a,b}_j x)_k = \frac{\nu(k)^a\sqrt{k_j+1}}{\nu(k+e_j)^b}\,x_{k+e_j},\qquad (C^{a,b}_j x)_{k+e_j} = \frac{\nu(k+e_j)^a\sqrt{k_j+1}}{\nu(k)^b}\,x_k,\quad (C^{a,b}_jx)_k = 0 \text{ if } k_j = 0 .
--   $$
--   The coefficients are bounded by $1$ and $2^a$ respectively, so both are bounded operators ($C^{a,b}_j$ is defined as the adjoint of a weighted pullback). The inverse weights $(W_m x)_k = \nu(k)^{-m}x_k$ are injective and self-adjoint with $W_{a+b} = W_aW_b$, and $A^{0,b}_j = W_aA^{a,b}_j$, $C^{0,b}_j = W_aC^{a,b}_j$, $A^{a,b+t}_j = A^{a,b}_jW_t$, $C^{a,b+t}_j = C^{a,b}_jW_t$.
--
--   4. **Lowering and raising.** $L_j = A^{0,1}_j$ and $R_j = C^{0,1}_j$, so $(L_jx)_k = \sqrt{k_j+1}\,(W_1x)_{k+e_j}$ and $(R_jx)_{k+e_j} = \sqrt{k_j+1}\,(W_1x)_k$. For every $x\in\mathcal F_n$
--   $$
--   \|L_jx\|^2 = \sum_{k}k_j\,|(W_1x)_k|^2,\qquad \|R_jx\|^2 = \sum_k (k_j+1)\,|(W_1x)_k|^2,
--   $$
--   and $L_j^*W_1 = W_1R_j$, i.e. $\langle L_jx, W_1y\rangle = \langle W_1x, R_jy\rangle$.
--
--   5. **Rank-one ensembles.** For families $u,v$ in a Hilbert space with $\sum_i\|u_i\|^2<\infty$ and $\sum_i\|v_i\|^2<\infty$, the series $O(u,v) = \sum_i |u_i\rangle\langle v_i|$ converges absolutely in operator norm, $\sum_i\|u_i\|\|v_i\|<\infty$, and $\langle x, O(u,v)y\rangle = \sum_i\langle x,u_i\rangle\langle v_i,y\rangle$. For a bounded operator $Z$ the pairing $\Pi(u,v;Z) = \sum_i\langle v_i, Zu_i\rangle$ converges absolutely, and $\sum_i\|Zu_i\|^2<\infty$; for a Hilbert basis $(b_j)$ the family $|\langle b_j,u_i\rangle|^2$ is summable over pairs $(i,j)$.
--
--   6. **Mode bounds and gains.** For a mode $j$ and a direction $\sigma\in\{+,-\}$ (raising or lowering), $B^\sigma_j$ is the diagonal operator with entries $(k_j+[\sigma=+])/\nu(k)\in[0,1]$, the gain is $G^+_j = C^{2,3}_j$, $G^-_j = A^{2,3}_j$, and the unweighted gain is $\hat G^+_j = R_j$, $\hat G^-_j = L_j$. Then $W_2G^\sigma_j = \hat G^\sigma_jW_2$ and
--   $$
--   \langle W_3x,\ W_2B^\sigma_jx\rangle = \|\hat G^\sigma_j\,W_2x\|^2 .
--   $$
--
--   7. **Weighted generator.** For a family $x=(x_i)$ in $\mathcal F_n$ and $r\in\mathbb{R}$, the dissipator and generator are
--   $$
--   D^\sigma_j(x) = O(G^\sigma_jx, G^\sigma_jx) - \tfrac12\bigl(O(B^\sigma_jx, W_1x) + O(W_1x, B^\sigma_jx)\bigr),\qquad \mathcal L_r(x) = \sum_{j=1}^n\bigl((r+1)\,D^-_j(x) + r\,D^+_j(x)\bigr),
--   $$
--   where $G^\sigma_jx$ denotes the family $(G^\sigma_jx_i)_i$, and similarly for the others. The scalar pairing of the generator with a bounded $Z$ is the same expression with each $O(u,v)$ replaced by $\Pi(u,v;Z)$.
--
--   The generator mirrors, after conjugation by powers of the number weight, the Lindblad form $\sum_j (r+1)\bigl(a_j\rho a_j^\dagger - \tfrac12\{a_j^\dagger a_j,\rho\}\bigr) + r\bigl(a_j^\dagger\rho a_j - \tfrac12\{a_ja_j^\dagger,\rho\}\bigr)$ of thermal noise with mean photon number $r$, while every operator involved is bounded; this lets the unbounded ladder operators be handled on all of $\mathcal F_n$.
--
--   **Formalization Note** The pullback (`WeightedShift.pullCLM`) takes the bound $C$ and its proof as arguments; the sandwich operators require the proof of $a+1\le b$. The direction $\sigma$ is a `Bool` (`true` = raising). $O(u,v)$ (`CrossEnsemble.operator`) and $\Pi$ are defined with `tsum`, which is $0$ for non-summable series; the convergence statements above carry the square-summability hypotheses. The coordinate identity `quadratic_coordinate` is an auxiliary algebraic lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Fock/Operators.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/Fock/Operators.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate

namespace WeightedShift
variable {I J : Type*}
abbrev H (I : Type*) := lp (fun _ : I => ℂ) 2

theorem hasSum_square (x : H I) : HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) x

theorem pull_mem (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (_hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) :
    Memℓp (fun i => c i*x (f i)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply (((hasSum_square x).summable.comp_injective hf).mul_left (C^2)).of_nonneg_of_le
    (fun _ => sq_nonneg _)
  intro i
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc i) 2) (sq_nonneg _)

def pull (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) : H I :=
  ⟨_, pull_mem f hf c C hC hc x⟩
@[simp] theorem pull_apply (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) (i : I) :
    pull f hf c C hC hc x i = c i*x (f i) := rfl

theorem pull_bound (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) :
    ‖pull f hf c C hC hc x‖ ≤ C*‖x‖ := by
  have h₁ : ‖pull f hf c C hC hc x‖^2 ≤ C^2*∑' i, ‖x (f i)‖^2 := by
    rw [← (hasSum_square (pull f hf c C hC hc x)).tsum_eq, ← tsum_mul_left]
    apply Summable.tsum_le_tsum (fun i => ?_) (hasSum_square _).summable
      (((hasSum_square x).summable.comp_injective hf).mul_left _)
    simp only [pull_apply, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc i) 2) (sq_nonneg _)
  have h₂ : (∑' i, ‖x (f i)‖^2) ≤ ‖x‖^2 := by
    rw [← (hasSum_square x).tsum_eq]
    exact tsum_comp_le_tsum_of_inj (hasSum_square x).summable (fun _ => sq_nonneg _) hf
  have h₃ := mul_le_mul_of_nonneg_left h₂ (sq_nonneg C)
  nlinarith [norm_nonneg (pull f hf c C hC hc x), mul_nonneg hC (norm_nonneg x)]

def pullCLM (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) : H J →L[ℂ] H I :=
  LinearMap.mkContinuous
    { toFun := pull f hf c C hC hc
      map_add' := fun x y => by
        apply lp.ext
        funext i
        change c i*(x (f i)+y (f i)) = c i*x (f i)+c i*y (f i)
        ring
      map_smul' := fun z x => by
        apply lp.ext
        funext i
        change c i*(z*x (f i)) = z*(c i*x (f i))
        ring }
    C (pull_bound f hf c C hC hc)
@[simp] theorem pullCLM_apply (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H J) (i : I) :
    pullCLM f hf c C hC hc x i = c i*x (f i) := rfl

variable [DecidableEq I] [DecidableEq J]

theorem pullCLM_single (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (i : I) (z : ℂ) :
    pullCLM f hf c C hC hc (lp.single 2 (f i) z) = lp.single 2 i (c i*z) := by
  apply lp.ext
  funext k
  simp only [pullCLM_apply, lp.coeFn_single, Pi.single_apply]
  by_cases he : k = i
  · subst k; simp
  · have hh : f k ≠ f i := fun h => he (hf h)
    simp [he, hh]

omit [DecidableEq I] in
 theorem pullCLM_single_outside (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (j : J) (hj : ∀ i, f i ≠ j) (z : ℂ) :
    pullCLM f hf c C hC hc (lp.single 2 j z) = 0 := by
  apply lp.ext
  funext i
  simp [hj i]

 theorem adjoint_apply_image (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H I) (i : I) :
    (pullCLM f hf c C hC hc).adjoint x (f i) = conj (c i)*x i := by
  have hh := ContinuousLinearMap.adjoint_inner_right (pullCLM f hf c C hC hc)
    (lp.single 2 (f i) 1) x
  simpa only [pullCLM_single, mul_one, lp.inner_single_left, RCLike.inner_apply,
    map_one, one_mul, mul_comm] using hh

omit [DecidableEq I] in
 theorem adjoint_apply_outside (f : I → J) (hf : Function.Injective f) (c : I → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) (x : H I) (j : J) (hj : ∀ i, f i ≠ j) :
    (pullCLM f hf c C hC hc).adjoint x j = 0 := by
  have hh := ContinuousLinearMap.adjoint_inner_right (pullCLM f hf c C hC hc)
    (lp.single 2 j 1) x
  rw [pullCLM_single_outside f hf c C hC hc j hj, inner_zero_left] at hh
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hh

end WeightedShift

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

def up (j : Fin n) (k : NumberIndex n) : NumberIndex n := k + Pi.single j 1
@[simp] theorem up_same (j : Fin n) (k : NumberIndex n) : up j k j = k j+1 := by simp [up]
@[simp] theorem up_other (j l : Fin n) (hl : l ≠ j) (k : NumberIndex n) : up j k l = k l := by simp [up, Pi.single_eq_of_ne hl]
theorem up_injective (j : Fin n) : Function.Injective (up j) := by
  intro k l h
  exact add_right_cancel h
@[simp] theorem weight_up (j : Fin n) (k : NumberIndex n) : numberWeight (up j k) = numberWeight k+1 := by
  simp only [numberWeight, up, Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  have h : (∑ i : Fin n, (((Pi.single j 1 : Fin n → ℕ) i): ℝ)) = 1 := by
    simp only [Pi.single_apply]
    simp
  rw [h]
  ring

theorem coordinate_le_weight (j : Fin n) (k : NumberIndex n) : (k j:ℝ)+1 ≤ numberWeight k := by
  have h : (k j:ℝ) ≤ ∑ i : Fin n, (k i:ℝ) :=
    Finset.single_le_sum (fun i _ => Nat.cast_nonneg (k i)) (Finset.mem_univ j)
  dsimp [numberWeight]
  linarith

theorem sqrt_step_le_weight (j : Fin n) (k : NumberIndex n) : Real.sqrt ((k j:ℝ)+1) ≤ numberWeight (up j k) := by
  have h₁ := coordinate_le_weight j k
  have h₂ := numberWeight_one_le k
  have hs := Real.sq_sqrt (show 0 ≤ (k j:ℝ)+1 by positivity)
  have hp := Real.sqrt_nonneg ((k j:ℝ)+1)
  rw [weight_up]
  nlinarith

def coefficient (a b : ℕ) (j : Fin n) (k : NumberIndex n) : ℂ :=
  ((numberWeight k)^a*Real.sqrt ((k j:ℝ)+1)/(numberWeight (up j k))^b : ℝ)

theorem coefficient_bound (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (k : NumberIndex n) : ‖coefficient a b j k‖ ≤ 1 := by
  have hk := numberWeight_one_le k
  have hu := numberWeight_one_le (up j k)
  have hkpos : 0 < numberWeight k := by linarith
  have hupos : 0 < numberWeight (up j k) := by linarith
  have hm : numberWeight k ≤ numberWeight (up j k) := by rw [weight_up]; linarith
  have hp : numberWeight k^a*Real.sqrt ((k j:ℝ)+1) ≤ numberWeight (up j k)^(a+1) := by
    rw [pow_succ]
    exact mul_le_mul (pow_le_pow_left₀ hkpos.le hm a) (sqrt_step_le_weight j k)
      (Real.sqrt_nonneg _) (pow_nonneg hupos.le _)
  have hpow : numberWeight (up j k)^(a+1) ≤ numberWeight (up j k)^b :=
    pow_le_pow_right₀ hu hab
  rw [coefficient, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (pow_pos hupos b)).mpr (hp.trans hpow)

def sandwich (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) : Fock n →L[ℂ] Fock n :=
  WeightedShift.pullCLM (up j) (up_injective j) (coefficient a b j) 1 (by norm_num)
    (coefficient_bound a b hab j)
@[simp] theorem sandwich_apply (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    sandwich a b hab j x k = coefficient a b j k*x (up j k) := rfl

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

theorem sqrt_step_le_base (j : Fin n) (k : NumberIndex n) : Real.sqrt ((k j:ℝ)+1) ≤ numberWeight k := by
  have h₁ := coordinate_le_weight j k
  have h₂ := numberWeight_one_le k
  have hs := Real.sq_sqrt (show 0 ≤ (k j:ℝ)+1 by positivity)
  nlinarith [Real.sqrt_nonneg ((k j:ℝ)+1)]

def creationCoefficient (a b : ℕ) (j : Fin n) (k : NumberIndex n) : ℂ :=
  ((numberWeight (up j k))^a*Real.sqrt ((k j:ℝ)+1)/(numberWeight k)^b : ℝ)

theorem creationCoefficient_bound (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (k : NumberIndex n) :
    ‖creationCoefficient a b j k‖ ≤ 2^a := by
  have hk := numberWeight_one_le k
  have hkpos : 0 < numberWeight k := by linarith
  have hu : 0 < numberWeight (up j k) := by linarith [numberWeight_one_le (up j k)]
  have hup : numberWeight (up j k) ≤ 2*numberWeight k := by rw [weight_up]; linarith
  have hp : numberWeight (up j k)^a*Real.sqrt ((k j:ℝ)+1) ≤ 2^a*numberWeight k^(a+1) := by
    calc
      _ ≤ (2*numberWeight k)^a*numberWeight k := mul_le_mul
        (pow_le_pow_left₀ (by linarith [numberWeight_one_le (up j k)]) hup a)
        (sqrt_step_le_base j k) (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow, pow_succ]; ring
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk hab) (show (0:ℝ) ≤ 2^a by positivity)
  rw [creationCoefficient, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_iff₀ (pow_pos hkpos b)).mpr (hp.trans hpow)

def creationSandwich (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) : Fock n →L[ℂ] Fock n :=
  (WeightedShift.pullCLM (up j) (up_injective j) (creationCoefficient a b j) (2^a)
    (by positivity) (creationCoefficient_bound a b hab j)).adjoint

@[simp] theorem creationSandwich_up (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    creationSandwich a b hab j x (up j k) = creationCoefficient a b j k*x k := by
  rw [creationSandwich, WeightedShift.adjoint_apply_image]
  simp only [creationCoefficient, Complex.conj_ofReal]

@[simp] theorem creationSandwich_zero (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) (x : Fock n)
    (k : NumberIndex n) (hk : k j = 0) : creationSandwich a b hab j x k = 0 := by
  rw [creationSandwich]
  apply WeightedShift.adjoint_apply_outside
  intro l hl
  have hh := congrFun hl j
  rw [up_same, hk] at hh
  omega

def down (j : Fin n) (k : NumberIndex n) : NumberIndex n := Function.update k j (k j-1)
@[simp] theorem up_down (j : Fin n) (k : NumberIndex n) (hk : 0 < k j) : up j (down j k) = k := by
  funext i
  by_cases he : i = j
  · subst i; simp [down, Nat.sub_add_cancel hk]
  · simp [down, he]
@[simp] theorem down_up (j : Fin n) (k : NumberIndex n) : down j (up j k) = k := by
  funext i
  by_cases he : i = j
  · subst i; simp [down]
  · simp [down, he]

 theorem index_cases (j : Fin n) (k : NumberIndex n) : k j = 0 ∨ ∃ l, k = up j l := by
  by_cases hk : k j = 0
  · exact Or.inl hk
  · exact Or.inr ⟨down j k, (up_down j k (Nat.pos_of_ne_zero hk)).symm⟩

 theorem coefficient_inverse_bound (m : ℕ) (k : NumberIndex n) : ‖((numberWeight k^m)⁻¹ : ℂ)‖ ≤ 1 := by
  rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [numberWeight_one_le k])]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (numberWeight_one_le k))

def inverseWeight (m : ℕ) : Fock n →L[ℂ] Fock n :=
  WeightedShift.pullCLM id Function.injective_id (fun k => ((numberWeight k^m)⁻¹ : ℂ)) 1 (by norm_num)
    (coefficient_inverse_bound m)
@[simp] theorem inverseWeight_apply (m : ℕ) (x : Fock n) (k : NumberIndex n) :
    inverseWeight m x k = ((numberWeight k^m)⁻¹ : ℂ)*x k := rfl

theorem inverseWeight_injective (m : ℕ) : Function.Injective (inverseWeight (n := n) m) := by
  intro x y h
  apply lp.ext
  funext k
  have hh := congrArg (fun z : Fock n => z k) h
  simp only [inverseWeight_apply] at hh
  exact mul_left_cancel₀ (by exact inv_ne_zero (pow_ne_zero m (by exact_mod_cast (show numberWeight k ≠ 0 by linarith [numberWeight_one_le k])))) hh

theorem inverseWeight_add (a b : ℕ) : inverseWeight (n := n) (a+b) = inverseWeight a ∘L inverseWeight b := by
  ext x k
  simp only [inverseWeight_apply, ContinuousLinearMap.comp_apply, pow_add, mul_inv_rev]
  ring

 theorem sandwich_factor (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    sandwich 0 b (by omega) j = inverseWeight a ∘L sandwich a b hab j := by
  ext x k
  have hn : (numberWeight k : ℂ) ≠ 0 := by exact_mod_cast (show numberWeight k ≠ 0 by linarith [numberWeight_one_le k])
  simp only [ContinuousLinearMap.comp_apply, inverseWeight_apply, sandwich_apply, coefficient,
    pow_zero, one_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

 theorem creationSandwich_factor (a b : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    creationSandwich 0 b (by omega) j = inverseWeight a ∘L creationSandwich a b hab j := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp [creationSandwich_zero _ _ _ _ _ k hk]
  · have hn : (numberWeight (up j l) : ℂ) ≠ 0 := by exact_mod_cast (show numberWeight (up j l) ≠ 0 by linarith [numberWeight_one_le (up j l)])
    simp only [ContinuousLinearMap.comp_apply, inverseWeight_apply, creationSandwich_up, creationCoefficient,
      pow_zero, one_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

def lowering (j : Fin n) : Fock n →L[ℂ] Fock n := sandwich 0 1 (by omega) j
def raising (j : Fin n) : Fock n →L[ℂ] Fock n := creationSandwich 0 1 (by omega) j

@[simp] theorem lowering_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    lowering j x k = (Real.sqrt ((k j:ℝ)+1) : ℂ)*inverseWeight 1 x (up j k) := by
  simp only [lowering, sandwich_apply, coefficient, pow_zero, one_mul, pow_one,
    Complex.ofReal_div, inverseWeight_apply]
  ring

@[simp] theorem raising_up (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    raising j x (up j k) = (Real.sqrt ((k j:ℝ)+1) : ℂ)*inverseWeight 1 x k := by
  simp only [raising, creationSandwich_up, creationCoefficient, pow_zero, one_mul,
    pow_one, Complex.ofReal_div, inverseWeight_apply]
  ring

@[simp] theorem raising_zero (j : Fin n) (x : Fock n) (k : NumberIndex n) (hk : k j = 0) :
    raising j x k = 0 := creationSandwich_zero _ _ _ _ _ _ hk

 theorem lowering_sq (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    ‖lowering j x k‖^2 = ((k j:ℝ)+1)*‖inverseWeight 1 x (up j k)‖^2 := by
  rw [lowering_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

 theorem raising_sq (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    ‖raising j x (up j k)‖^2 = ((k j:ℝ)+1)*‖inverseWeight 1 x k‖^2 := by
  rw [raising_up, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

 theorem lowering_norm_sum (j : Fin n) (x : Fock n) :
    HasSum (fun k : NumberIndex n => (k j:ℝ)*‖inverseWeight 1 x k‖^2) (‖lowering j x‖^2) := by
  have hh := WeightedShift.hasSum_square (lowering j x)
  simp only [lowering_sq] at hh
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) :
      (k j:ℝ)*‖inverseWeight 1 x k‖^2 = 0 := by
    rcases index_cases j k with he | ⟨l,rfl⟩
    · simp [he]
    · exact (hk ⟨l,rfl⟩).elim
  apply (up_injective j).hasSum_iff hz |>.mp
  simpa only [Function.comp_def, up_same, Nat.cast_add, Nat.cast_one] using hh

 theorem raising_norm_sum (j : Fin n) (x : Fock n) :
    HasSum (fun k : NumberIndex n => ((k j:ℝ)+1)*‖inverseWeight 1 x k‖^2) (‖raising j x‖^2) := by
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) : ‖raising j x k‖^2 = 0 := by
    rcases index_cases j k with he | ⟨l,rfl⟩
    · simp [raising_zero _ _ _ he]
    · exact (hk ⟨l,rfl⟩).elim
  have hh := (up_injective j).hasSum_iff hz |>.mpr (WeightedShift.hasSum_square (raising j x))
  simpa only [Function.comp_def, raising_sq] using hh

 theorem inverseWeight_selfAdjoint (m : ℕ) : IsSelfAdjoint (inverseWeight (n := n) m) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜 := ℂ) (inverseWeight m x) y)
  convert! lp.hasSum_inner (𝕜 := ℂ) x (inverseWeight m y) using 1
  ext k
  simp only [inverseWeight_apply, RCLike.inner_apply, map_mul, map_inv₀, map_pow,
    Complex.conj_ofReal]
  ring

 theorem lowering_adjoint_inverse (j : Fin n) :
    (lowering j).adjoint ∘L inverseWeight 1 = inverseWeight 1 ∘L raising j := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · have hn : ∀ l, up j l ≠ k := by intro l he; have hh := congrFun he j; rw [up_same, hk] at hh; omega
    change (lowering j).adjoint (inverseWeight 1 x) k = inverseWeight 1 (raising j x) k
    have hh := WeightedShift.adjoint_apply_outside (up j) (up_injective j) (coefficient 0 1 j) 1 (by norm_num) (coefficient_bound 0 1 (by omega) j) (inverseWeight 1 x) k hn
    change (lowering j).adjoint (inverseWeight 1 x) k = 0 at hh
    rw [hh]
    simp [inverseWeight_apply, raising_zero _ _ _ hk]
  · change (lowering j).adjoint (inverseWeight 1 x) (up j l) = inverseWeight 1 (raising j x) (up j l)
    have hh := WeightedShift.adjoint_apply_image (up j) (up_injective j) (coefficient 0 1 j) 1 (by norm_num) (coefficient_bound 0 1 (by omega) j) (inverseWeight 1 x) l
    change (lowering j).adjoint (inverseWeight 1 x) (up j l) = _ at hh
    rw [hh]
    have hc : (starRingEnd ℂ) (coefficient 0 1 j l) = coefficient 0 1 j l :=
      Complex.conj_ofReal _
    rw [hc]
    simp only [coefficient, pow_zero, one_mul, pow_one,
      raising_up, inverseWeight_apply, Complex.ofReal_div]
    ring

 theorem ladder_adjoint_pairing (j : Fin n) (x y : Fock n) :
    inner ℂ (lowering j x) (inverseWeight 1 y) = inner ℂ (inverseWeight 1 x) (raising j y) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hh := congrArg (fun T : Fock n →L[ℂ] Fock n => T y) (lowering_adjoint_inverse j)
  change (lowering j).adjoint (inverseWeight 1 y) = inverseWeight 1 (raising j y) at hh
  rw [hh]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 1) x (raising j y)).symm

end Annihilation

namespace CrossEnsemble
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def operator (u v : I → E) : E →L[ℂ] E := ∑' i, InnerProductSpace.rankOne ℂ (u i) (v i)

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem norm_product_summable {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) : Summable (fun i => ‖u i‖*‖v i‖) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ (hu.add hv)
  intro i
  nlinarith [sq_nonneg (‖u i‖-‖v i‖)]

theorem hasSum_operator {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun i => InnerProductSpace.rankOne ℂ (u i) (v i)) (operator u v) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa only [InnerProductSpace.norm_rankOne] using norm_product_summable hu hv

theorem entry_hasSum {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (x y : E) :
    HasSum (fun i => inner ℂ x (u i)*inner ℂ (v i) y) (inner ℂ x (operator u v y)) := by
  convert! ((hasSum_operator hu hv).mapL (ContinuousLinearMap.apply ℂ E y)).mapL (innerSL ℂ x) using 1
  ext i
  simp [InnerProductSpace.rankOne_apply, mul_comm]

omit [CompleteSpace E] in
theorem square_coordinates_summable (b : HilbertBasis J ℂ E) {u : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) :
    Summable (fun ij : I × J => ‖inner ℂ (b ij.2) (u ij.1)‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  have hh (i : I) : HasSum (fun j => ‖inner ℂ (b j) (u i)‖^2) (‖u i‖^2) := by
    have ht := (b.hasSum_inner_mul_inner (u i) (u i)).mapL Complex.reCLM
    convert! ht using 1
    · ext j
      rw [← inner_conj_symm (u i) (b j), mul_comm, Complex.mul_conj]
      simp only [Complex.reCLM_apply, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    · simp [← Complex.ofReal_pow]
  refine ⟨fun i => (hh i).summable, ?_⟩
  simpa only [(hh _).tsum_eq] using hu

def pairing (u v : I → E) (Z : E →L[ℂ] E) : ℂ := ∑' i, inner ℂ (v i) (Z (u i))

omit [CompleteSpace E] in
theorem applied_summable {u : I → E} (hu : Summable (fun i => ‖u i‖^2)) (Z : E →L[ℂ] E) :
    Summable (fun i => ‖Z (u i)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hu.mul_left (‖Z‖^2))
  intro i
  calc
    _ ≤ (‖Z‖*‖u i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm _) _
    _ = _ := mul_pow _ _ _

omit [CompleteSpace E] in
theorem pairing_summable {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Summable (fun i => inner ℂ (v i) (Z (u i))) :=
  (norm_product_summable hv (applied_summable hu Z)).of_norm_bounded
    (fun _i => norm_inner_le_norm _ _)

end CrossEnsemble

namespace CrossEnsemble
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

def modeBound (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  WeightedShift.pullCLM id Function.injective_id
    (fun k => (((k j:ℝ)+(if upward then 1 else 0))/numberWeight k : ℝ)) 1 (by norm_num) (by
    intro k
    have hk := numberWeight_one_le k
    have hc := coordinate_le_weight j k
    have hp : 0 < numberWeight k := by linarith
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply (div_le_iff₀ hp).mpr
    cases upward <;> norm_num at * <;> linarith)

@[simp] theorem modeBound_apply (j : Fin n) (upward : Bool) (x : Fock n) (k : NumberIndex n) :
    modeBound j upward x k =
      ((((k j:ℝ)+(if upward then 1 else 0))/numberWeight k : ℝ):ℂ)*x k := rfl

theorem sandwich_right_inverse (a b t : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    sandwich a (b+t) (by omega) j = sandwich a b hab j ∘L inverseWeight t := by
  ext x k
  simp only [sandwich_apply, coefficient, inverseWeight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, pow_add]
  ring

theorem creationSandwich_right_inverse (a b t : ℕ) (hab : a+1 ≤ b) (j : Fin n) :
    creationSandwich a (b+t) (by omega) j = creationSandwich a b hab j ∘L inverseWeight t := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp [creationSandwich_zero _ _ _ _ _ k hk]
  · simp only [creationSandwich_up, creationCoefficient, inverseWeight_apply, ContinuousLinearMap.comp_apply,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, pow_add]
    ring

def gain (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  if upward then creationSandwich 2 3 (by omega) j else sandwich 2 3 (by omega) j

def unweightedGain (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  if upward then raising j else lowering j

theorem gain_factor (j : Fin n) (upward : Bool) :
    inverseWeight 2 ∘L gain j upward=unweightedGain j upward ∘L inverseWeight 2 := by
  cases upward
  · exact (sandwich_factor 2 3 (by omega) j).symm.trans (sandwich_right_inverse 0 1 2 (by omega) j)
  · exact (creationSandwich_factor 2 3 (by omega) j).symm.trans (creationSandwich_right_inverse 0 1 2 (by omega) j)

theorem quadratic_coordinate (w t : ℝ) (hw : 0 < w) (z : ℂ) :
    ((w:ℂ)^2)⁻¹ * ((t:ℂ)/(w:ℂ)*z) * (((w:ℂ)^3)⁻¹*conj z)=
      (t:ℂ)*((((|w|:ℝ):ℂ)^3)⁻¹*(‖z‖:ℂ))^2 := by
  rw [abs_of_pos hw]
  calc
    _ = (t:ℂ)*(w:ℂ)⁻¹^6*(z*conj z) := by ring
    _ = _ := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      ring

theorem mode_quadratic (j : Fin n) (upward : Bool) (x : Fock n) :
    inner ℂ (inverseWeight 3 x) (inverseWeight 2 (modeBound j upward x))=
      (‖unweightedGain j upward (inverseWeight 2 x)‖^2:ℝ) := by
  have hh : HasSum (fun k : NumberIndex n =>
      ((k j:ℝ)+(if upward then 1 else 0))*‖inverseWeight 3 x k‖^2)
      (‖unweightedGain j upward (inverseWeight 2 x)‖^2) := by
    have hi : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
      exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (inverseWeight_add 1 2).symm
    cases upward
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, unweightedGain, hi] using lowering_norm_sum j (inverseWeight 2 x)
    · simpa only [↓reduceIte, unweightedGain, hi] using raising_norm_sum j (inverseWeight 2 x)
  apply HasSum.unique (lp.hasSum_inner (𝕜 := ℂ) (inverseWeight 3 x) (inverseWeight 2 (modeBound j upward x)))
  convert! hh.mapL Complex.ofRealCLM using 1
  ext k
  simp only [RCLike.inner_apply, inverseWeight_apply, modeBound_apply, Complex.ofRealCLM_apply,
    map_mul, map_inv₀, map_pow, Complex.conj_ofReal, norm_mul, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_div]
  exact quadratic_coordinate _ _ (by have := numberWeight_one_le k; linarith) (x k)
end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

def dissipator (x : I → Fock n) (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  CrossEnsemble.operator (fun i => gain j upward (x i)) (fun i => gain j upward (x i))-
    (2:ℂ)⁻¹ • (CrossEnsemble.operator (fun i => modeBound j upward (x i)) (fun i => inverseWeight 1 (x i))+
      CrossEnsemble.operator (fun i => inverseWeight 1 (x i)) (fun i => modeBound j upward (x i)))

def generator (r : ℝ) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  ∑ j, (((r+1:ℝ):ℂ) • dissipator x j false+(r:ℂ) • dissipator x j true)

def pairing (r : ℝ) (x : I → Fock n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(CrossEnsemble.pairing (fun i => gain j false (x i)) (fun i => gain j false (x i)) Z-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun i => modeBound j false (x i)) (fun i => inverseWeight 1 (x i)) Z+
        CrossEnsemble.pairing (fun i => inverseWeight 1 (x i)) (fun i => modeBound j false (x i)) Z))+
    (r:ℂ)*(CrossEnsemble.pairing (fun i => gain j true (x i)) (fun i => gain j true (x i)) Z-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun i => modeBound j true (x i)) (fun i => inverseWeight 1 (x i)) Z+
        CrossEnsemble.pairing (fun i => inverseWeight 1 (x i)) (fun i => modeBound j true (x i)) Z)))

end WeightedGenerator

end

end

end OAI


