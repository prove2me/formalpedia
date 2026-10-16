-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
-- name    : OAI_InformationTheory_PhotonNumber_ThermalMetric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:20:39.126341+00:00
-- url     : https://prove2.me/theorems/f0ab938a-d7cb-40bc-918d-661db80488c4
-- title:
--   Thermal metric coefficients, defect vectors and centered annihilation matrices in a Gibbs eigenbasis
-- statement:
--   This file introduces a family of positive weights $m_r(p,q)$ on pairs of eigenvalues, built from the logarithmic mean and tilted by a thermal parameter $r>0$, together with a "defect" coefficient that they control exactly, and applies them to matrices of operators written in the eigenbasis of a Gibbs-form state.
--
--   Notation: $L(X,Y)$ is the logarithmic mean ($L(X,Y) = (Y-X)/(\log Y-\log X)$ for $X\ne Y$, $L(X,X) = X$); $f(x) = x/\sinh x$ ($f(0)=1$) and $T(m,x,y) = m\,f(x)f(y)/f(x+y)$. On the $n$-mode Fock space $\mathcal F_n = \ell^2(\mathbb{N}^n)$, $\nu(k) = 1+\sum_jk_j$, $W_m$ multiplies the $k$-th coordinate by $\nu(k)^{-m}$, and $L_j$, $R_j$ are the number-weighted lowering and raising operators, $(L_jx)_k = \sqrt{k_j+1}\,(W_1x)_{k+e_j}$, $(R_jx)_{k+e_j} = \sqrt{k_j+1}\,(W_1x)_k$ and $(R_jx)_k = 0$ if $k_j = 0$.
--
--   1. **Thermal weights.** For $r>0$ put $h(r) = \log(r+1)-\log r>0$, the frequency $\omega_r(p,q) = (\log p-\log q)/h(r)$, and $w_r(v) = T\bigl(1/h(r),\ h(r)v/2,\ -h(r)/2\bigr)>0$. Then $L(r,r+1) = 1/h(r)$, and for $p,q>0$
--   $$
--   L(p,q)\;w_r\bigl(\omega_r(p,q)\bigr) = L\bigl(rp,(r+1)q\bigr),\qquad r\le w_r\bigl(\omega_r(p,q)\bigr)\le r+1 .
--   $$
--
--   2. **Metric and defect coefficients.** The defect coefficient is $\delta_r(p,q) = (r+1)q-rp$ and the metric coefficient is $m_r(p,q) = h(r)\,L(p,q)\,w_r(\omega_r(p,q))$. For $r,p,q>0$: $m_r(p,q)>0$, $m_r(p,p) = p$, $L(p,q)(\log q-\log p) = q-p$, and
--   $$
--   \delta_r(p,q) = \bigl(1-\omega_r(p,q)\bigr)\,m_r(p,q),\qquad \frac{\delta_r(p,q)^2}{m_r(p,q)} = \bigl(1-\omega_r(p,q)\bigr)\,\delta_r(p,q).
--   $$
--
--   3. **Vectors on pairs.** For weights $a_j\ge0$ and $z$ with $\sum_ja_j|z_j|^2<\infty$, the family $(\sqrt{a_j}\,z_j)$ lies in $\ell^2$. Given $r>0$, positive $p:J\to\mathbb{R}$ and $d:J\times J\to\mathbb{C}$ with $\sum_{(l,s)}(1-\omega_r(p_l,p_s))\,\delta_r(p_l,p_s)\,|d(l,s)|^2<\infty$, the defect vector has entries $\delta_r(p_l,p_s)\,m_r(p_l,p_s)^{-1/2}\,d(l,s)$, and the defect functional is the inner product with it. If moreover $\sum_jp_j<\infty$, the identity vector has entries $\sqrt{m_r(p_l,p_s)}\,[l=s]$ and the centered space is its orthogonal complement in $\ell^2(J\times J)$. With $c_j = -\log p_j$, the defect series above converges as soon as the six series $\sum p_s|d|^2$, $\sum p_l|d|^2$, $\sum c_lp_s|d|^2$, $\sum c_sp_s|d|^2$, $\sum c_lp_l|d|^2$, $\sum c_sp_l|d|^2$ converge. The diagonal mean is $\mu(p,d) = \sum_jp_j\,d(j,j)$. For a Hilbert basis $(b_l)$, $p>0$ summable, $t>0$ and any bounded $Z$, $\sum_{l,s}m_t(p_l,p_s)\,|\langle b_l,Zb_s\rangle|^2<\infty$, which defines the matrix vector $\bigl(\sqrt{m_t(p_l,p_s)}\langle b_l,Zb_s\rangle\bigr)$.
--
--   4. **Centered annihilation matrices.** For a Hilbert basis $(b_l)$ of $\mathcal F_n$, weights $p$ and a family $(x_s)$, the lowering entries are $\lambda_j(l,s) = \langle b_l,L_jW_2x_s\rangle/\sqrt{p_s}$, and the centered entries are $\lambda_j(l,s)-\mu\,[l=s]$ for $\mu\in\mathbb{C}$. Summability results: $\sum_{l,s}|\langle b_l,\hat GW_2x_s\rangle|^2<\infty$ for $\hat G\in\{L_j,R_j\}$ when $\sum_s\|x_s\|^2<\infty$; if $F\ge0$, $\sum F|d|^2<\infty$ and $\sum_jF(j,j)<\infty$ then $\sum F(a)\,|d(a)-\mu[a_1=a_2]|^2<\infty$; and, under the hypotheses $p_s>0$, $\sum p<\infty$, $\sum\|x_s\|^2<\infty$, $W_3x_s = \sqrt{p_s}\,b_s$, a symmetric $S$ with $\sum_lc_l|\langle b_l,W_2y\rangle|^2 = \operatorname{Re}\langle y,Sy\rangle$ for all $y$, $c\ge0$ and $S(W_1x_s) = c_s\,W_5x_s$, one has $\sum_sc_sp_s<\infty$ and all six weighted series of item 3 converge for the centered entries. The centered ladder operators are $(L_j-\mu W_1)W_2$ and $(R_j-\bar\mu W_1)W_2$, and for $t\in\mathbb{R}$ the weak defect of a family $x$ against $Z$ is
--   $$
--   (t+1)\sum_s\bigl\langle (L_j-\mu W_1)W_2x_s,\ Z\,W_3x_s\bigr\rangle - t\sum_s\bigl\langle W_3x_s,\ Z\,(R_j-\bar\mu W_1)W_2x_s\bigr\rangle .
--   $$
--
--   5. **Gibbs states.** For a state $\rho$ with Gibbs data ($\rho = \sum_l\gamma_l|b_l\rangle\langle b_l|$ with $\gamma_l = e^{-u_l}/\sum e^{-u}$, eigenvalue relation for the bounded operator $\kappa+VBV$, finite seventh number moment) and its spectral columns $x_s$ (square-summable with $W_3x_s = \sqrt{\gamma_s}\,b_s$), the annihilation matrix is $A_j(l,s) = \lambda_j(l,s)$ with $p = \gamma$, its mean is $\mu_j = \sum_l\gamma_lA_j(l,l)$, and the centered matrix is $A_j-\mu_j\,\mathrm{Id}$. If $\kappa>0$, the six weighted series and hence the defect series of the centered matrix converge for every $t$, and for $t>0$ this gives a bounded defect functional on the centered space. The observable vector of a bounded $Z$ is its matrix vector in the basis $(b_l)$ with $p=\gamma$.
--
--   6. **Matrix units.** $|a\rangle\langle b|$ denotes the rank-one number matrix unit; $\langle a|x\rangle = x_a$, $\langle x|a\rangle = \overline{x_a}$, and $\langle v,|a\rangle\langle b|\,u\rangle = u_b\,\overline{v_a}$.
--
--   The weights $m_r(p,q)$ define a weighted Hilbert space of matrices indexed by pairs of eigenvalues of a state, and the identity $\delta^2/m = (1-\omega)\delta$ is what lets the defect functional be represented as an inner product in that space; the summability statements show that the centered annihilation matrix of a Gibbs state lies in the required weighted spaces.
--
--   **Formalization Note** The Gibbs data structure is `GibbsData n κ ρ`, its eigenvalues are `G.probability`, and its spectral columns are chosen with `Classical.choose`. Sums are `tsum`s over `J × J`; the diagonal mean is $0$ if its series diverges. The centered space is the kernel of `innerSL` applied to the identity vector. A private `if`-rewriting lemma is plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric

section
open EntropyPhotonNumber DiagonalForms.System

def h (r : ℝ) : ℝ := Real.log (r+1)-Real.log r

theorem h_pos {r : ℝ} (hr : 0<r) : 0<h r :=
  sub_pos.mpr (Real.strictMonoOn_log hr (show 0<r+1 by linarith) (by linarith))

def frequency (r p q : ℝ) : ℝ := (Real.log p-Real.log q)/h r

def weight (r v : ℝ) : ℝ := fourWeightTarget (1/h r) (h r*v/2) (-h r/2)

theorem logMean_reference {r : ℝ} (_hr : 0<r) : logMean r (r+1)=1/h r := by
  rw [logMean, ite_eq_right (by linarith : r≠r+1)]
  unfold h
  congr 1
  ring

theorem weight_pos {r : ℝ} (hr : 0<r) (v : ℝ) : 0<weight r v :=
  fourWeightTarget_pos (div_pos (by norm_num) (h_pos hr)) _ _

theorem tilted_logMean {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    logMean p q*weight r (frequency r p q)=logMean (r*p) ((r+1)*q) := by
  rw [weight, frequency, mul_div_cancel₀ _ (h_pos hr).ne', ← logMean_reference hr]
  have he : -h r/2=(Real.log r-Real.log (r+1))/2 := by unfold h; ring
  rw [he]
  simpa only [mul_comm r p, mul_comm (r+1) q] using (logMean_product hp hq hr (by positivity)).symm

theorem weight_frequency_bounds {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    r≤weight r (frequency r p q) ∧ weight r (frequency r p q)≤r+1 := by
  have h₁ := logMean_mono (mul_pos hr hp) (mul_pos hr hq) le_rfl
    (mul_le_mul_of_nonneg_right (by linarith : r≤r+1) hq.le)
  have h₂ := logMean_mono (mul_pos hr hp) (mul_pos (by positivity : 0<r+1) hq)
    (mul_le_mul_of_nonneg_right (by linarith : r≤r+1) hp.le) le_rfl
  rw [logMean_scale hp hq hr, ← tilted_logMean hr hp hq] at h₁
  rw [logMean_scale hp hq (by positivity : 0<r+1), ← tilted_logMean hr hp hq] at h₂
  have hl := logMean_pos hp hq
  constructor <;> nlinarith

end

section
open DiagonalForms.System

theorem logMean_mul_log_sub {p q : ℝ} (hp : 0<p) (hq : 0<q) :
    logMean p q*(Real.log q-Real.log p)=q-p := by
  by_cases he : p=q
  · subst q; simp
  · rw [logMean, ite_eq_right he]
    apply div_mul_cancel₀
    intro h
    apply he
    exact Real.log_injOn_pos hp hq (sub_eq_zero.mp h).symm

def defectCoefficient (r p q : ℝ) : ℝ := (r+1)*q-r*p

def metricCoefficient (r p q : ℝ) : ℝ :=
  h r*logMean p q*weight r (frequency r p q)

theorem metricCoefficient_pos {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    0 < metricCoefficient r p q :=
  mul_pos (mul_pos (h_pos hr) (logMean_pos hp hq)) (weight_pos hr _)

theorem defect_multiplier {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    defectCoefficient r p q = (1-frequency r p q)*metricCoefficient r p q := by
  have ht := tilted_logMean hr hp hq
  have hl := logMean_mul_log_sub (mul_pos hr hp) (mul_pos (by positivity : 0<r+1) hq)
  rw [Real.log_mul (by positivity : r+1≠0) hq.ne', Real.log_mul hr.ne' hp.ne'] at hl
  rw [← ht] at hl
  unfold defectCoefficient metricCoefficient frequency h at *
  have hh : Real.log (r+1)-Real.log r≠0 := (h_pos hr).ne'
  field_simp
  linear_combination -hl

theorem defect_dual_square {r p q : ℝ} (hr : 0<r) (hp : 0<p) (hq : 0<q) :
    (defectCoefficient r p q)^2/metricCoefficient r p q =
      (1-frequency r p q)*defectCoefficient r p q := by
  rw [defect_multiplier hr hp hq]
  field_simp [(metricCoefficient_pos hr hp hq).ne']

end

section
open EntropyPhotonNumber
variable {J : Type*}

def weightedVector (a : J → ℝ) (z : J → ℂ)
    (hz : Summable (fun j => a j*‖z j‖^2)) (ha : ∀ j, 0 ≤ a j) :
    lp (fun _ : J => ℂ) 2 := by
  refine ⟨fun j => (Real.sqrt (a j):ℂ)*z j, ?_⟩
  apply memℓp_gen
  convert! hz using 1
  funext j
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (ha j)]

@[simp] theorem weightedVector_apply (a : J → ℝ) (z : J → ℂ)
    (hz : Summable (fun j => a j*‖z j‖^2)) (ha : ∀ j, 0 ≤ a j) (j : J) :
    weightedVector a z hz ha j=(Real.sqrt (a j):ℂ)*z j := rfl

theorem defectVector_entry_norm (r p q : ℝ) (hr : 0<r) (hp : 0<p) (hq : 0<q) (d : ℂ) :
    ‖((defectCoefficient r p q / Real.sqrt (metricCoefficient r p q):ℝ):ℂ)*d‖^2 =
      (1-frequency r p q)*defectCoefficient r p q*‖d‖^2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (metricCoefficient_pos hr hp hq).le, defect_dual_square hr hp hq]

def defectVector (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ)
    (hd : Summable (fun a : J × J =>
      (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2)) :
    lp (fun _ : J × J => ℂ) 2 := by
  refine ⟨fun a => ((defectCoefficient r (p a.1) (p a.2) /
    Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℝ):ℂ)*d a, ?_⟩
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    defectVector_entry_norm r _ _ hr (hp _) (hp _)] using hd

@[simp] theorem defectVector_apply (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (a : J × J) :
    defectVector r hr p hp d hd a=((defectCoefficient r (p a.1) (p a.2) /
      Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℝ):ℂ)*d a := rfl

end

section
variable {J : Type*}

def defectFunctional (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ)
    (hd : Summable (fun a : J × J =>
      (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2)) :
    lp (fun _ : J × J => ℂ) 2 →L[ℂ] ℂ :=
  innerSL ℂ (defectVector r hr p hp d hd)

end

open scoped ComplexConjugate
variable {J : Type*}

@[simp] theorem metricCoefficient_self {r p : ℝ} (hr : 0<r) (hp : 0<p) :
    metricCoefficient r p p=p := by
  have hh := defect_multiplier hr hp hp
  simp only [frequency, sub_self, zero_div, sub_zero, one_mul, defectCoefficient] at hh
  nlinarith

theorem summable_diagonal [DecidableEq J] {f : J → ℝ} (hf : Summable f) :
    Summable (fun a : J × J => if a.1=a.2 then f a.1 else 0) := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  apply (hi.summable_iff (fun a ha => ?_)).mp
  · simpa only [Function.comp_def, ↓reduceIte] using hf
  · have hn : a.1≠a.2 := by
      intro he
      exact ha ⟨a.1, Prod.ext rfl he⟩
    simp only [hn, ↓reduceIte]

def identityEntry (a : J × J) : ℂ := by
  classical
  exact if a.1=a.2 then 1 else 0

theorem identityEntry_summable (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) :
    Summable (fun a : J × J => metricCoefficient r (p a.1) (p a.2)*‖identityEntry a‖^2) := by
  classical
  convert! summable_diagonal hs using 1
  ext a
  by_cases he : a.1=a.2
  · simp only [identityEntry, he, ↓reduceIte, norm_one, one_pow, mul_one,
      metricCoefficient_self hr (hp _)]
  · simp only [identityEntry, he, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero]

def identityVector (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j) (hs : Summable p) :
    lp (fun _ : J × J => ℂ) 2 :=
  weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) identityEntry
    (identityEntry_summable r hr p hp hs) (fun _a => (metricCoefficient_pos hr (hp _) (hp _)).le)

def centeredSpace (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j) (hs : Summable p) :
    Submodule ℂ (lp (fun _ : J × J => ℂ) 2) :=
  (innerSL ℂ (identityVector r hr p hp hs)).ker

theorem defect_series_summable (t : ℝ) (p : J → ℝ) (c : J → ℝ)
    (hc : ∀ j, c j = -Real.log (p j)) (d : J × J → ℂ)
    (h₁ : Summable (fun a : J × J => p a.2*‖d a‖^2))
    (h₂ : Summable (fun a : J × J => p a.1*‖d a‖^2))
    (h₃ : Summable (fun a : J × J => c a.1*p a.2*‖d a‖^2))
    (h₄ : Summable (fun a : J × J => c a.2*p a.2*‖d a‖^2))
    (h₅ : Summable (fun a : J × J => c a.1*p a.1*‖d a‖^2))
    (h₆ : Summable (fun a : J × J => c a.2*p a.1*‖d a‖^2)) :
    Summable (fun a : J × J => (1-frequency t (p a.1) (p a.2))*
      defectCoefficient t (p a.1) (p a.2)*‖d a‖^2) := by
  convert! ((h₁.mul_left (t+1)).sub (h₂.mul_left t)).add
    ((((h₃.sub h₄).mul_left (t+1)).sub ((h₅.sub h₆).mul_left t)).div_const (h t)) using 1
  ext a
  simp only [hc, frequency, defectCoefficient]
  ring

def diagonalMean (p : J → ℝ) (d : J × J → ℂ) : ℂ := ∑' j, (p j:ℂ)*d (j,j)

end ThermalMetric

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

def centeredEntry (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (x : J → Fock n)
    (j : Fin n) (μ : ℂ) (l r : J) : ℂ := by
  classical
  exact loweringEntry b p x j l r - if l=r then μ else 0

theorem nonlog_summable (b : HilbertBasis J ℂ (Fock n))
    (x : J → Fock n) (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (u : Bool) :
    Summable (fun a : J × J => ‖spectralGain b x j u a.1 a.2‖^2) := by
  have hs := CrossEnsemble.applied_summable hx (unweightedGain j u ∘L inverseWeight 2)
  have hh := CrossEnsemble.square_coordinates_summable b hs
  simpa only [spectralGain, ContinuousLinearMap.comp_apply, Prod.swap] using hh.prod_symm

theorem centered_weight_summable [DecidableEq J] (f : J × J → ℝ) (hf : ∀ a, 0 ≤ f a)
    (d : J × J → ℂ) (hd : Summable (fun a => f a*‖d a‖^2))
    (hdiag : Summable (fun j => f (j,j))) (μ : ℂ) :
    Summable (fun a : J × J => f a*‖d a-(if a.1=a.2 then μ else 0)‖^2) := by
  classical
  have ht : Summable (fun a : J × J => if a.1=a.2 then f a*‖μ‖^2 else 0) := by
    apply (summable_prod_of_nonneg (by intro a; dsimp only; split_ifs; exact mul_nonneg (hf a) (sq_nonneg _); exact le_rfl)).mpr
    refine ⟨?_, ?_⟩
    · intro l
      have hh := (hasSum_ite_eq' l (f (l,l)*‖μ‖^2)).summable
      convert! hh using 1
      ext q
      by_cases h : l=q
      · subst q; rfl
      · simp only [h, ↓reduceIte]
    · simpa only [tsum_ite_eq'] using hdiag.mul_right (‖μ‖^2)
  apply Summable.of_nonneg_of_le (fun a => mul_nonneg (hf a) (sq_nonneg _)) _
    ((hd.mul_left 2).add (ht.mul_left 2))
  intro a
  by_cases he : a.1=a.2
  · simp only [he, ↓reduceIte]
    have hn := norm_sub_le (d a) μ
    have hsq : ‖d a-μ‖^2 ≤ 2*‖d a‖^2+2*‖μ‖^2 := by
      nlinarith [sq_nonneg (‖d a‖-‖μ‖), norm_nonneg (d a-μ), norm_nonneg (d a), norm_nonneg μ]
    nlinarith [mul_le_mul_of_nonneg_left hsq (hf a)]
  · simp only [he, ↓reduceIte, sub_zero, mul_zero, add_zero]
    nlinarith [mul_nonneg (hf a) (sq_nonneg ‖d a‖)]

theorem entropy_weight_summable (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (S : Fock n →L[ℂ] Fock n) (c : J → ℝ)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r)) :
    Summable (fun r => c r*p r) := by
  have hs := CrossEnsemble.applied_summable hx (inverseWeight 1)
  have ht := (CrossEnsemble.pairing_summable hs hs S).hasSum.mapL Complex.reCLM
  convert! ht.summable using 1
  ext r
  simp only [Complex.reCLM_apply, he, inner_smul_right]
  have hw : inner ℂ (inverseWeight 1 (x r)) (inverseWeight 5 (x r))=
      inner ℂ (inverseWeight 3 (x r)) (inverseWeight 3 (x r)) := by
    have h5 : inverseWeight 5 (x r)=inverseWeight 2 (inverseWeight 3 (x r)) := by
      exact congrArg (fun T : Fock n →L[ℂ] Fock n => T (x r)) (inverseWeight_add 2 3)
    rw [h5]
    calc
      _ = inner ℂ (inverseWeight 2 (inverseWeight 1 (x r))) (inverseWeight 3 (x r)) :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 2)
          (inverseWeight 1 (x r)) (inverseWeight 3 (x r))).symm
      _ = _ := by
        congr 1
        change (inverseWeight 2 ∘L inverseWeight 1) (x r)=_
        rw [← inverseWeight_add]
  rw [hw, hi, inner_self_eq_norm_sq_to_K, norm_smul, b.orthonormal.norm_eq_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  norm_cast
  rw [Real.sq_sqrt (hp r).le]
  simp

theorem centered_six_sums (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ r, 0<p r) (hs : Summable p) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (p r):ℂ) • b r)
    (S : Fock n →L[ℂ] Fock n) (hS : S.IsSymmetric) (c : J → ℝ)
    (hc : ∀ l, 0 ≤ c l)
    (hf : ∀ y, HasSum (fun l => c l*‖inner ℂ (b l) (inverseWeight 2 y)‖^2)
      (inner ℂ y (S y)).re)
    (he : ∀ r, S (inverseWeight 1 (x r)) = (c r : ℂ) • inverseWeight 5 (x r))
    (j : Fin n) (μ : ℂ) :
    Summable (fun a : J × J => p a.2*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => p a.1*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => c a.1*p a.2*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => c a.2*p a.2*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => c a.1*p a.1*‖centeredEntry b p x j μ a.1 a.2‖^2) ∧
    Summable (fun a : J × J => c a.2*p a.1*‖centeredEntry b p x j μ a.1 a.2‖^2) := by
  classical
  have hec := entropy_weight_summable b p hp x hx hi S c he
  have hd := nonlog_summable b x hx j false
  have hu := (nonlog_summable b x hx j true).prod_symm
  have hcd := crossed_log_summable b x hx S c hc hf j false
  have hud := uncrossed_log_summable b x hx S hS c hc he j false
  have hcu := (crossed_log_summable b x hx S c hc hf j true).prod_symm
  have huu := (uncrossed_log_summable b x hx S hS c hc he j true).prod_symm
  simp only [spectralGain_lowering_sq b p hp, spectralGain_raising_sq b p hp x hi,
    Prod.swap, ← mul_assoc] at hd hu hcd hud hcu huu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact centered_weight_summable (fun a => p a.2) (fun a => (hp a.2).le)
      (fun a => loweringEntry b p x j a.1 a.2) hd hs μ
  · exact centered_weight_summable (fun a => p a.1) (fun a => (hp a.1).le)
      (fun a => loweringEntry b p x j a.1 a.2) hu hs μ
  · exact centered_weight_summable (fun a => c a.1*p a.2) (fun a => mul_nonneg (hc _) (hp _).le)
      (fun a => loweringEntry b p x j a.1 a.2) hcd hec μ
  · exact centered_weight_summable (fun a => c a.2*p a.2) (fun a => mul_nonneg (hc _) (hp _).le)
      (fun a => loweringEntry b p x j a.1 a.2) hud hec μ
  · exact centered_weight_summable (fun a => c a.1*p a.1) (fun a => mul_nonneg (hc _) (hp _).le)
      (fun a => loweringEntry b p x j a.1 a.2) huu hec μ
  · exact centered_weight_summable (fun a => c a.2*p a.1) (fun a => mul_nonneg (hc _) (hp _).le)
      (fun a => loweringEntry b p x j a.1 a.2) hcu hec μ

end WeightedGenerator

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ} {J : Type*}

def centeredLadder (j : Fin n) (μ : ℂ) (up : Bool) : Fock n →L[ℂ] Fock n :=
  (if up then raising j-conj μ • inverseWeight 1 else lowering j-μ • inverseWeight 1) ∘L inverseWeight 2

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

def annihilationMatrix (j : Fin n) (a : G.J × G.J) : ℂ :=
  loweringEntry G.basis G.probability G.spectralColumns j a.1 a.2

def annihilationMean (j : Fin n) : ℂ := diagonalMean G.probability (G.annihilationMatrix j)

def centeredMatrix (j : Fin n) (a : G.J × G.J) : ℂ :=
  centeredEntry G.basis G.probability G.spectralColumns j (G.annihilationMean j) a.1 a.2

theorem centeredMatrix_six_sums (hk : 0<k) (j : Fin n) :
    Summable (fun a : G.J × G.J => G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.probability a.1*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.1*G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.2*G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.1*G.probability a.1*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.2*G.probability a.1*‖G.centeredMatrix j a‖^2) :=
  centered_six_sums G.basis G.probability G.probability_pos G.probability_sum.summable
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse
    G.logSandwich (G.logSandwich_symmetric hk) G.logCoefficient G.logCoefficient_nonneg
    (G.logSandwich_parseval hk)
    (fun r => G.logSandwich_preimage hk r _ (G.spectralColumns_inverse r)) j (G.annihilationMean j)

theorem centeredMatrix_defect_summable (hk : 0<k) (t : ℝ) (j : Fin n) :
    Summable (fun a : G.J × G.J =>
      (1-frequency t (G.probability a.1) (G.probability a.2))*
      defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2) := by
  rcases G.centeredMatrix_six_sums hk j with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  exact defect_series_summable t G.probability G.logCoefficient (fun _ => rfl)
    (G.centeredMatrix j) h₁ h₂ h₃ h₄ h₅ h₆

def defect (hk : 0<k) (t : ℝ) (ht : 0<t) (j : Fin n) :
    centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable →L[ℂ] ℂ :=
  (defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable hk t j)).comp
    (centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable).subtypeL

end EntropyPhotonNumber.GibbsData

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

def weakDefect (t : ℝ) (x : J → Fock n) (j : Fin n) (μ : ℂ)
    (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  (t+1:ℂ)*CrossEnsemble.pairing (fun r => inverseWeight 3 (x r))
    (fun r => centeredLadder j μ false (x r)) Z-
  (t:ℂ)*CrossEnsemble.pairing (fun r => centeredLadder j μ true (x r))
    (fun r => inverseWeight 3 (x r)) Z

end WeightedGenerator

namespace ThermalMetric
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem bounded_matrix_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (t : ℝ) (ht : 0<t) (Z : E →L[ℂ] E) :
    Summable (fun a : J × J => metricCoefficient t (p a.1) (p a.2)*
      ‖inner ℂ (b a.1) (Z (b a.2))‖^2) := by
  let u : J → E := fun r => (Real.sqrt (p r):ℂ) • b r
  have hu : Summable (fun r => ‖u r‖^2) := by
    convert! hs using 1
    ext r
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hp r).le, b.orthonormal.norm_eq_one r, mul_one]
  have hc : Summable (fun a : J × J => p a.2*‖inner ℂ (b a.1) (Z (b a.2))‖^2) := by
    have hh := (CrossEnsemble.square_coordinates_summable b (CrossEnsemble.applied_summable hu Z)).prod_symm
    simpa only [Prod.swap, u, map_smul, inner_smul_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hp _).le] using hh
  have hr : Summable (fun a : J × J => p a.1*‖inner ℂ (b a.1) (Z (b a.2))‖^2) := by
    have hh := CrossEnsemble.square_coordinates_summable b (CrossEnsemble.applied_summable hu Z.adjoint)
    simpa only [u, map_smul, inner_smul_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hp _).le,
      ContinuousLinearMap.adjoint_inner_right, norm_inner_symm] using hh
  apply Summable.of_nonneg_of_le
    (fun a => mul_nonneg (metricCoefficient_pos ht (hp _) (hp _)).le (sq_nonneg _)) _
    (((hr.mul_left t).add (hc.mul_left (t+1))).mul_left (h t/2))
  intro a
  have hh := DiagonalForms.System.logMean_le_arithmetic (mul_pos ht (hp a.1))
    (mul_pos (by positivity : 0<t+1) (hp a.2))
  have hm : metricCoefficient t (p a.1) (p a.2) =
      h t*DiagonalForms.System.logMean (t*p a.1) ((t+1)*p a.2) := by
    rw [metricCoefficient, mul_assoc, tilted_logMean ht (hp _) (hp _)]
  rw [hm]
  have hh' := mul_le_mul_of_nonneg_left hh (h_pos ht).le
  nlinarith [mul_le_mul_of_nonneg_right hh' (sq_nonneg ‖inner ℂ (b a.1) (Z (b a.2))‖)]

def matrixVector (t : ℝ) (ht : 0<t) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (z : J × J → ℂ)
    (hz : Summable (fun a : J × J => metricCoefficient t (p a.1) (p a.2)*‖z a‖^2)) :
    lp (fun _ : J × J => ℂ) 2 :=
  weightedVector (fun a : J × J => metricCoefficient t (p a.1) (p a.2)) z hz
    (fun a => (metricCoefficient_pos ht (hp a.1) (hp a.2)).le)

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

def observableVector (t : ℝ) (ht : 0<t) (Z : Fock n →L[ℂ] Fock n) :
    lp (fun _ : G.J × G.J => ℂ) 2 :=
  matrixVector t ht G.probability G.probability_pos
    (fun a => inner ℂ (G.basis a.1) (Z (G.basis a.2)))
    (bounded_matrix_summable G.basis G.probability G.probability_pos
      G.probability_sum.summable t ht Z)

end EntropyPhotonNumber.GibbsData

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ}

end Annihilation

namespace EntropyPhotonNumber
open Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

def numberMatrixUnit (a b : NumberIndex n) : Fock n →L[ℂ] Fock n :=
  InnerProductSpace.rankOne ℂ (numberKet a) (numberKet b)

@[simp] theorem numberKet_inner (a : NumberIndex n) (x : Fock n) :
    inner ℂ (numberKet a) x=x a := by
  simp only [numberKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

@[simp] theorem inner_numberKet (a : NumberIndex n) (x : Fock n) :
    inner ℂ x (numberKet a)=conj (x a) := by
  rw [← inner_conj_symm, numberKet_inner]

@[simp] theorem numberMatrixUnit_inner (u v : Fock n) (a b : NumberIndex n) :
    inner ℂ v (numberMatrixUnit a b u)=u b*conj (v a) := by
  simp only [numberMatrixUnit, InnerProductSpace.rankOne_apply, inner_smul_right,
    numberKet_inner, inner_numberKet]
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open Annihilation WeightedGenerator
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

end

end OAI


