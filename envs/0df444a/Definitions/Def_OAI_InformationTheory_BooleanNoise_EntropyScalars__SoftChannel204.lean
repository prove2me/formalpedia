-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:51:55.126504+00:00
-- url     : https://prove2.me/theorems/be275c8a-f35f-4251-ae67-0009b13aebf2
-- title:
--   Basic properties of the sign entropy and of $\psi$
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$ and $h(v)=\log2-\psi(v)$. The following properties hold.
--
--   1. $\psi(0)=0$, $\psi(\pm1)=\log2$ and $\psi(-v)=\psi(v)$. Correspondingly, $h(0)=\log2$, $h(\pm1)=0$ and $h(-v)=h(v)$.
--   2. $h(v)=H_{\mathrm{nat}}\bigl(\tfrac{1+v}{2}\bigr)$, where $H_{\mathrm{nat}}(p)=-p\log p-(1-p)\log(1-p)$ is the binary entropy in nats.
--   3. $h$ and $\psi$ are continuous on $\mathbb{R}$, and $\psi$ is strictly increasing on $[0,1]$.
--
--   $h(v)$ is the entropy of a $\pm1$-valued variable with mean $v$. Strict monotonicity of $\psi$ on $[0,1]$ is what allows inverting it.
--
--   **Formalization Note** At $|v|=1$ the formulas use $\log0=0$. The identification uses Mathlib's `Real.binEntropy`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/EntropyScalars.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/EntropyScalars.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SoftChannel204 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

@[simp] theorem psi_zero : psi 0 = 0 := by norm_num [psi]
@[simp] theorem psi_one : psi 1 = ell := by norm_num [psi, ell]

@[simp] theorem psi_neg (v : ℝ) : psi (-v) = psi v := by
  simp only [psi, sub_eq_add_neg, neg_neg]
  ring

@[simp] theorem psi_neg_one : psi (-1) = ell := by rw [psi_neg, psi_one]

@[simp] theorem entropy_zero : entropy 0 = ell := by simp [entropy]
@[simp] theorem entropy_one : entropy 1 = 0 := by simp [entropy]
@[simp] theorem entropy_neg (v : ℝ) : entropy (-v) = entropy v := by simp [entropy]
@[simp] theorem entropy_neg_one : entropy (-1) = 0 := by simp

theorem entropy_eq_binEntropy (v : ℝ) :
    entropy v = Real.binEntropy ((1 + v) / 2) := by
  have hs (t : ℝ) : Real.negMulLog (t / 2) =
      -(t / 2) * Real.log t + (t / 2) * ell := by
    calc
      _ = (2 : ℝ)⁻¹ * Real.negMulLog t + t * Real.negMulLog ((2 : ℝ)⁻¹) := by
        simpa [div_eq_mul_inv] using Real.negMulLog_mul t ((2 : ℝ)⁻¹)
      _ = _ := by simp [Real.negMulLog, ell, Real.log_inv]; ring
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [show 1 - (1 + v) / 2 = (1 - v) / 2 by ring, hs, hs]
  unfold entropy psi
  ring

theorem continuous_entropy : Continuous entropy := by
  have h : entropy = fun v => Real.binEntropy ((1 + v) / 2) :=
    funext entropy_eq_binEntropy
  rw [h]
  fun_prop

theorem continuous_psi : Continuous psi := by
  have h : psi = fun v => ell - entropy v := by ext v; simp [entropy]
  rw [h]
  exact continuous_const.sub continuous_entropy

theorem strictMonoOn_psi : StrictMonoOn psi (Icc 0 1) := by
  intro x hx y hy hxy
  have h := Real.binEntropy_strictAntiOn
    (show (1 + x) / 2 ∈ Icc ((2 : ℝ)⁻¹) 1 by constructor <;> linarith [hx.1, hx.2])
    (show (1 + y) / 2 ∈ Icc ((2 : ℝ)⁻¹) 1 by constructor <;> linarith [hy.1, hy.2])
    (show (1 + x) / 2 < (1 + y) / 2 by linarith)
  rw [← entropy_eq_binEntropy, ← entropy_eq_binEntropy] at h
  unfold entropy at h
  linarith

end LeanBlast.CourtadeKumar

end

end OAI


