-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
-- name    : OAI_InformationTheory_BooleanNoise_InverseScalars
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:19:47.547963+00:00
-- url     : https://prove2.me/theorems/fcd74d19-0f16-4f18-8e36-4d2f57b563ed
-- title:
--   The inverse of $\psi$ and the auxiliary functions $r$, $L$ and $K$
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$, a strictly increasing bijection $[0,1]\to[0,\log2]$.
--
--   1. **Inverse.** $\psi^{-1}:[0,\log2]\to[0,1]$, with $\psi^{-1}(0)=0$ and $\psi^{-1}(\log2)=1$. Together these give an order isomorphism.
--   2. **The function $r$ and its derivatives.** $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$, and $r(s)-2s$. With $w=\psi^{-1}(s)$, for $s>0$ the explicit expressions
--   $$
--   r'(s)=1+\frac{w}{(1-w^2)\operatorname{artanh}w},\qquad r''(s)=\frac{(1+w^2)\operatorname{artanh}w-w}{(1-w^2)^2(\operatorname{artanh}w)^3},
--   $$
--   with the limiting values $2$ and $\frac43$ for $s\le0$.
--   3. **The gap function $L$ on $(0,\log2)$.** $L(x)=r(\log2-x)-2(\log2-x)$ and $L'(x)=2-r'(\log2-x)$ for $0<x<\log2$, and $0$ otherwise.
--   4. **The modified function $K$.** With $s_0=\psi(1/5)$, $K(s)=r(s)-2s$ for $0<s\le s_0$, extended linearly with slope $r'(s_0)-2$ for $s>s_0$, and $K(s)=0$ for $s\le0$. Its derivative is defined accordingly.
--
--   $r$ expresses the dissipation in terms of the entropy. Concavity-type properties of $L$ and $K$ drive the inductive proof of the information inequality.
--
--   **Formalization Note** $\psi^{-1}$ is `Function.invFunOn psi (Icc 0 1)`. The derivative formulas are definitions; that they are derivatives is proved elsewhere.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/InverseScalars.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/InverseScalars.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def psiInv (s : ℝ) : ℝ := Function.invFunOn psi (Set.Icc 0 1) s

def r (s : ℝ) : ℝ := psiInv s * Real.artanh (psiInv s)

def rDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 2 else
    1 + psiInv s / ((1 - (psiInv s) ^ 2) * Real.artanh (psiInv s))

def rSecondDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 4 / 3 else
    (((1 + (psiInv s) ^ 2) * Real.artanh (psiInv s) - psiInv s) /
      ((1 - (psiInv s) ^ 2) ^ 2 * (Real.artanh (psiInv s)) ^ 3))

def rGap (s : ℝ) : ℝ := r s - 2 * s

def L (x : ℝ) : ℝ :=
  if 0 < x ∧ x < ell then rGap (ell - x) else 0

def LDeriv (x : ℝ) : ℝ :=
  if 0 < x ∧ x < ell then 2 - rDeriv (ell - x) else 0

def s0 : ℝ := psi (1 / 5)

def K (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else
    if s ≤ s0 then rGap s else rGap s0 + (rDeriv s0 - 2) * (s - s0)

def KDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else
    if s ≤ s0 then rDeriv s - 2 else rDeriv s0 - 2

theorem psiInv_mem_of_mem_image {s : ℝ} (hs : s ∈ psi '' Set.Icc 0 1) :
    psiInv s ∈ Set.Icc 0 1 :=
  Function.invFunOn_mem hs

theorem psi_psiInv_of_mem_image {s : ℝ} (hs : s ∈ psi '' Set.Icc 0 1) :
    psi (psiInv s) = s :=
  Function.invFunOn_eq hs

@[simp] theorem rDeriv_zero : rDeriv 0 = 2 := by simp [rDeriv]
@[simp] theorem rSecondDeriv_zero : rSecondDeriv 0 = 4 / 3 := by simp [rSecondDeriv]
@[simp] theorem K_zero : K 0 = 0 := by simp [K]
@[simp] theorem KDeriv_zero : KDeriv 0 = 0 := by simp [KDeriv]

theorem image_psi_Icc : psi '' Icc 0 1 = Icc 0 ell := by
  simpa only [psi_zero, psi_one] using
    continuous_psi.continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) strictMonoOn_psi.monotoneOn

theorem psiInv_mem_Icc {s : ℝ} (hs : s ∈ Icc 0 ell) : psiInv s ∈ Icc 0 1 := by
  exact psiInv_mem_of_mem_image (image_psi_Icc.symm ▸ hs)

theorem psi_psiInv_Icc {s : ℝ} (hs : s ∈ Icc 0 ell) : psi (psiInv s) = s := by
  exact psi_psiInv_of_mem_image (image_psi_Icc.symm ▸ hs)

theorem psiInv_psi {u : ℝ} (hu : u ∈ Icc 0 1) : psiInv (psi u) = u :=
  strictMonoOn_psi.injOn.leftInvOn_invFunOn hu

@[simp] theorem psiInv_zero : psiInv 0 = 0 := by
  simpa only [psi_zero] using psiInv_psi (show (0 : ℝ) ∈ Icc 0 1 by norm_num)

@[simp] theorem psiInv_ell : psiInv ell = 1 := by
  simpa only [psi_one] using psiInv_psi (show (1 : ℝ) ∈ Icc 0 1 by norm_num)

@[simp] theorem r_zero : r 0 = 0 := by simp [r]
@[simp] theorem rGap_zero : rGap 0 = 0 := by simp [rGap]

def psiOrderIso : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) ell where
  toFun u := ⟨psi u, image_psi_Icc ▸ mem_image_of_mem psi u.property⟩
  invFun s := ⟨psiInv s, psiInv_mem_Icc s.property⟩
  left_inv u := Subtype.ext (psiInv_psi u.property)
  right_inv s := Subtype.ext (psi_psiInv_Icc s.property)
  map_rel_iff' := by
    intro u v
    exact strictMonoOn_psi.le_iff_le u.property v.property

end LeanBlast.CourtadeKumar

end

end OAI


