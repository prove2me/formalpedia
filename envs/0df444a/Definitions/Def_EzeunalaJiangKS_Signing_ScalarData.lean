-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_ScalarData
-- name    : EzeunalaJiangKS_Signing_ScalarData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:05:20.245975+00:00
-- url     : https://prove2.me/theorems/920d8c85-93ff-4edc-970a-657aa00e8733
-- title:
--   Light states, contractions, and rescaled scalar quantities
-- statement:
--   At the chosen primal and dual matrices let $a_i=\operatorname{ReTr}(A_iX)$, $b_i=\operatorname{ReTr}(A_iY)$, $p_i=\operatorname{ReTr}(A_iP)$ and $q_i=\operatorname{ReTr}(A_iQ)$. For $A_i=v_iv_i^*$ these are exactly the source's $v_i^*Zv_i$ and need no choice of a factor vector. A light state has an active coordinate and satisfies $40\psi_i a_i<1+x_i$ and $40\psi_i b_i<1-x_i$ on every active coordinate. Put $\alpha_i=1+40\psi_i'b_i$, $\beta_i=1-40\psi_i'a_i$ and
--   $$\chi_i=-\psi_i''-\tfrac43(\psi_i')^2/\psi_i,\quad\ell_i=\sqrt{\psi_i\alpha_i/\beta_i},\quad m_i=\sqrt{\psi_i\beta_i/\alpha_i},\quad T_i=\sqrt{\alpha_i\beta_i/\psi_i}.$$
--   The scaled quantities are $\widetilde a_i=\ell_i a_i$, $\widetilde b_i=m_i b_i$, $\widetilde p_i=\ell_i p_i$, $\widetilde q_i=m_i q_i$. Valid light states have positive denominators and square-root arguments, as consequences to prove rather than fields of the data. Zero divisions and square roots outside this domain have Lean's standard total values. These objects are shared by all three light-state lemmas.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §4.2, (13), (18), (20), (25), printed p. 16 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_Linearization
import Definitions.Def_EzeunalaJiangKS_Signing_FaceCalculus

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Rank-one contractions v*Zv = Re Tr(AZ), independent of the chosen factor of A=vv*. -/
def contraction {d : ℕ} (A Z : CMat d) : ℝ := tr (A * Z)

def scalarA {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  contraction (A i) (optimizer A x₀ x).2.1
def scalarB {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  contraction (A i) (optimizer A x₀ x).2.2
def scalarP {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  contraction (A i) (dual A x₀ x).1
def scalarQ {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  contraction (A i) (dual A x₀ x).2

def light {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) : Prop :=
  cube x ∧ 0 < activeCount x ∧ ∀ i ∈ active x,
    couplingConstant * psi (x i) * scalarA A x₀ x i < 1 + x i ∧
    couplingConstant * psi (x i) * scalarB A x₀ x i < 1 - x i

def alpha {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  1 + couplingConstant * psiPrime (x i) * scalarB A x₀ x i
def beta {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  1 - couplingConstant * psiPrime (x i) * scalarA A x₀ x i

def chi (u : ℝ) : ℝ := -psiSecond u - (4 / 3 : ℝ) * (psiPrime u)^2 / psi u

def ell {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  Real.sqrt (psi (x i) * alpha A x₀ x i / beta A x₀ x i)
def emm {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  Real.sqrt (psi (x i) * beta A x₀ x i / alpha A x₀ x i)
def coordinateScale {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  Real.sqrt (alpha A x₀ x i * beta A x₀ x i / psi (x i))

def scaledA {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  ell A x₀ x i * scalarA A x₀ x i
def scaledB {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  emm A x₀ x i * scalarB A x₀ x i
def scaledP {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  ell A x₀ x i * scalarP A x₀ x i
def scaledQ {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (i : Fin N) : ℝ :=
  emm A x₀ x i * scalarQ A x₀ x i

end EzeunalaJiangKS.Signing


