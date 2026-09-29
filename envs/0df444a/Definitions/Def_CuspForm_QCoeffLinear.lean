-- Prove2me | Definitions.Def_CuspForm_QCoeffLinear
-- name    : CuspForm_QCoeffLinear
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/db1d2ede-322b-548a-9dc4-527a83aa67ae
-- title:
--   Linearity of q-expansion coefficients on Sk​(Γ0​(M))
-- statement:
--   Two declarations about Fourier coefficients of cusp forms for $\Gamma_0(M)$, taken with respect to the parameter $q = e^{2\pi i \tau}$ of width $1$. The underlying coefficient function is the project notion [`ModularFormClass.qCoeff`](../def/FLTPrelim_Modularity.html#L19), which assigns to a bare function $f \colon \mathbb{H} \to \mathbb{C}$ and an index $n \in \mathbb{N}$ the $n$-th coefficient of `UpperHalfPlane.qExpansion 1 f`, i.e. of the power series in $q$ attached to the associated cusp function at width $1$.
--
--   First, [`CuspForm.analyticAt_cuspFunction_one_gamma0`](../def/CuspForm_QCoeffLinear.html#L10): for any $M \in \mathbb{N}$, any weight $k \in \mathbb{Z}$ and any cusp form $f$ of weight $k$ for $\Gamma_0(M)$, the cusp function of $f$ at width $1$ is analytic at the point $0$ of the $q$-disc. This is obtained from Mathlib's analyticity statement for cusp functions together with the fact that $1$ lies in the strict periods of $\Gamma_0(M)$; no positivity or divisibility condition on $M$, and no condition on $k$, is imposed.
--
--   Second, [`CuspForm.qCoeffLinear M k n`](../def/CuspForm_QCoeffLinear.html#L15), for $M, n \in \mathbb{N}$ and $k \in \mathbb{Z}$: the $\mathbb{C}$-linear map
--   $$S_k(\Gamma_0(M)) \longrightarrow \mathbb{C}, \qquad f \longmapsto \mathrm{qCoeff}(f, n),$$
--   from the space of cusp forms of weight $k$ for $\Gamma_0(M)$ to $\mathbb{C}$, whose underlying function sends $f$ to the $n$-th $q$-expansion coefficient of the function underlying $f$. Because `qCoeff` is defined on bare functions on $\mathbb{H}$, additivity and $\mathbb{C}$-homogeneity are not formal consequences of the definition: they rest on the compatibility of `UpperHalfPlane.qExpansion` with sums and scalar multiples, whose analyticity hypotheses are furnished by the first declaration.
--
--   **Relation to Mathlib.** Built on Mathlib's `UpperHalfPlane.qExpansion` and its additivity and scalar-multiplication lemmas; the coefficient function [`ModularFormClass.qCoeff`](../def/FLTPrelim_Modularity.html#L19) is the project's width-$1$ wrapper around it, and the packaging of $f \mapsto a_n(f)$ as a `ℂ`-linear map on `CuspForm (CongruenceSubgroup.Gamma0 M) k` is the project's own.
--
--   **Where it is used.** The coefficient functionals $a_n$ are the data through which modularity is expressed in this development: the project's predicate [`CuspForm.IsNormalizedEigenform`](../def/FLTPrelim_Modularity.html#L28) is a conjunction of Hecke-type recursions among the numbers $\mathrm{qCoeff}(f,n)$, and [`WeierstrassCurve.IsModularModelOfLevel`](../def/FLTPrelim_Modularity.html#L93) matches $\mathrm{qCoeff}(f,p)$ with the trace of Frobenius of a reduction. Linearity in $f$ is what allows these coefficients to be used as linear functionals, for instance when expanding a cusp form in a basis or comparing forms through their coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_QCoeffLinear.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane

namespace CuspForm

theorem analyticAt_cuspFunction_one_gamma0 {M : ℕ} {k : ℤ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) : AnalyticAt ℂ (cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _)

noncomputable def qCoeffLinear (M : ℕ) (k : ℤ) (n : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 M) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := by
    show ModularFormClass.qCoeff (⇑(f + g)) n =
      ModularFormClass.qCoeff (⇑f) n + ModularFormClass.qCoeff (⇑g) n
    unfold ModularFormClass.qCoeff
    rw [CuspForm.coe_add, UpperHalfPlane.qExpansion_add (analyticAt_cuspFunction_one_gamma0 f)
      (analyticAt_cuspFunction_one_gamma0 g), map_add]
  map_smul' c f := by
    show ModularFormClass.qCoeff (⇑(c • f)) n = c • ModularFormClass.qCoeff (⇑f) n
    unfold ModularFormClass.qCoeff
    rw [show (⇑(c • f) : ℍ → ℂ) = c • (⇑f) from by ext z; rfl,
      UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_one_gamma0 f), map_smul]

end CuspForm


