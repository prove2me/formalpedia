-- Prove2me | Definitions.Def_QSDMixing_GU_pgmSuccess
-- name    : QSDMixing_GU_pgmSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:45.700071+00:00
-- url     : https://prove2.me/theorems/c31adf94-180a-45ba-8393-a3fbe0c65678
-- title:
--   Success probability of the pretty good measurement, uniform pure ensemble
-- statement:
--   For the uniform ensemble of pure states $v_i$, $i\in I$, $|I|=n$, set $\bar\rho=\frac1n\sum_i|v_i\rangle\langle v_i|$ and $R=\bar\rho^{-1/2}$. The pretty good measurement has elements $\Pi_i=R\,\frac1n|v_i\rangle\langle v_i|\,R$, and its success probability is
--
--   $$
--   p_{\mathrm{PGM}}=\frac1n\sum_i\mathrm{tr}(\Pi_i|v_i\rangle\langle v_i|)=\frac1n\sum_i\frac1n\,|\langle v_i,Rv_i\rangle|^2.
--   $$
--
--   **Formalization Note** $\bar\rho$ is positive of finite rank, so its spectrum is a finite subset of $[0,\infty)$ and the continuous functional calculus applies to $z\mapsto(\sqrt{\mathrm{Re}\,z})^{-1}$. Since $(\sqrt0)^{-1}=0$ in Lean, $R$ is the pseudo-inverse. The calculus used is the complex one on normal elements, which agrees with the real one on a self-adjoint operator.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (5), p.4

import Mathlib
import Definitions.Def_GaussTesting_Ell2

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- The success probability of the pretty good measurement for the uniform ensemble of pure states
`v_i`: with `ρ̄ = (1/|I|) Σ_i |v_i⟩⟨v_i|` and `R = ρ̄^{-1/2}`,
`p_PGM = (1/|I|) Σ_i tr(Π_i |v_i⟩⟨v_i|) = (1/|I|) Σ_i (1/|I|) |⟨v_i, R v_i⟩|²`,
where `Π_i = R (1/|I|) |v_i⟩⟨v_i| R`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (5), p.4, with `p_i = 1/|I|` and `ρ_i = |v_i⟩⟨v_i|`.

**Formalization Note.** `ρ̄` is a positive operator of finite rank, so its spectrum is a finite subset of
`[0, ∞)`, the function `z ↦ (√(Re z))⁻¹` is continuous on it, and `cfc` is not junk. Since `(√0)⁻¹ = 0` in
Lean, `R` is the pseudo-inverse of `√ρ̄`, the standard meaning of `ρ̄^{-1/2}` for the PGM. The calculus is
Mathlib's complex one (normal elements), which agrees with the real one on a self-adjoint operator. -/
noncomputable def pgmSuccess {K I : Type} [Fintype I] (v : I → Ell2 K) : ℝ :=
  let n : ℝ := Fintype.card I
  let ρbar : Ell2 K →L[ℂ] Ell2 K :=
    ((1 / n : ℝ) : ℂ) • ∑ i, InnerProductSpace.rankOne ℂ (v i) (v i)
  let R : Ell2 K →L[ℂ] Ell2 K := cfc (fun z : ℂ => (((Real.sqrt z.re)⁻¹ : ℝ) : ℂ)) ρbar
  (1 / n) * ∑ i, (1 / n) * ‖(inner ℂ (v i) (R (v i)) : ℂ)‖ ^ 2

end QSDMixing.GU


