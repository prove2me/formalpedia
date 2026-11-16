-- Prove2me | Definitions.Def_DRSub4633_Supplement_concaveClosure
-- name    : DRSub4633_Supplement_concaveClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:34:21.965404+00:00
-- url     : https://prove2.me/theorems/176f9db2-fb95-4b5d-8257-a4b83695182c
-- title:
--   The concave closure $f^+$ on the cube, Eq. (135)
-- statement:
--   For $f:[0,1]^n\to\mathbb R$ continuous, its **concave closure** on the full cube is
--   $$f^+(x)=\sup\{\mathbb E f(O) : O\in[0,1]^n\text{ almost surely},\ \mathbb E O=x\}.$$
--   It compares $f$ at $x$ with all distributions of comparators that have mean $x$.
--
--   **Formalization Note** The supremum is taken over Borel probability measures $\mu$ on $\mathbb R^n$ concentrated on $[0,1]^n$ with mean $\int y\,d\mu(y)=x$, of $\int f\,d\mu$. Integrability of the identity and of $f$ under $\mu$ is part of the condition. Both hold automatically when $f$ is continuous on the cube. For $x$ in the cube the set contains $f(x)$ (the Dirac law) and is bounded above, so the real supremum is the paper's. Outside the cube the set is empty, and that case is never used.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Appendix B.1, Eq. (135), p.53

import Mathlib
import Definitions.Def_GeomDRSub_cube

namespace DRSub4633.Supplement

/-- **The concave closure `f⁺` on the cube, Eq. (135).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Appendix B.1, Eq. (135), p.53:
"For a continuous function `f : [0, 1]ⁿ → ℝ`, define its concave closure on the full cube by
`f⁺(x) = sup{E f(O) : O ∈ [0, 1]ⁿ almost surely, E O = x}`."

`concaveClosure f x` is the supremum of `∫ f dμ` over Borel probability measures `μ` on `ℝⁿ`
that are concentrated on `[0,1]ⁿ` and have mean `∫ y dμ(y) = x`.

**Formalization Note.** The law `μ` of `O` replaces the random vector. Integrability of the
identity and of `f` under `μ` is part of the defining condition; for `μ` concentrated on the
cube and `f` continuous on the cube both hold automatically, so the set is the paper's. For
`x ∈ [0,1]ⁿ` the set contains `∫ f dδₓ = f(x)` and is bounded above by `sup_Q f`, so the real
supremum is the paper's (for `x` outside the cube the set is empty and the value is `0`, a case
the paper does not use). -/
noncomputable def concaveClosure {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {r | ∃ μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)), MeasureTheory.IsProbabilityMeasure μ ∧
    μ (GeomDRSub.cube n)ᶜ = 0 ∧ MeasureTheory.Integrable (fun y => y) μ ∧
    MeasureTheory.Integrable f μ ∧ (∫ y, y ∂μ) = x ∧ r = ∫ y, f y ∂μ}

end DRSub4633.Supplement


