-- Prove2me | Definitions.Def_BosonicLearn_PhiMap
-- name    : BosonicLearn_PhiMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:26:22.938631+00:00
-- url     : https://prove2.me/theorems/f512fd9d-1420-44fb-8301-120d25faca9d
-- title:
--   The relative parametrization $\Phi_{X_0}$
-- statement:
--   For $X_0\in\mathrm{Herm}_0(n)$ and $\xi>0$, $\Phi_{X_0}$ is defined on $\{Z\in\mathrm{Herm}_0(n):1+\xi^2\operatorname{Tr}(X_0Z)/n>0\}$ by
--
--   $$I+\xi\,\Phi_{X_0}(Z)=\frac{(I+\xi X_0)^{1/2}(I+\xi Z)(I+\xi X_0)^{1/2}}{1+\xi^2\operatorname{Tr}(X_0Z)/n}.$$
--
--   It satisfies $\Phi_{X_0}(0)=X_0$ and parametrizes a neighbourhood of $X_0$ by relative (multiplicative) perturbations of $R_{X_0}$.
--
--   **Formalization Note** The square root is the continuous functional calculus. When $I+\xi X_0\succeq0$ and the denominator is nonzero, the right-hand side minus $I$, divided by $\xi$, is Hermitian and traceless and is the value; on all other inputs (outside the paper's domain) the value is $0$. On the inputs of Lemma 8 ($\|X_0\|_{\mathrm{op}}\le3$, $\xi<1/32$, $\|Z\|_{\mathrm{op}}\le0.1$) the formula is used, also on a neighbourhood.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.2, Eq. (34), p. 31

import Mathlib
import Definitions.Def_BosonicLearn_Herm0

open scoped MatrixOrder

namespace BosonicLearn

/-- **The relative parametrization `Φ_{X₀}`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.2, Eq. (34), p. 31: "Φ_{X_0} : {Z ∈ Herm_0(n) : 1 + ξ² Tr(X_0 Z)/n > 0} → Herm_0(n), s.t.
I + ξΦ_{X_0}(Z) = (I + ξX_0)^{1/2}(I + ξZ)(I + ξX_0)^{1/2} / (1 + ξ² Tr(X_0 Z)/n)."

`PhiMap X₀ ξ Z = ξ^{-1}(d_Z^{-1} S^{1/2}(I + ξZ)S^{1/2} − I)` with `S = I + ξX₀` and
`d_Z = 1 + ξ² Tr(X₀Z)/n`.

**Formalization Note.** `S^{1/2}` is `CFC.sqrt`. Whenever `S ⪰ 0` and `d_Z ≠ 0` (in particular on the paper's
domain with `ξ‖X₀‖_op < 1`) the matrix is Hermitian and traceless, so it is returned as an element of
`Herm₀(n)`; on any other input the value is `0`, a junk value outside the paper's domain. In Lemma 8 the
inputs satisfy `‖X₀‖_op ≤ 3`, `ξ < 1/32`, `‖Z‖_op ≤ 0.1`, where the junk branch is never taken, also on a
neighbourhood, so derivatives are those of the formula. -/
noncomputable def PhiMap {n : ℕ} (X₀ : Herm0 n) (ξ : ℝ) (Z : Herm0 n) : Herm0 n :=
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X₀ : Matrix (Fin n) (Fin n) ℂ)
  let d : ℂ := 1 + (ξ : ℂ) ^ 2 * ((X₀ : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let M : Matrix (Fin n) (Fin n) ℂ := (ξ⁻¹ : ℂ) •
    (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)
  @dite _ (M ∈ Herm0 n) (Classical.propDecidable _) (fun h => ⟨M, h⟩) (fun _ => 0)

end BosonicLearn


