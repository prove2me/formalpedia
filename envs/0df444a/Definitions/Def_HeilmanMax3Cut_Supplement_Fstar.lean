-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_Fstar
-- name    : HeilmanMax3Cut_Supplement_Fstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:01:13.322624+00:00
-- url     : https://prove2.me/theorems/8bd7bbe8-ff44-4663-a19e-1a765944f1ab
-- title:
--   The optimal stability $F^*(k,\rho)$, Eq. (3)
-- statement:
--   For $k\ge1$ and $\rho\in(-1,1)$,
--
--   $$F^*(k,\rho)=\frac2k\left(\frac{\Gamma((k+1)/2)}{\Gamma(k/2)}\right)^2\rho\;{}_2F_1\!\left(\tfrac12,\tfrac12;\tfrac k2+1;\rho^2\right),$$
--
--   where ${}_2F_1$ is the Gauss hypergeometric function. By [HNP+23, Theorem 7.15] it is the noise stability of $f_{\mathrm{opt},k}(x)=(x_1,\dots,x_k)/(x_1^2+\cdots+x_k^2)^{1/2}$.
--
--   It is the right-hand side of the vector-valued Borell inequalities (4) and (5), and the numerator of the BOV ratio (6).
--
--   **Formalization Note** ${}_2F_1$ is Mathlib's `ordinaryHypergeometric`, which is $0$ outside its disc of convergence $|z|<1$; all uses have $|\rho|<1$. $F^*$ is the closed form, not defined as a noise stability.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (3), p.9

import Mathlib

namespace HeilmanMax3Cut.Supplement

/-- **The optimal stability `F*(k, ρ)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (3), p.9:
`F*(k, ρ) := (2/k) (Γ((k + 1)/2) / Γ(k/2))² ρ · ₂F₁(1/2, 1/2; k/2 + 1; ρ²)`, the noise stability of
`f_opt,k(x) = (x₁, …, x_k)/(x₁² + ⋯ + x_k²)^{1/2}` ([HNP+23, Theorem 7.15]).

**Formalization Note.** `Γ` is `Real.Gamma` and `₂F₁` is Mathlib's `ordinaryHypergeometric` over `ℝ`
(the Gauss series `∑ⱼ (a)ⱼ(b)ⱼ/((c)ⱼ j!) zʲ`), which returns `0` outside its disc of convergence
`|z| < 1`; every theorem of the mission evaluates `F*` at `|ρ| < 1`, inside the disc. `F*` is the
closed form (3), not `Stab_ρ(f_opt,k)`: the identity between the two is [HNP+23, Theorem 7.15]. -/
noncomputable def Fstar (k : ℕ) (ρ : ℝ) : ℝ :=
  (2 / (k : ℝ)) * (Real.Gamma (((k : ℝ) + 1) / 2) / Real.Gamma ((k : ℝ) / 2)) ^ 2 * ρ *
    ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2) ((k : ℝ) / 2 + 1) (ρ ^ 2)

end HeilmanMax3Cut.Supplement


