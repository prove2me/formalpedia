-- Prove2me | Definitions.Def_PWDB_StrictSlaterDB
-- name    : PWDB_StrictSlaterDB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:58.53109+00:00
-- url     : https://prove2.me/theorems/d42df95e-7c4c-410d-80ea-c8f72838eec8
-- title:
--   Strict Slater point of the dual best problem (D-B)
-- statement:
--   A point $(w_0, z_0, \{w_i, z_i\}_{i\in I}, \lambda)$ is a **strict Slater point of (D-B)** if
--
--   1. $w_0 + \sum_i w_i = 0$ and $\lambda_i > 0$ for all $i \in I$;
--   2. $c_\ell(z_i) < 0$ and $z_i \in \operatorname{ri}(\operatorname{dom} c_\ell)$ for all $\ell \in L$ and $i \in I_0$;
--   3. $(w_0, z_0) \in \operatorname{ri}(\operatorname{dom} f_0^{*1})$ and $(w_i/\lambda_i, z_i) \in \operatorname{ri}(\operatorname{dom} f_i^{*1})$ for all $i \in I$.
--
--   This is Definition 2 for (D-B) with the relative interior of the objective's domain read through the domains of the partial conjugates. The literal condition implies this one. The literal domain can be a nonconvex set with empty relative interior (for $f_0 = x$, $f_1 = zx - 1$, $Z = \mathbb R$), which would make Theorem 7 (iii) vacuous there; the proof of Theorem 7 (iii), p.55, uses exactly conditions 1–3.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Definition 2, p.7, applied to (D-B), p.10; used in Proposition 5 (ii), p.12, Theorem 7 (iii), p.13, proof p.55

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PWDB_PartialConj

namespace PWDB

/-- **Strict Slater point of the dual best problem (D-B)** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, Definition 2 for a maximization problem, p.7, applied to (D-B), p.10; used in
Proposition 5 (ii), p.12, and Theorem 7 (iii), p.13).

`StrictSlaterDB c f₀ f p` at `p = (w₀, z₀, w, z, λ)` says:
1. `w₀ + Σ_i wi = 0`;
2. `λi > 0` for every `i ∈ I` (the constraints `−λi ≤ 0` hold strictly);
3. `cℓ(z₀) < 0` and `z₀ ∈ ri(dom cℓ)` for every `ℓ ∈ L`, and the same for every `zi`, `i ∈ I`
   (the constraints `zi ∈ Z` hold strictly, inside the relative interiors of their domains);
4. `(w₀, z₀) ∈ ri(dom f0∗1)` and `(wi/λi, zi) ∈ ri(dom fi∗1)` for every `i ∈ I`.

**Formalization Note** This is a reading of Definition 2 for (D-B). Condition 4 replaces the
literal `ri(dom(−objective))`, taken in the variables `(w, z, λ)`, by the relative interiors of the
domains of the partial conjugates. The literal condition implies condition 4 (the domain of the
(D-B) objective is a product over the indices, and its slice at fixed `λi > 0` is the image of
`dom fi∗1` under `(w, z) ↦ (λi w, z)`). The literal set is in general nonconvex and can have empty
relative interior: for `f0(x, z) = x`, `f1(x, z) = zx − 1` and `Z = ℝ` it contains four affinely
independent points of `ℝ³` and has empty interior, so the literal reading would make Theorem 7 (iii)
vacuous there although its conclusion holds. The paper's own use of the notion (proof of Theorem 7,
p.55) needs exactly conditions 1–4: they make `(w, z₀, λ, υ = λ z)` a strict Slater point of (D-B′)
and every `zi` a Slater point of `Z`. `ri` is `intrinsicInterior ℝ`, `dom` is
`AubinLipschitz.effDom`. -/
def StrictSlaterDB {E F ι L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ)
    (p : E × F × (ι → E) × (ι → F) × (ι → ℝ)) : Prop :=
  p.1 + ∑ i, p.2.2.1 i = 0 ∧
  (∀ i, 0 < p.2.2.2.2 i) ∧
  (∀ ℓ, c ℓ p.2.1 < 0 ∧ p.2.1 ∈ intrinsicInterior ℝ (AubinLipschitz.effDom (c ℓ))) ∧
  (∀ i ℓ, c ℓ (p.2.2.2.1 i) < 0 ∧
    p.2.2.2.1 i ∈ intrinsicInterior ℝ (AubinLipschitz.effDom (c ℓ))) ∧
  (p.1, p.2.1) ∈ intrinsicInterior ℝ
    (AubinLipschitz.effDom (fun q : E × F => pconj1 (fun x z => ((f₀ x z : ℝ) : EReal)) q.1 q.2)) ∧
  ∀ i, ((p.2.2.2.2 i)⁻¹ • p.2.2.1 i, p.2.2.2.1 i) ∈ intrinsicInterior ℝ
    (AubinLipschitz.effDom (fun q : E × F => pconj1 (fun x z => ((f i x z : ℝ) : EReal)) q.1 q.2))

end PWDB


