-- Prove2me | Definitions.Def_TriFormQ_TriForm
-- name    : TriFormQ_TriForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:06.179424+00:00
-- url     : https://prove2.me/theorems/9da20f92-ba43-4319-88d6-39f5efe6459b
-- title:
--   Trilinear form on $\mathbb F_q^n$ (coefficient tensor)
-- statement:
--   Let $\mathbb F$ be a field and $n\ge 0$. A **trilinear form** on $\mathbb F^n\times\mathbb F^n\times\mathbb F^n$ is determined by its **coefficient tensor** $\theta=(\theta_{ijk})_{i,j,k\in[n]}$:
--
--   $$f(u,v,w)=\sum_{i,j,k\in[n]}\theta_{ijk}\,u_i v_j w_k .$$
--
--   This module fixes the representation: a trilinear form is its coefficient tensor $\theta:[n]^3\to\mathbb F$, and $\mathbb F^n$ is the coordinate space $\mathrm{Vec}\,\mathbb F\,n=[n]\to\mathbb F$. Every object of the mission (oracles, slices, analytic rank) is stated in terms of these tensors.
--
--   **Formalization Note** `TriForm F n` is an abbreviation of `Fin n → Fin n → Fin n → F`, so the sum and difference of two forms (such as $f-T^i$) are taken coefficientwise. The paper's spaces $U,V,W$ are all $\mathbb F_q^n$, as in its main theorem.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §1, p.2 (PDF p.5); Corollary 5, p.12 (PDF p.15)

import Mathlib

namespace TriFormQ

/-- The coordinate space `𝔽_q^n` of the paper (Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum
Query Bounds for Identifying Classes of 3-Tensors*, STOC 2027 submission, manuscript sha256
c56b0365…, §1, p.2, PDF p.5). -/
abbrev Vec (F : Type) (n : ℕ) := Fin n → F

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §1, p.2 (PDF p.5): "an unknown
trilinear form f : U × V × W, f(u, v, w) = Σ_{i,j,k∈[n]} θ_{ijk} u_i v_j w_k"; Corollary 5,
p.12 (PDF p.15); §2.2, p.12: "Similarly relation holds between trilinear forms and 3-tensors".

**Formalization Note.** A trilinear form on `𝔽ⁿ × 𝔽ⁿ × 𝔽ⁿ` is represented by its coefficient
tensor `θ : Fin n → Fin n → Fin n → F`; every trilinear form on the coordinate spaces has exactly
one. `TriForm` is an `abbrev`, so sums and differences of forms (`f − Tⁱ`) are pointwise on
coefficients. The paper's U, V, W are taken to be the whole coordinate space `𝔽ⁿ`, as in
Theorem 1 ("trilinear forms on an n-dimensional vector space"). -/
abbrev TriForm (F : Type) (n : ℕ) := Fin n → Fin n → Fin n → F

end TriFormQ


