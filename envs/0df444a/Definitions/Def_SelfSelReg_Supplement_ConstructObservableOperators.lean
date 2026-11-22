-- Prove2me | Definitions.Def_SelfSelReg_Supplement_ConstructObservableOperators
-- name    : SelfSelReg_Supplement_ConstructObservableOperators
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:16:35.014899+00:00
-- url     : https://prove2.me/theorems/3cc199a7-7e1b-4672-abc8-9089cb66eb7c
-- title:
--   Algorithm 6.2 (CONSTRUCTOBSERVABLEOPERATORS) as an input–output relation
-- statement:
--   Algorithm 6.2 takes symmetric matrices $\widehat A,\widehat M_1,\dots,\widehat M_n\in\mathbb R^{p\times p}$ and returns a dimension $i_\star$ and matrices $\widehat D_1,\dots,\widehat D_n\in\mathbb R^{i_\star\times i_\star}$:
--
--   1. compute the eigenvalues $\widehat\lambda_1\ge\dots\ge\widehat\lambda_p$ and corresponding orthonormal eigenvectors $\widehat v_1,\dots,\widehat v_p$ of $\widehat A$;
--   2. replace $\widehat\lambda_h$ by $\max\{\widehat\lambda_h,0\}$ for $h\in[p]$ and put $\widehat\lambda_{p+1}=0$;
--   3. let $i_\star\in\arg\max_{1\le h\le p}(\widehat\lambda_h-\widehat\lambda_{h+1})$;
--   4. with $\widehat V$ the $i_\star\times p$ matrix of rows $\widehat v_1^\top,\dots,\widehat v_{i_\star}^\top$ and $\widehat\Lambda=\operatorname{diag}(\widehat\lambda_1,\dots,\widehat\lambda_{i_\star})$, return
--   $$
--   \widehat D_\ell=\widehat\Lambda^{-1/2}\,\widehat V\,\widehat M_\ell\,\widehat V^\top\,\widehat\Lambda^{-1/2}\qquad(\ell\in[n]).
--   $$
--
--   The definition is the relation "$(i_\star,\widehat D_1,\dots,\widehat D_n)$ is an output of the routine on $(\widehat A,\widehat M_1,\dots,\widehat M_n)$": there are an eigendecomposition of $\widehat A$ and an index $1\le i_\star\le p$ maximizing the clipped consecutive gap for which the displayed formula holds entrywise, $(\widehat D_\ell)_{ab}=\widehat\lambda_a^{-1/2}\,(\widehat v_a^\top\widehat M_\ell\widehat v_b)\,\widehat\lambda_b^{-1/2}$.
--
--   Theorem 6.5 is a statement about every output of this relation, hence about every way of choosing the eigenvectors and of breaking ties.
--
--   **Formalization Note** The routine is a relation and not a function because step 1 does not fix the eigenvectors and step 3 does not fix the maximizer. The factor $\widehat\lambda^{-1/2}$ is $(\sqrt{\widehat\lambda})^{-1}$, which Lean evaluates to $0$ at $\widehat\lambda=0$; the paper divides only after proving $\widehat\lambda_{i_\star}>0$.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Algorithm 6.2, p.39 (PDF p.42)

import Mathlib
import Definitions.Def_SelfSelReg_Supplement_EigDecomp

namespace SelfSelReg

namespace Supplement

/-- The clipped eigenvalue `λ̂_h ← max{λ̂_h, 0}` for `h ∈ [p]`, indexed from `1`, with `λ̂_h = 0` for
`h = 0` and `h > p` (Algorithm 6.2, line 2: "and λ̂_{p_s+1} ← 0"). -/
noncomputable def clipEig {p : ℕ} (vals : Fin p → ℝ) (h : ℕ) : ℝ :=
  if hh : 1 ≤ h ∧ h ≤ p then max (vals ⟨h - 1, by omega⟩) 0 else 0

/-- **Algorithm 6.2** (CONSTRUCTOBSERVABLEOPERATORS) as an input–output relation.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Algorithm 6.2, p.39 (PDF p.42): "Input: Symmetric matrices
Â, M̂_1, …, M̂_n ∈ ℝ^{p_s×p_s}. Output: A dimension i⋆ and matrices D̂_1, …, D̂_n.
1 Compute the eigenvalues λ̂_1 ≥ ⋯ ≥ λ̂_{p_s} and corresponding orthonormal eigenvectors v̂_1, …, v̂_{p_s}
of Â; 2 λ̂_h ← max{λ̂_h, 0} for h ∈ [p_s], and λ̂_{p_s+1} ← 0; 3 i⋆ ← arg max_{1≤h≤p_s}(λ̂_h − λ̂_{h+1});
4 V̂ ← [v̂_1ᵀ; …; v̂_{i⋆}ᵀ]; 5 Λ̂ ← diag(λ̂_1, …, λ̂_{i⋆}); 6 for ℓ = 1, …, n do
7 D̂_ℓ ← Λ̂^{−1/2} V̂ M̂_ℓ V̂ᵀ Λ̂^{−1/2}; 8 return (i⋆, D̂_1, …, D̂_n)."

`IsConstructOutput A M iStar D` says that `(iStar, D)` is an output of the routine on `(A, M)`:
for some eigendecomposition `(vals, V)` of `A` (line 1), `1 ≤ iStar ≤ p` maximizes the clipped
consecutive gap (lines 2–3), and entry `(a, b)` of `D_ℓ` is
`λ̂_a^{−1/2} · (v̂_aᵀ M_ℓ v̂_b) · λ̂_b^{−1/2}` (lines 4–7).

**Formalization Note.** The routine is a relation because line 1 does not fix the eigenvectors and
line 3 does not fix the maximizer among ties; a statement about every output covers every choice.
`λ̂^{−1/2}` is `(√λ̂)⁻¹`, which Lean evaluates to `0` when `λ̂ = 0`; the paper divides only after
proving `λ̂_{i⋆} > 0` ((70), p.42). -/
def IsConstructOutput {n p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (M : Fin n → Matrix (Fin p) (Fin p) ℝ) (iStar : ℕ)
    (D : Fin n → Matrix (Fin iStar) (Fin iStar) ℝ) : Prop :=
  ∃ (vals : Fin p → ℝ) (V : Matrix (Fin p) (Fin p) ℝ), IsEigDecomp A vals V ∧
    1 ≤ iStar ∧ ∃ hi : iStar ≤ p,
      (∀ h : ℕ, 1 ≤ h → h ≤ p →
        clipEig vals h - clipEig vals (h + 1) ≤ clipEig vals iStar - clipEig vals (iStar + 1)) ∧
      ∀ (l : Fin n) (a b : Fin iStar),
        D l a b = (Real.sqrt (clipEig vals (a + 1)))⁻¹ *
          (V * M l * V.transpose) (Fin.castLE hi a) (Fin.castLE hi b) *
          (Real.sqrt (clipEig vals (b + 1)))⁻¹

end Supplement

end SelfSelReg


