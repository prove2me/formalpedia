-- Prove2me | Definitions.Def_PrivateUniformGen_Characterization_Robust
-- name    : PrivateUniformGen_Characterization_Robust
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:57.282191+00:00
-- url     : https://prove2.me/theorems/f4745ffd-faa3-497e-9619-0a83b3e78fc4
-- title:
--   Robust closures and profile blocks
-- statement:
--   Let $c=\operatorname{CDim}(C)\ge0$, $h=h_{\mathrm{fin}}(C)$ and $m>c$ be a public integer, under the finite dimension assumptions of Section 5. Define
--
--   $$N(C,m)=\left\lceil\frac{m-c}{h}\right\rceil,\qquad R_t(S)=\{T\subseteq\widehat S:|T|=|\widehat S|-t,\ \exists L\in C,\ T\subseteq L\}.$$
--
--   For $0\le t<N(C,m)$, the robust closure is empty if $|\widehat S|-ht\le c$, the intersection of the closures of $T\in R_t(S)$ if the strict reverse inequality holds and $R_t(S)$ is nonempty, and $X$ otherwise. Subtraction is integer subtraction. The index range depends on public $m$, not on the dataset.
--
--   For a profile $\sigma$, the block length $\lambda_S(\sigma)$ counts indices with barred profile $\sigma$. When the block is nonempty, $\gamma_S(\sigma)$ is the barred iterated core of the robust closure at its least index; its unused empty-block value is $X$. Finite-value projections of dimensions are used only in the finite regime; the Helly number is finite there by Lemmas 4.7–4.8, not by an extra assumption.
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Definitions 5.9 and 5.13, pp. 14, 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Profiles
import Definitions.Def_PrivateUniformGen_Characterization_Helly

namespace PrivateUniformGen.Characterization

/-- Finite-value projections are used only under the section's finiteness assumptions. -/
noncomputable def cdimInt {X : Type*} (C : LanguageClass X) : ℤ :=
  (closureDim C).untopD 0

noncomputable def hellyNat {X : Type*} (C : LanguageClass X) : ℕ :=
  (hellyNumber C.languages).toNat

/-- Definition 5.9: a public range, independent of the dataset. -/
noncomputable def robustLength {X : Type*} (C : LanguageClass X) (m : ℕ) : ℕ :=
  ⌈((m : ℝ) - (cdimInt C : ℝ)) / (hellyNat C : ℝ)⌉₊

/-- R_t(S); cardinality subtraction takes place in the integers. -/
noncomputable def retained {X : Type*} (C : LanguageClass X) {n : ℕ}
    (S : Fin n → X) (t : ℕ) : Set (Finset X) :=
  {T | T ⊆ support S ∧ (T.card : ℤ) = (support S).card - (t : ℤ) ∧
    ∃ L ∈ C.languages, (↑T : Set X) ⊆ L}

/-- Definition 5.9, all three cases in their source order. -/
noncomputable def robustClosure {X : Type*} (C : LanguageClass X) {n : ℕ}
    (S : Fin n → X) (t : ℕ) : Set X :=
  by
    classical
    exact if (((support S).card : ℤ) - (hellyNat C : ℤ) * t : WithTop ℤ) ≤ closureDim C then ∅
      else if (retained C S t).Nonempty then ⋂ T ∈ retained C S t, closure C (↑T)
      else Set.univ

/-- Definition 5.13: occurrences in the public range. -/
noncomputable def blockIndices {X : Type*} (C : LanguageClass X) (m : ℕ)
    {n : ℕ} (S : Fin n → X) (σ : List ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (robustLength C m)).filter
      (fun t => barredProfile C (robustClosure C S t) = σ)

noncomputable def blockLength {X : Type*} (C : LanguageClass X) (m : ℕ)
    {n : ℕ} (S : Fin n → X) (σ : List ℕ) : ℕ :=
  (blockIndices C m S σ).card

/-- Least occurring index, with an irrelevant empty-block default. -/
noncomputable def blockOutput {X : Type*} (C : LanguageClass X) (m : ℕ)
    {n : ℕ} (S : Fin n → X) (σ : List ℕ) : Set X :=
  by
    classical
    exact if h : (blockIndices C m S σ).Nonempty then
      barredCoreStar C (robustClosure C S ((blockIndices C m S σ).min' h))
    else Set.univ

end PrivateUniformGen.Characterization


