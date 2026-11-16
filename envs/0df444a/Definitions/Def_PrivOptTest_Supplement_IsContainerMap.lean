-- Prove2me | Definitions.Def_PrivOptTest_Supplement_IsContainerMap
-- name    : PrivOptTest_Supplement_IsContainerMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:33:54.658047+00:00
-- url     : https://prove2.me/theorems/01465722-bc50-44fc-8526-a07b7cb3ee2a
-- title:
--   Dual discretizations (Lemma 4.3) and halfspace container maps at $\eta=1/4$ (Lemma 4.5)
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d$ be finite with $|\mathcal X|=m$.
--
--   1. A finite set $\mathcal W\subseteq\mathbb R^d$ is a **dual discretization** of $\mathcal X$ if for every $w\in\mathbb R^d$ some $w'\in\mathcal W$ satisfies $h_w(x)=h_{w'}(x)$ for every $x\in\mathcal X$, and $|\mathcal W|\le(2m)^d$. These are the two conclusions of Lemma 4.3.
--   2. A map $S\mapsto\mathcal C(S)$ from finite subsets of $\mathbb R^d$ to families of subsets is a **halfspace container map with constant $c$** if, for every finite $S$, every $C\in\mathcal C(S)$ satisfies $C\subseteq S$, $|\mathcal C(S)|\le 8^{cd}$, and for every affine halfspace $H=\{x:\langle a,x\rangle\le b\}$ with $a\ne0$ there is $C\in\mathcal C(S)$ with
--   $$H\cap S\subseteq C\qquad\text{and}\qquad |C\setminus H|\le |S|/4 .$$
--   These are the conclusions of Lemma 4.5 at $\eta=1/4$, where $(2/\eta)^{cd}=8^{cd}$.
--
--   Algorithm 3 takes such a $\mathcal W$ (its $\mathcal W_{\mathrm{disc}}$) and such a map (its $\mathcal C(\cdot,1/4)$) as public inputs.
--
--   **Formalization Note** Only closed halfspaces are required: on a finite $S$ an open halfspace cuts out the same subset of $S$ as a closed one.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 4.3, p.28; Lemma 4.5, p.29; Algorithm 3, line 7, p.30

import Mathlib
import Definitions.Def_PrivOptTest_Supplement_HhsOn

namespace PrivOptTest

namespace Supplement

/-- **A finite dual discretization, the conclusion of Lemma 4.3** (arXiv:2611.03599, manuscript sha256
4ac94dcf…, p.28): a finite `W ⊆ ℝ^d` such that every `w ∈ ℝ^d` has some `w' ∈ W` with
`h_w(x) = h_{w'}(x)` for every `x ∈ X`, and `|W| ≤ (2m)^d` with `m = |X|`. This is the input `W_disc` of
Algorithm 3. -/
def IsDualDisc {d : ℕ} (X W : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ w : EuclideanSpace ℝ (Fin d), ∃ w' ∈ W, ∀ x ∈ X, hs w x = hs w' x) ∧
    W.card ≤ (2 * X.card) ^ d

/-- **A halfspace container map, the conclusion of Lemma 4.5 at `η = 1/4`** (p.29), with container
constant `c`: for every finite `S ⊆ ℝ^d`,
1. every `C ∈ cont S` is a subset of `S` (`C(S, η) ⊆ 2^S`);
2. `|cont S| ≤ (2/η)^{cd} = 8^{cd}`;
3. for every affine halfspace `H = {x : ⟨a, x⟩ ≤ b}` (`a ≠ 0`) some `C ∈ cont S` has `H ∩ S ⊆ C` and
   `|C \ H| ≤ |S|/4`.

This is the family `C(·, 1/4)` that line 7 of Algorithm 3 (p.30) constructs.

**Formalization Note.** Only closed halfspaces are required. On a finite `S` an open halfspace
`{⟨a, x⟩ < b}` cuts out the same subset of `S` as a closed one `{⟨a, x⟩ ≤ b'}`, so the condition is
the paper's. -/
def IsContainerMap {d : ℕ} (c : ℝ)
    (cont : Finset (EuclideanSpace ℝ (Fin d)) → Finset (Finset (EuclideanSpace ℝ (Fin d)))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin d)),
    (∀ C ∈ cont S, C ⊆ S) ∧
    ((cont S).card : ℝ) ≤ (8 : ℝ) ^ (c * d) ∧
    ∀ (a : EuclideanSpace ℝ (Fin d)) (b : ℝ), a ≠ 0 →
      ∃ C ∈ cont S, S.filter (fun x => inner ℝ a x ≤ b) ⊆ C ∧
        ((C.filter fun x => ¬ inner ℝ a x ≤ b).card : ℝ) ≤ (S.card : ℝ) / 4

end Supplement

end PrivOptTest


