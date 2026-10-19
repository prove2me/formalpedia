-- Prove2me | Definitions.Def_TwoStageSRO_AsymOpt_Geometry
-- name    : TwoStageSRO_AsymOpt_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:34.48346+00:00
-- url     : https://prove2.me/theorems/1bc2faa6-716f-4e62-9d27-29bdd51b6610
-- title:
--   App. A, pp. 33–34, and §4, pp. 12–14 — faces and minimal faces of Ξ, the radius ∆_Ξ (Definition 2), conditions [A4], [A5], [A6]
-- statement:
--   Write the polyhedron as $\Xi=\{\zeta\in\mathbb R^d: g_i^\top\zeta\ge g^0_i,\ i\in[\tilde m]\}$ and let $\mathcal H_i=\{\zeta: g_i^\top\zeta=g^0_i\}$ be the hyperplane of its $i$-th constraint.
--
--   1. **Faces.** A face of $\Xi$ is a nonempty set of the form $\{\zeta\in\Xi: g_i^\top\zeta=g^0_i \text{ for all } i\in I\}$ with $I\subseteq[\tilde m]$; a **minimal face** is a face that contains no other face.
--   2. **Definition 2 (radius of a point).** For $\zeta\in\Xi$ with active set $I_\Xi(\zeta)=\{i: \zeta\in \mathcal H_i\}$,
--   $$\Delta_\Xi(\zeta)=\min_{i\in[\tilde m]\setminus I_\Xi(\zeta)}\operatorname{dist}(\zeta,\mathcal H_i),\qquad \operatorname{dist}(\zeta,\mathcal H_i)=\min_{\zeta'\in \mathcal H_i}\|\zeta'-\zeta\|,$$
--   with $\Delta_\Xi(\zeta)=+\infty$ when every constraint is active.
--   3. **[A4]** There exist $x\in\mathbb R^n$ and $\epsilon>0$ such that for every $\hat\zeta\in\Xi$ some linear decision rule $y^{\hat\zeta}(\cdot)\in\mathcal L$ satisfies $Tx+Wy^{\hat\zeta}(\zeta)\ge h(\zeta)$ for all $\zeta\in B(\hat\zeta,\epsilon)\cap\Xi$.
--   4. **[A5]** There exist $x\in\mathbb R^n$ and $\epsilon>0$ such that (a) $Q(x,\zeta)<\infty$ for all $\zeta\in\Xi$, and (b) for each minimal face $F$ of $\Xi$ there is $Y^F\in\mathbb R^{r\times d}$ with $Q^{\{Y^F\}}_\epsilon(x,\zeta)<\infty$ for all $\zeta\in F$.
--   5. **[A6]** There exist $x\in\mathbb R^n$, $\epsilon>0$ and a finite set $\mathcal C\subseteq\mathbb R^{r\times d}$ with $Q^{\mathcal C}_\epsilon(x,\zeta)<\infty$ for all $\zeta\in\Xi$.
--
--   [A4] is the feasibility hypothesis of the main theorem; [A5] and [A6] are the equivalent conditions of Lemma 1, and faces and radii are the polyhedral tools of its proof.
--
--   **Formalization Note** Faces are described by index sets of constraints set to equality, and are required to be nonempty. The distance and the radius are computed in `EReal` with the $\ell_p$-norm, as an infimum over the inactive indices and the points of $\mathcal H_i$; an empty hyperplane (a zero row of $G$ with $g^0_i\ne0$) contributes $+\infty$. Outside $\Xi$ the radius is not used.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, pp. 33–34, App. A.1 and Definition 2; p. 12, Theorem 2 [A4]; p. 14, Lemma 1 [A5], [A6]

import Mathlib
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 33, App. A.1:
the hyperplane `Hₖ = {ζ ∈ ℝᵈ : gₖᵀζ = g⁰ₖ}` of the `k`-th constraint of `Ξ` (`gₖᵀ` is row `k` of `G`). -/
def hyperplane (M : Model n d r m mt) (k : Fin mt) : Set (Fin d → ℝ) :=
  {ζ | (M.G *ᵥ ζ) k = M.g0 k}

/-- arXiv:1907.07142v4, pp. 33–34, App. A.1: the set `{ζ ∈ Ξ : gₖᵀζ = g⁰ₖ for all k ∈ I}` obtained by
setting the constraints indexed by `I ⊆ [m̃]` of `Ξ` to equality. -/
def face (M : Model n d r m mt) (I : Finset (Fin mt)) : Set (Fin d → ℝ) :=
  {ζ | ζ ∈ Xi M ∧ ∀ k ∈ I, (M.G *ᵥ ζ) k = M.g0 k}

/-- arXiv:1907.07142v4, p. 34, App. A.1 (Faces(Ξ); Conforti et al. 2014, §3.8): `F` is a (nonempty)
face of the polyhedron `Ξ`, i.e. `F = {ζ ∈ Ξ : G_I ζ = g⁰_I}` for some index set `I`, and `F ≠ ∅`. -/
def IsFace (M : Model n d r m mt) (F : Set (Fin d → ℝ)) : Prop :=
  F.Nonempty ∧ ∃ I : Finset (Fin mt), F = face M I

/-- arXiv:1907.07142v4, p. 14, Lemma 1 [A5], and p. 40, Lemma 9: `F` is a minimal face of `Ξ`, i.e. a
face of `Ξ` that contains no other face of `Ξ`. -/
def IsMinimalFace (M : Model n d r m mt) (F : Set (Fin d → ℝ)) : Prop :=
  IsFace M F ∧ ∀ F', IsFace M F' → F' ⊆ F → F' = F

/-- arXiv:1907.07142v4, p. 34, Definition 2: the radius of `ζ ∈ Ξ` with respect to `Ξ`,
`∆_Ξ(ζ) = min_{i ∈ [m̃] \ I_Ξ(ζ)} dist(ζ, Hᵢ)`, where `I_Ξ(ζ) = {i : ζ ∈ Hᵢ}` is the active index set
(p. 33) and `dist(ζ, Hᵢ) = min_{ζ' ∈ Hᵢ} ‖ζ' − ζ‖` (p. 33, (14)).

**Formalization Note** Computed in `EReal` as an infimum over the inactive indices `i` and the points
`ζ' ∈ Hᵢ` of `‖ζ' − ζ‖` (the `ℓp`-norm): it is `+∞` when every constraint is active (as in the proof of
Lemma 4, p. 34) and, for an empty hyperplane (a zero row of `G`), that hyperplane contributes `+∞`. -/
noncomputable def radius (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] (ζ : Fin d → ℝ) : EReal :=
  ⨅ k ∈ {k : Fin mt | ζ ∉ hyperplane M k}, ⨅ ζ' ∈ hyperplane M k,
    ((‖WithLp.toLp p (ζ' - ζ)‖ : ℝ) : EReal)

/-- arXiv:1907.07142v4, p. 12, Theorem 2, condition [A4]: there exist a first-stage decision `x ∈ ℝⁿ` and
a radius `ε > 0` such that, for all `ζ̂ ∈ Ξ`, there is a linear decision rule `y^ζ̂(·) ∈ L` with
`Tx + Wy^ζ̂(ζ) ≥ h(ζ)` for all `ζ ∈ B(ζ̂, ε) ∩ Ξ`. -/
def A4 (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∃ x : Fin n → ℝ, ∃ ε : ℝ, 0 < ε ∧
    ∀ zhat ∈ Xi M, ∃ y : Pol d r, y ∈ LDR ∧ robFeas M x (ball p zhat ε ∩ Xi M) y

/-- arXiv:1907.07142v4, p. 14, Lemma 1, condition [A5]: there exist `x ∈ ℝⁿ` and `ε > 0` such that
(a) `Q(x, ζ) < ∞` for all `ζ ∈ Ξ`, and (b) for each minimal face `F` of `Ξ` there is a recourse matrix
`Y^F ∈ ℝ^{r×d}` with `Q^{{Y^F}}_ε(x, ζ) < ∞` for all `ζ ∈ F`. -/
def A5 (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∃ x : Fin n → ℝ, ∃ ε : ℝ, 0 < ε ∧
    (∀ ζ ∈ Xi M, Q M x ζ < ⊤) ∧
    ∀ F, IsMinimalFace M F → ∃ YF : Matrix (Fin r) (Fin d) ℝ, ∀ ζ ∈ F, QC M p {YF} ε x ζ < ⊤

/-- arXiv:1907.07142v4, p. 14, Lemma 1, condition [A6]: there exist `x ∈ ℝⁿ`, `ε > 0` and a finite set
`C ⊆ ℝ^{r×d}` of recourse matrices with `Q^C_ε(x, ζ) < ∞` for all `ζ ∈ Ξ`. -/
def A6 (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∃ x : Fin n → ℝ, ∃ ε : ℝ, 0 < ε ∧ ∃ C : Set (Matrix (Fin r) (Fin d) ℝ), C.Finite ∧
    ∀ ζ ∈ Xi M, QC M p C ε x ζ < ⊤

end TwoStageSRO.AsymOpt


