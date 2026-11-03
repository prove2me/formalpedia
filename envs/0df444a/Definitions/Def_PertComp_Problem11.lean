-- Prove2me | Definitions.Def_PertComp_Problem11
-- name    : PertComp_Problem11
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:04.522198+00:00
-- url     : https://prove2.me/theorems/f4b66e7d-3ef4-4fa9-b09d-2e0c8558fe10
-- title:
--   Problem 1.1: the standing setting
-- statement:
--   Let $X$ and $Y$ be reflexive real Banach spaces, let $\varphi\in\Gamma_0(\mathbb R)$ be increasing and not constant, let $f\in\Gamma_0(X)$, $g\in\Gamma_0(Y)$, $\ell\in\Gamma_0(Y)$, let $L\colon X\to Y$ be linear and bounded, and let $h\in\Gamma_0(X)$. Suppose that
--
--   1. [a] there is $z\in\operatorname{dom} f$ with $f(z)\in\operatorname{int}\operatorname{dom}\varphi$;
--   2. [b] $0\in\operatorname{sri}\big(f^{-1}(\operatorname{dom}\varphi)-\operatorname{dom} h\big)$;
--   3. [c] $0\in\operatorname{sri}\big(\operatorname{dom} g^*-\operatorname{dom}\ell^*\big)$;
--   4. [d] $0\in\operatorname{sri}\big(L(\operatorname{dom} h\cap f^{-1}(\operatorname{dom}\varphi))-\operatorname{dom} g-\operatorname{dom}\ell\big)$.
--
--   The problem is to minimize $(\varphi\circ f)(x)+(g\,\Box\,\ell)(Lx)+h(x)$ over $x\in X$.
--
--   **Formalization Note** "Increasing" is nondecreasing (`Monotone φ`), the paper's usage (Example 1.2 takes $\varphi=\iota_{]-\infty,0]}$). Completeness is an instance on the theorems, reflexivity a field of the structure. Differences of sets are Minkowski differences; $g^*,\ell^*$ are functions on $Y^*$ and [c] is a condition in $Y^*$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Problem 1.1, p.2

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_sri
import Definitions.Def_PertComp_preDom

namespace PertComp

open Pointwise

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Problem 1.1**, p.2: the standing setting.
`X` and `Y` are reflexive real Banach spaces, `φ ∈ Γ₀(ℝ)` is increasing and not constant,
`f ∈ Γ₀(X)`, `g ∈ Γ₀(Y)`, `ℓ ∈ Γ₀(Y)`, `L : X → Y` is linear and bounded, `h ∈ Γ₀(X)`, and
* [a] `(∃ z ∈ dom f) f(z) ∈ int dom φ`;
* [b] `0 ∈ sri (f⁻¹(dom φ) − dom h)`;
* [c] `0 ∈ sri (dom g* − dom ℓ*)` (in `Y*`);
* [d] `0 ∈ sri (L(dom h ∩ f⁻¹(dom φ)) − dom g − dom ℓ)`.

**Formalization Note.** `Γ₀` (proper, lower semicontinuous, convex, into `]−∞, +∞]`, pp.1–2) is the
published `TensorAHPE.IsProperClosedConvex` (never `⊥`, somewhere `≠ ⊤`, lower semicontinuous for
the norm topology, convex epigraph). Completeness is the instance `[CompleteSpace _]` on the
theorems; reflexivity is the predicate `IsReflexive`. "Increasing" is nondecreasing (`Monotone φ`, the
paper's usage: Example 1.2 takes `φ = ι_{]−∞,0]}`). `dom` is `{· ≠ ⊤}`, `−` is the pointwise
(Minkowski) difference of sets, `g*` is `RockafellarMaxMono.Shared.conj g` on `StrongDual ℝ Y`. -/
structure Problem11 {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (φ : ℝ → EReal) (f : X → EReal)
    (g ℓ : Y → EReal) (L : X →L[ℝ] Y) (h : X → EReal) : Prop where
  reflexive_X : IsReflexive X
  reflexive_Y : IsReflexive Y
  gamma0_φ : TensorAHPE.IsProperClosedConvex φ
  monotone_φ : Monotone φ
  not_const_φ : ∃ a b : ℝ, φ a ≠ φ b
  gamma0_f : TensorAHPE.IsProperClosedConvex f
  gamma0_g : TensorAHPE.IsProperClosedConvex g
  gamma0_ℓ : TensorAHPE.IsProperClosedConvex ℓ
  gamma0_h : TensorAHPE.IsProperClosedConvex h
  cond_a : ∃ z : X, f z ≠ ⊤ ∧ (f z).toReal ∈ interior {t : ℝ | φ t ≠ ⊤}
  cond_b : (0 : X) ∈ sri (preDom φ f - {x | h x ≠ ⊤})
  cond_c : (0 : StrongDual ℝ Y) ∈
    sri ({y' | RockafellarMaxMono.Shared.conj g y' ≠ ⊤} -
      {y' | RockafellarMaxMono.Shared.conj ℓ y' ≠ ⊤})
  cond_d : (0 : Y) ∈
    sri (L '' ({x | h x ≠ ⊤} ∩ preDom φ f) - {y | g y ≠ ⊤} - {y | ℓ y ≠ ⊤})

end PertComp


