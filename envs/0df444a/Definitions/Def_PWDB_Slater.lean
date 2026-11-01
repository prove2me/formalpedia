-- Prove2me | Definitions.Def_PWDB_Slater
-- name    : PWDB_Slater
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:59.669992+00:00
-- url     : https://prove2.me/theorems/1980ec27-2f5f-4f54-b12f-9955d0d11405
-- title:
--   Slater points of sets and of optimization problems (Definitions 1, 2)
-- statement:
--   Let $X = \{x \mid f_i(x) \le 0\ \forall i \in I,\ h_j(x) = 0\ \forall j \in J\}$ with $f_i, h_j : \mathbb X \to \overline{\mathbb R}$ on a real normed space $\mathbb X$.
--
--   1. $x^S$ is a **Slater point** of this representation of $X$ if (i) $x^S \in \operatorname{ri}(\operatorname{dom} f_i)$ and $x^S \in \operatorname{ri}(\operatorname{dom} h_j)$ for all $i, j$; (ii) $x^S \in X$; (iii) $f_i(x^S) < 0$ for every $i$ such that $f_i$ is not affine. It is **strict** if $f_i(x^S) < 0$ for all $i \in I$.
--   2. $x^S$ is a (strict) Slater point of the minimization problem $\inf\{f_0(x) \mid x \in X\}$ if it is a (strict) Slater point of $X$ and $x^S \in \operatorname{ri}(\operatorname{dom} f_0)$; for a maximization problem the last condition is $x^S \in \operatorname{ri}(\operatorname{dom}(-f_0))$.
--
--   The definitions depend on the representation of $X$: $\{0\} = \{x \mid x = 0\}$ has a strict Slater point, $\{0\} = \{x \mid x^2 \le 0\}$ has none (p.6).
--
--   **Formalization Note** $\operatorname{ri}$ is Mathlib's `intrinsicInterior ℝ`, $\operatorname{dom}$ is `AubinLipschitz.effDom`. The module contains `SlaterSet`, `StrictSlaterSet`, `SlaterMin`, `StrictSlaterMin`, `SlaterMax`, `StrictSlaterMax`. "Nonlinear" is read as "not affine" (Definition A.6, p.41).
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Definitions 1, 2 and the remark after Definition 2, pp.6–7

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PWDB_IsAffineFn

namespace PWDB

/-- **Slater point of a set** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Definition 1, p.6):
"The vector `xS` is a Slater point of the set `X` represented by
`X = {x ∈ ℝ^{dx} | fi(x) ≤ 0 ∀i ∈ I, hj(x) = 0 ∀j ∈ J}` if (i) `xS ∈ ri(dom(fi))` as well as
`xS ∈ ri(dom(hj))` for all `i ∈ I` and `j ∈ J`; (ii) `xS ∈ X`; and (iii) `fi(xS) < 0` for all
`i ∈ I` such that `fi` is nonlinear."

**Formalization Note** `ri` is Mathlib's `intrinsicInterior ℝ`; `dom` is `AubinLipschitz.effDom`.
"Nonlinear" is read as "not affine" (`IsAffineFn`), as in the paper's Definition A.6 (p.41). The
definition depends on the representation `(f, h)`, as the paper stresses. The ambient space is a
real normed space `X`, so that the definition also applies to the variable spaces (products) of the
dual and reformulated problems. -/
def SlaterSet {X ι J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ι → X → EReal) (h : J → X → EReal) (xS : X) : Prop :=
  (∀ i, xS ∈ intrinsicInterior ℝ (AubinLipschitz.effDom (f i))) ∧
  (∀ j, xS ∈ intrinsicInterior ℝ (AubinLipschitz.effDom (h j))) ∧
  (∀ i, f i xS ≤ 0) ∧ (∀ j, h j xS = 0) ∧
  (∀ i, ¬ IsAffineFn (f i) → f i xS < 0)

/-- **Strict Slater point of a set** (arXiv:2105.00760v2, Definition 1, p.6): "The Slater point
`xS` is strict if `fi(xS) < 0` for all `i ∈ I`." -/
def StrictSlaterSet {X ι J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ι → X → EReal) (h : J → X → EReal) (xS : X) : Prop :=
  SlaterSet f h xS ∧ ∀ i, f i xS < 0

/-- **Slater point of a minimization problem** (arXiv:2105.00760v2, Definition 2, p.7): "The vector
`xS` is a Slater point of the minimization problem `inf{f0(x) | x ∈ X}`, where `X` is represented as
in Definition 1, if `xS` is a Slater point of `X` and `xS ∈ ri(dom(f0))`." -/
def SlaterMin {X ι J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f₀ : X → EReal) (f : ι → X → EReal) (h : J → X → EReal) (xS : X) : Prop :=
  SlaterSet f h xS ∧ xS ∈ intrinsicInterior ℝ (AubinLipschitz.effDom f₀)

/-- **Strict Slater point of a minimization problem** (arXiv:2105.00760v2, Definition 2, p.7):
"The Slater point `xS` is strict if it is a strict Slater point of `X`." -/
def StrictSlaterMin {X ι J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f₀ : X → EReal) (f : ι → X → EReal) (h : J → X → EReal) (xS : X) : Prop :=
  SlaterMin f₀ f h xS ∧ ∀ i, f i xS < 0

/-- **Slater point of a maximization problem** (arXiv:2105.00760v2, p.7): "For a maximization
problem, we replace the requirement `xS ∈ ri(dom(f0))` in Definition 2 with `xS ∈ ri(dom(−f0))`."
Here `dom(−f0) = {x | f0 x ≠ −∞}`. -/
def SlaterMax {X ι J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f₀ : X → EReal) (f : ι → X → EReal) (h : J → X → EReal) (xS : X) : Prop :=
  SlaterSet f h xS ∧ xS ∈ intrinsicInterior ℝ (AubinLipschitz.effDom (fun x => -f₀ x))

/-- **Strict Slater point of a maximization problem** (arXiv:2105.00760v2, Definition 2 and the
remark after it, p.7): a Slater point of the maximization problem that is a strict Slater point of
the feasible set. -/
def StrictSlaterMax {X ι J : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f₀ : X → EReal) (f : ι → X → EReal) (h : J → X → EReal) (xS : X) : Prop :=
  SlaterMax f₀ f h xS ∧ ∀ i, f i xS < 0

end PWDB


