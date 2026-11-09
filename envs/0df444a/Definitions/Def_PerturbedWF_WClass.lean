-- Prove2me | Definitions.Def_PerturbedWF_WClass
-- name    : PerturbedWF_WClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:34:11.220278+00:00
-- url     : https://prove2.me/theorems/0fba3c21-d3a2-4c12-81ce-568f5ec3ce1c
-- title:
--   Configuration spaces, the exchange property, 1-Lipschitzness, the class $\mathcal W(\mathcal C)$, $\mathrm{supp}(W)$ and $W^*$
-- statement:
--   A **configuration space** is a compact set $\mathcal C\subseteq\{x\in\mathbb R^n_{\ge0}:\sum_ix_i=C\}$ for a fixed constant $C>0$. Examples: the simplex $\{x\in[0,1]^n:\sum_ix_i=1\}$ and the integral configurations $\{x\in\mathbb Z^n_{\ge0}:\sum_ix_i=k\}$.
--
--   Let $W:\mathcal C\to\mathbb R\cup\{\infty\}$ and $\mathrm{dom}(W)=\{x\in\mathcal C:W(x)<\infty\}$.
--
--   1. **Exchange property (Definition 2.1).** Whenever $x,y\in\mathcal C$ satisfy $x_i>y_i$, there are $j$ with $x_j<y_j$ and $\varepsilon\in(0,\min\{x_i-y_i,\,y_j-x_j\}]$ such that $\tilde x=x-\varepsilon e_i+\varepsilon e_j$ and $\tilde y=y+\varepsilon e_i-\varepsilon e_j$ lie in $\mathcal C$ and
--   $$W(\tilde x)+W(\tilde y)\le W(x)+W(y);$$
--   for an integral configuration space $\mathcal C\subseteq\mathbb Z^n_{\ge0}$ this must hold with $\varepsilon=1$.
--   2. **1-Lipschitzness (Definition 2.2).** $|W(x)-W(y)|\le\|x-y\|$ for all $x,y\in\mathrm{dom}(W)$.
--
--   The class $\mathcal W(\mathcal C)$ consists of the $W$ with nonempty compact domain satisfying 1 and 2. The **support** of $W$ is
--   $$\mathrm{supp}(W)=\{x\in\mathcal C:\ W(x)<W(y)+\|x-y\|\ \ \forall y\in\mathcal C\setminus\{x\}\},$$
--   and its **Fenchel conjugate** is
--   $$W^*(v)=\max_{x\in\mathcal C}\{\langle v,x\rangle-W(x)\}.\qquad(2.4)$$
--
--   These are the abstract properties of work functions on which the whole analysis runs.
--
--   **Formalization Note.** $W$ is a function $\mathbb R^\iota\to$ `EReal`, of which only the values on $\mathcal C$ are used; the class requires $W\ne-\infty$ on $\mathcal C$. The 1-Lipschitz condition is the pair of one-sided inequalities $W(x)\le W(y)+\|x-y\|$, $W(y)\le W(x)+\|x-y\|$. The conjugate `conj` is the supremum in `EReal`; for $W\in\mathcal W(\mathcal C)$ it is finite and attained, and statements that use the maximum assert a maximizer explicitly. `IsIntegral C` says every coordinate of every configuration is an integer.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §2 'Configurations', p.5 (PDF p.6); Definitions 2.1 and 2.2, the class W(C), supp(W) and (2.4), p.6 (PDF p.7); simplex, §4 p.11; integral configurations, Lemma B.1(2) p.32

import Mathlib
import Definitions.Def_PerturbedWF_transNorm

namespace PerturbedWF

/-!
# Configuration spaces, the class `W(C)`, the support and the Fenchel conjugate

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §2, p.5 (PDF p.6), "Configurations"; p.6 (PDF p.7),
Definition 2.1 (Exchange property), Definition 2.2 (1-Lipschitzness), the class `W(C)`, the support
`supp(W)` and the Fenchel conjugate (2.4); §4, p.11 (the simplex); Lemma B.1(2), p.32 (the integral
configurations `{x ∈ ℤⁿ_{≥0} : ∑ x_i = k}`).

**Formalization Note.**
* A function `W : C → ℝ ∪ {∞}` is a function `W : (ι → ℝ) → EReal`; only its values on `C` are
  ever used, and the class requires `W x ≠ ⊥` on `C`. `dom C W = {x ∈ C | W x ≠ ⊤}`.
* The exchange property keeps the paper's requirement "where `x̃, ỹ ∈ C`" inside the existential,
  and, when `C` consists of integral points (`IsIntegral C`, the paper's `C ⊆ ℤⁿ_{≥0}`), requires
  `ε = 1`. The other index `j` is distinct from `i` automatically (`x_j < y_j`, `x_i > y_i`).
* 1-Lipschitzness `|W(x) − W(y)| ≤ ‖x − y‖` on `dom(W)` is written as the two one-sided
  inequalities in `EReal` (both values are finite there).
* `conj C W v = sup_{x ∈ C} (⟨v, x⟩ − W(x))` is taken in `EReal`; the paper's (2.4) writes `max`.
  For `W ∈ W(C)` the supremum is finite and attained; statements that use the maximum say so
  explicitly.
* `IsConfigSpace C` is the standing assumption of §2: `C` is compact and contained in
  `{x ∈ ℝⁿ_{≥0} : ∑ x_i = c}` for some fixed `c > 0`.
-/

/-- The standing assumption of §2 (p.5): `C` is compact and `C ⊆ {x ∈ ℝⁿ_{≥0} : ∑ x_i = c}` for
some fixed constant `c > 0`. -/
def IsConfigSpace {ι : Type} [Fintype ι] (C : Set (ι → ℝ)) : Prop :=
  IsCompact C ∧ ∃ c : ℝ, 0 < c ∧ ∀ x ∈ C, (∀ i, 0 ≤ x i) ∧ ∑ i, x i = c

/-- `C` is an integral configuration space: every coordinate of every configuration is an
integer. -/
def IsIntegral {ι : Type} (C : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ C, ∀ i, ∃ z : ℤ, x i = z

/-- The (fractional) simplex `{x ∈ [0, 1]ⁿ : ∑ x_i = 1}` (§4, p.11), the configuration space of
metric allocation. -/
def simplex (ι : Type) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = 1}

/-- The integral configurations `{x ∈ ℤⁿ_{≥0} : ∑ x_i = k}` (k-server configurations, §2 p.5 and
Lemma B.1(2)). -/
def kConfig (ι : Type) [Fintype ι] (k : ℕ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ ∃ z : ℤ, x i = z) ∧ ∑ i, x i = k}

/-- Definition 2.1 (Exchange property): whenever `x, y ∈ C` and `x_i > y_i`, there are `j` with
`x_j < y_j` and `ε ∈ (0, min{x_i − y_i, y_j − x_j}]` such that `x̃ = x − ε e_i + ε e_j` and
`ỹ = y + ε e_i − ε e_j` lie in `C` and `W(x̃) + W(ỹ) ≤ W(x) + W(y)`; for an integral `C`, with
`ε = 1`. -/
def ExchangeProperty {ι : Type} [DecidableEq ι] (C : Set (ι → ℝ)) (W : (ι → ℝ) → EReal) :
    Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ i, y i < x i → ∃ j, x j < y j ∧ ∃ ε : ℝ, 0 < ε ∧
    ε ≤ x i - y i ∧ ε ≤ y j - x j ∧ (IsIntegral C → ε = 1) ∧
    x - ε • Pi.single i (1 : ℝ) + ε • Pi.single j (1 : ℝ) ∈ C ∧
    y + ε • Pi.single i (1 : ℝ) - ε • Pi.single j (1 : ℝ) ∈ C ∧
    W (x - ε • Pi.single i (1 : ℝ) + ε • Pi.single j (1 : ℝ)) +
      W (y + ε • Pi.single i (1 : ℝ) - ε • Pi.single j (1 : ℝ)) ≤ W x + W y

/-- `dom(W) = {x ∈ C : W(x) < ∞}`. -/
def dom {ι : Type} (C : Set (ι → ℝ)) (W : (ι → ℝ) → EReal) : Set (ι → ℝ) :=
  {x | x ∈ C ∧ W x ≠ ⊤}

/-- Definition 2.2 (1-Lipschitzness on the domain): `|W(x) − W(y)| ≤ ‖x − y‖` for all
`x, y ∈ dom(W)`. -/
def OneLipschitz {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ)) (d : ι → ι → ℝ)
    (W : (ι → ℝ) → EReal) : Prop :=
  ∀ x ∈ dom C W, ∀ y ∈ dom C W,
    W x ≤ W y + (transNorm d (x - y) : EReal) ∧ W y ≤ W x + (transNorm d (x - y) : EReal)

/-- The class `W(C)` (p.6): `W : C → ℝ ∪ {∞}` with nonempty compact domain satisfying
Definitions 2.1 and 2.2. -/
def WClass {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ)) (d : ι → ι → ℝ)
    (W : (ι → ℝ) → EReal) : Prop :=
  (∀ x ∈ C, W x ≠ ⊥) ∧ (dom C W).Nonempty ∧ IsCompact (dom C W) ∧ ExchangeProperty C W ∧
    OneLipschitz C d W

/-- The support `supp(W) = {x ∈ C : W(x) < W(y) + ‖x − y‖ for all y ∈ C ∖ {x}}` (p.6). -/
def supp {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ)) (d : ι → ι → ℝ)
    (W : (ι → ℝ) → EReal) : Set (ι → ℝ) :=
  {x | x ∈ C ∧ ∀ y ∈ C, y ≠ x → W x < W y + (transNorm d (x - y) : EReal)}

/-- The Fenchel conjugate (2.4), `W*(v) = sup_{x ∈ C} (⟨v, x⟩ − W(x))`, in `EReal`. -/
noncomputable def conj {ι : Type} [Fintype ι] (C : Set (ι → ℝ)) (W : (ι → ℝ) → EReal)
    (v : ι → ℝ) : EReal :=
  ⨆ x ∈ C, ((dot v x : ℝ) : EReal) - W x

end PerturbedWF


