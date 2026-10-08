-- Prove2me | Definitions.Def_ReluMIP_Ideal_Setting
-- name    : ReluMIP_Ideal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:40.790578+00:00
-- url     : https://prove2.me/theorems/94e0685a-d2c5-48e5-8385-0fc38b6d32f2
-- title:
--   §1.1, §1.3, §2.1–2.3, App. A.1 — the ReLU graph, L̆, Ŭ, M±(f), strict activity, formulations (3), (5), (6), system (7), ideality
-- statement:
--   This module fixes the objects of Anderson, Huchette, Tjandraatmadja and Vielma's analysis of a single ReLU neuron.
--
--   Let $\eta\in\mathbb N$, a weight vector $w\in\mathbb R^\eta$, a bias $b\in\mathbb R$ and bounds $L,U\in\mathbb R^\eta$. The neuron computes $\mathrm{ReLU}(f(x))$ with $\mathrm{ReLU}(v)=\max\{0,v\}$ and the affine function $f(x)=w\cdot x+b$, over the box $[L,U]=\{x : L\le x\le U\}$. Its graph is
--   $$
--   \operatorname{gr}(\mathrm{ReLU}\circ f;[L,U])=\{(x,\mathrm{ReLU}(f(x))) : L\le x\le U\}.
--   $$
--
--   1. **Sign-adjusted bounds.** $\breve L_i=L_i$ and $\breve U_i=U_i$ if $w_i\ge 0$; $\breve L_i=U_i$ and $\breve U_i=L_i$ if $w_i<0$.
--   2. **Extreme values of $f$.** $M^+(f)=w\cdot\breve U+b$ and $M^-(f)=w\cdot\breve L+b$ (the maximum and minimum of $f$ over $[L,U]$).
--   3. **Support.** $\operatorname{supp}(w)=\{i : w_i\neq 0\}$.
--   4. **Strict activity.** $M^-(f)<0<M^+(f)$.
--   5. **Formulation (6) and its LP relaxation.** For $I\subseteq\operatorname{supp}(w)$, inequality (6b) reads
--   $$
--   y\le\sum_{i\in I}w_i\bigl(x_i-\breve L_i(1-z)\bigr)+\Bigl(b+\sum_{i\notin I}w_i\breve U_i\Bigr)z ,
--   $$
--   and the LP relaxation of (6) is the set of $(x,y,z)$ with $y\ge w\cdot x+b$ (6a), (6b) for every $I\subseteq\operatorname{supp}(w)$, $x\in[L,U]$, $y\ge 0$ and $0\le z\le 1$.
--   6. **Formulations and ideality.** A set $R$ of points $(x,y,z)$ (an LP relaxation) together with $z\in\{0,1\}$ is a *formulation* of a set $S$ of points $(x,y)$ if $(x,y)\in S$ exactly when $(x,y,z)\in R$ for some $z\in\{0,1\}$. The formulation is *ideal* if every extreme point of $R$ has $z\in\{0,1\}$.
--   7. **Big-M formulation (3), LP relaxation:** $y\ge f(x)$, $y\le f(x)-M^-(f)(1-z)$, $y\le M^+(f)z$, $x\in[L,U]$, $y\ge0$, $0\le z\le1$.
--   8. **Multiple-choice formulation (5), LP relaxation, projected to $(x,y,z)$:** the points for which there are $x^0,x^1\in\mathbb R^\eta$ and $y^0,y^1\in\mathbb R$ with $(x,y)=(x^0,y^0)+(x^1,y^1)$, $y^0=0\ge w\cdot x^0+b(1-z)$, $y^1=w\cdot x^1+bz\ge0$, $L(1-z)\le x^0\le U(1-z)$, $Lz\le x^1\le Uz$ and $0\le z\le 1$.
--   9. **System (7)**, in sign-adjusted form: the LP relaxation of (6) together with, for every $I\subseteq\operatorname{supp}(w)$,
--   $$
--   y\ge\sum_{i\in I}w_i\bigl(x_i-\breve U_i(1-z)\bigr)+\Bigl(b+\sum_{i\notin I}w_i\breve L_i\Bigr)z. \qquad (7c)
--   $$
--   10. **Separating set of Proposition 3.** For $(\hat x,\hat z)$, $\hat I=\{i\in\operatorname{supp}(w) : w_i\hat x_i<w_i(\breve L_i(1-\hat z)+\breve U_i\hat z)\}$.
--
--   These are the objects in which Propositions 1 and 3 and the steps of the proof of Proposition 1 in Appendix A.1 are stated.
--
--   **Formalization Note** The index set $\llbracket\eta\rrbracket=\{1,\dots,\eta\}$ is `Fin η` (0-based) and points $(x,y,z)$ live in `(Fin η → ℝ) × ℝ × ℝ`. $M^\pm(f)$ are defined by their closed forms; that these are the maximum and minimum of $f$ is the companion theorem `mplus_mminus_extremal`. "$i\notin I$" ranges over all of $\llbracket\eta\rrbracket\setminus I$, zero weights included (they contribute $0$). The page states (7b)–(7c) after substituting $\tilde x_i=-x_i$ for negative weights, i.e. for $w>0$ with $L,U$; mapped back this is $\breve L,\breve U$, and (7b) is exactly (6b). Ideality looks at $z$ only, the single integer variable. The LP relaxation of (5) is stored projected to $(x,y,z)$ (the copies are existentially quantified). All declarations sit in a `noncomputable section` because `L̆`, `Ŭ` branch on the sign of a real number.
-- source:
--   arXiv:1811.08359v2, §1.1 (p. 3), §1.3 (p. 4), §2.1 (3a)–(3d) (p. 4), §2.2 (5a)–(5f) (pp. 5–6), §2.3 (6a)–(6c) and Proposition 3 (pp. 6–7), App. A.1 (7a)–(7d) (p. 14)

import Mathlib

namespace ReluMIP.Ideal

noncomputable section

/-! Setting of Anderson, Huchette, Tjandraatmadja, Vielma, *Strong mixed-integer programming
formulations for trained neural networks*, arXiv:1811.08359v2 (IPCO 2019 extended abstract):
§1.1 (p. 3), §1.3 (p. 4), formulations (3), (5), (6) of §2.1–2.3 (pp. 4–6) and system (7) of
App. A.1 (p. 14). Inputs `x ∈ ℝ^η` are `Fin η → ℝ`; the index set `⟦η⟧ = {1, …, η}` is
`Fin η = {0, …, η - 1}`. A point `(x, y, z)` is `p : (Fin η → ℝ) × ℝ × ℝ` with `p.1 = x`,
`p.2.1 = y`, `p.2.2 = z`; a point `(x, y)` of the graph is `q : (Fin η → ℝ) × ℝ`. -/

/-- `ReLU(v) = max{0, v}` (arXiv:1811.08359v2, p. 2). -/
def relu (v : ℝ) : ℝ := max 0 v

/-- The affine function `f(x) = w · x + b` (p. 2). -/
def affineFn {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (x : Fin η → ℝ) : ℝ := ∑ i, w i * x i + b

/-- The box `[L, U] = {x : L ≤ x ≤ U}`. -/
def box {η : ℕ} (L U : Fin η → ℝ) : Set (Fin η → ℝ) := {x | ∀ i, L i ≤ x i ∧ x i ≤ U i}

/-- `gr(ReLU ∘ f; [L, U]) = {(x, ReLU(f(x))) : L ≤ x ≤ U}`, display (2), p. 2. -/
def reluGraph {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : Set ((Fin η → ℝ) × ℝ) :=
  {q | q.1 ∈ box L U ∧ q.2 = relu (affineFn w b q.1)}

/-- `L̆ᵢ = Lᵢ` if `wᵢ ≥ 0`, `Uᵢ` if `wᵢ < 0` (§1.3, p. 4). -/
def Lbrev {η : ℕ} (w L U : Fin η → ℝ) (i : Fin η) : ℝ := if 0 ≤ w i then L i else U i

/-- `Ŭᵢ = Uᵢ` if `wᵢ ≥ 0`, `Lᵢ` if `wᵢ < 0` (§1.3, p. 4). -/
def Ubrev {η : ℕ} (w L U : Fin η → ℝ) (i : Fin η) : ℝ := if 0 ≤ w i then U i else L i

/-- `M⁺(f) = w · Ŭ + b`, the maximum of `f` over `[L, U]` (§1.3, p. 4). -/
def Mplus {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : ℝ := ∑ i, w i * Ubrev w L U i + b

/-- `M⁻(f) = w · L̆ + b`, the minimum of `f` over `[L, U]` (§1.3, p. 4). -/
def Mminus {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : ℝ := ∑ i, w i * Lbrev w L U i + b

/-- `supp(w) = {i ∈ ⟦η⟧ : wᵢ ≠ 0}` (§1.3, p. 4). -/
def supp {η : ℕ} (w : Fin η → ℝ) : Finset (Fin η) := Finset.univ.filter (fun i => w i ≠ 0)

/-- Strict activity: `M⁻(f) < 0 < M⁺(f)` (§1.3, p. 4). -/
def StrictActivity {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : Prop :=
  Mminus w b L U < 0 ∧ 0 < Mplus w b L U

/-- The right-hand side of (6b) for the subset `I`:
`∑_{i ∈ I} wᵢ (xᵢ − L̆ᵢ (1 − z)) + (b + ∑_{i ∉ I} wᵢ Ŭᵢ) z` (p. 6). -/
def rhs6b {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (I : Finset (Fin η))
    (x : Fin η → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ I, w i * (x i - Lbrev w L U i * (1 - z)) + (b + ∑ i ∈ Finset.univ \ I, w i * Ubrev w L U i) * z

/-- The LP relaxation of formulation (6): (6a), (6b) for every `I ⊆ supp(w)`, and (6c) with
`z ∈ [0, 1]` in place of `z ∈ {0, 1}`. -/
def relax6 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : Set ((Fin η → ℝ) × ℝ × ℝ) :=
  {p | affineFn w b p.1 ≤ p.2.1 ∧
    (∀ I : Finset (Fin η), I ⊆ supp w → p.2.1 ≤ rhs6b w b L U I p.1 p.2.2) ∧
    p.1 ∈ box L U ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ 1}

/-- `R` (an LP relaxation in `(x, y, z)`) together with `z ∈ {0, 1}` is a formulation of `S`:
`(x, y) ∈ S` iff some `z ∈ {0, 1}` has `(x, y, z) ∈ R` (p. 3). -/
def IsFormulationFor {η : ℕ} (R : Set ((Fin η → ℝ) × ℝ × ℝ)) (S : Set ((Fin η → ℝ) × ℝ)) : Prop :=
  ∀ x y, (x, y) ∈ S ↔ ∃ z : ℝ, (z = 0 ∨ z = 1) ∧ (x, y, z) ∈ R

/-- A formulation is ideal if the extreme points of its LP relaxation `R` are integral, i.e. have
`z ∈ {0, 1}` (p. 3). -/
def IsIdeal {η : ℕ} (R : Set ((Fin η → ℝ) × ℝ × ℝ)) : Prop :=
  ∀ p ∈ Set.extremePoints ℝ R, p.2.2 = 0 ∨ p.2.2 = 1

/-! Objects specific to this mission (not part of the shared layer). -/

/-- The LP relaxation of the big-M formulation (3) (§2.1, p. 4): (3a) `y ≥ f(x)`,
(3b) `y ≤ f(x) − M⁻(f)(1 − z)`, (3c) `y ≤ M⁺(f) z`, and (3d) with `z ∈ [0, 1]` in place of
`z ∈ {0, 1}`. -/
def relax3 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : Set ((Fin η → ℝ) × ℝ × ℝ) :=
  {p | affineFn w b p.1 ≤ p.2.1 ∧ p.2.1 ≤ affineFn w b p.1 - Mminus w b L U * (1 - p.2.2) ∧
    p.2.1 ≤ Mplus w b L U * p.2.2 ∧ p.1 ∈ box L U ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ 1}

/-- The LP relaxation of the multiple-choice formulation (5) (§2.2, p. 5), projected to `(x, y, z)`:
the points for which some copies `x⁰, x¹ ∈ ℝ^η`, `y⁰, y¹ ∈ ℝ` satisfy
(5a) `(x, y) = (x⁰, y⁰) + (x¹, y¹)`, (5b) `y⁰ = 0 ≥ w · x⁰ + b(1 − z)`,
(5c) `y¹ = w · x¹ + bz ≥ 0`, (5d) `L(1 − z) ≤ x⁰ ≤ U(1 − z)`, (5e) `Lz ≤ x¹ ≤ Uz`, and (5f)
with `z ∈ [0, 1]` in place of `z ∈ {0, 1}`. Note that the constant `b` is scaled by `1 − z` in (5b)
and by `z` in (5c). -/
def relax5 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : Set ((Fin η → ℝ) × ℝ × ℝ) :=
  {p | ∃ x0 x1 : Fin η → ℝ, ∃ y0 y1 : ℝ,
    p.1 = x0 + x1 ∧ p.2.1 = y0 + y1 ∧
    y0 = 0 ∧ ∑ i, w i * x0 i + b * (1 - p.2.2) ≤ 0 ∧
    y1 = ∑ i, w i * x1 i + b * p.2.2 ∧ 0 ≤ y1 ∧
    (∀ i, L i * (1 - p.2.2) ≤ x0 i ∧ x0 i ≤ U i * (1 - p.2.2)) ∧
    (∀ i, L i * p.2.2 ≤ x1 i ∧ x1 i ≤ U i * p.2.2) ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ 1}

/-- The right-hand side of (7c) (App. A.1, p. 14) in general-sign form, for the subset `I`:
`∑_{i ∈ I} wᵢ (xᵢ − Ŭᵢ (1 − z)) + (b + ∑_{i ∉ I} wᵢ L̆ᵢ) z`. For `w ≥ 0` this is the page's
`∑_{i∈I} wᵢxᵢ − ∑_{i∈I} wᵢUᵢ(1 − z) + (b + ∑_{i∉I} wᵢLᵢ) z`. -/
def rhs7c {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (I : Finset (Fin η))
    (x : Fin η → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ I, w i * (x i - Ubrev w L U i * (1 - z)) + (b + ∑ i ∈ Finset.univ \ I, w i * Lbrev w L U i) * z

/-- The linear system (7a)–(7d) (App. A.1, p. 14) in general-sign form: (7a) `y ≥ w · x + b`,
(7b) = (6b) for every `I ⊆ supp(w)`, (7c) `y ≥ rhs7c I` for every `I ⊆ supp(w)`, and
(7d) `(x, y, z) ∈ [L, U] × ℝ≥0 × [0, 1]`. -/
def system7 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : Set ((Fin η → ℝ) × ℝ × ℝ) :=
  {p | p ∈ relax6 w b L U ∧
    ∀ I : Finset (Fin η), I ⊆ supp w → rhs7c w b L U I p.1 p.2.2 ≤ p.2.1}

/-- The separating set of Proposition 3 (p. 7):
`Î = {i ∈ supp(w) : wᵢ x̂ᵢ < wᵢ (L̆ᵢ (1 − ẑ) + Ŭᵢ ẑ)}`. -/
def sepSet {η : ℕ} (w L U : Fin η → ℝ) (xh : Fin η → ℝ) (zh : ℝ) : Finset (Fin η) :=
  (supp w).filter (fun i => w i * xh i < w i * (Lbrev w L U i * (1 - zh) + Ubrev w L U i * zh))

end

end ReluMIP.Ideal


