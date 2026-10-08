-- Prove2me | Definitions.Def_ReluMIP_Facet_Setting
-- name    : ReluMIP_Facet_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:04.778601+00:00
-- url     : https://prove2.me/theorems/0ef222d3-22f4-42e6-adac-6f60b8578eb0
-- title:
--   §1.3, §2.3, App. A.2 — L̆, Ŭ, M±(f), strict activity, formulation (6), facet-defining inequalities and the points of the proof of Proposition 2
-- statement:
--   This module fixes the objects of Anderson, Huchette, Tjandraatmadja and Vielma's facet analysis of the ideal formulation (6) of a single ReLU neuron.
--
--   Let $\eta\in\mathbb N$, a weight vector $w\in\mathbb R^\eta$, a bias $b\in\mathbb R$ and bounds $L,U\in\mathbb R^\eta$. The neuron computes $\mathrm{ReLU}(f(x))$ with $\mathrm{ReLU}(v)=\max\{0,v\}$ and the affine function $f(x)=w\cdot x+b$, over the box $[L,U]=\{x : L\le x\le U\}$. Its graph is $\operatorname{gr}(\mathrm{ReLU}\circ f;[L,U])=\{(x,\mathrm{ReLU}(f(x))) : L\le x\le U\}$.
--
--   1. **Sign-adjusted bounds.** $\breve L_i=L_i$ and $\breve U_i=U_i$ if $w_i\ge 0$; $\breve L_i=U_i$ and $\breve U_i=L_i$ if $w_i<0$.
--   2. **Extreme values of $f$.** $M^+(f)=w\cdot\breve U+b$ and $M^-(f)=w\cdot\breve L+b$ (the maximum and minimum of $f$ over $[L,U]$).
--   3. **Support.** $\operatorname{supp}(w)=\{i : w_i\neq 0\}$.
--   4. **Strict activity.** $M^-(f)<0<M^+(f)$.
--   5. **Formulation (6).** For $I\subseteq\operatorname{supp}(w)$, inequality (6b) reads
--   $$
--   y\le\sum_{i\in I}w_i\bigl(x_i-\breve L_i(1-z)\bigr)+\Bigl(b+\sum_{i\notin I}w_i\breve U_i\Bigr)z .
--   $$
--   The LP relaxation of (6) is the set of $(x,y,z)$ with $y\ge w\cdot x+b$ (6a), (6b) for every $I\subseteq\operatorname{supp}(w)$, $x\in[L,U]$, $y\ge 0$ and $0\le z\le 1$; the points *feasible with respect to (6)* are those of the relaxation with $z\in\{0,1\}$.
--   6. **Formulations and ideality** (as in §1.1): a relaxation $R$ together with $z\in\{0,1\}$ is a formulation of a set $S$ of points $(x,y)$ if $(x,y)\in S$ exactly when $(x,y,z)\in R$ for some $z\in\{0,1\}$; it is ideal if every extreme point of $R$ has $z\in\{0,1\}$.
--   7. **Facet-defining inequality** (standard notion, not defined in the paper): an inequality $g\le 0$ is facet-defining for a set $P$ if it holds on $P$, its face $F=P\cap\{g=0\}$ is nonempty, and $\dim F=\dim P-1$, where the dimension of a set is that of its affine hull.
--   8. **The points of the proof of Proposition 2.** With the sign $\sigma_i=1$ if $w_i\ge0$ and $\sigma_i=-1$ if $w_i<0$, a subset $I$ and a step $\varepsilon$, the $\eta+2$ points are
--   $$
--   p^0=(\breve L,0,0),\qquad p^1=(\breve U,f(\breve U),1),
--   $$
--   $$
--   \tilde p^i=(\breve L+\varepsilon\sigma_i e^i,\,0,\,0)\ (i\notin I),\qquad \tilde p^i=(\breve U-\varepsilon\sigma_i e^i,\,f(\breve U-\varepsilon\sigma_i e^i),\,1)\ (i\in I).
--   $$
--
--   These are the objects in which Proposition 2 and the steps of its proof in Appendix A.2 are stated.
--
--   **Formalization Note** The index set $\llbracket\eta\rrbracket=\{1,\dots,\eta\}$ is `Fin η` (0-based) and points $(x,y,z)$ live in `(Fin η → ℝ) × ℝ × ℝ`. $M^\pm(f)$ are defined by their closed forms. "$i\notin I$" ranges over all of $\llbracket\eta\rrbracket\setminus I$, zero weights included (they contribute $0$). The dimension is the `finrank` of the `vectorSpan`, and $\dim F=\dim P-1$ is written $\dim F+1=\dim P$ so that no natural-number subtraction occurs; nonemptiness of $F$ is required explicitly. The paper's proof takes $w\ge0$ (so $\breve L=L$, $\breve U=U$, $\sigma=1$) "without loss of generality by appropriately interchanging $+$ and $-$"; the points are defined here for every sign pattern. The points are indexed by `Fin 2 ⊕ Fin η`: `inl 0` is $p^0$, `inl 1` is $p^1$, `inr i` is $\tilde p^i$.
-- source:
--   arXiv:1811.08359v2, §1.3 (p. 4), §2.3 formulation (6a)–(6c) and Proposition 2 (p. 6), App. A.2 (p. 15)

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting

namespace ReluMIP.Facet

noncomputable section

/-! Setting of Anderson, Huchette, Tjandraatmadja, Vielma, *Strong mixed-integer programming
formulations for trained neural networks*, arXiv:1811.08359v2 (IPCO 2019 extended abstract):
§1.3 (p. 4) and formulation (6) of §2.3 (p. 6). Inputs `x ∈ ℝ^η` are `Fin η → ℝ`; the index set
`⟦η⟧ = {1, …, η}` is `Fin η = {0, …, η - 1}`. A point `(x, y, z)` is `p : (Fin η → ℝ) × ℝ × ℝ`
with `p.1 = x`, `p.2.1 = y`, `p.2.2 = z`. -/

/-! ## Specific to Proposition 2 and its proof (App. A.2, p. 15) -/

/-- The points feasible with respect to formulation (6), (6a)–(6c): the LP relaxation `relax6`
together with `z ∈ {0, 1}`. -/
def form6 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) : Set ((Fin η → ℝ) × ℝ × ℝ) :=
  {p | p ∈ ReluMIP.Ideal.relax6 w b L U ∧ (p.2.2 = 0 ∨ p.2.2 = 1)}

/-- The inequality `g ≤ 0` is *facet-defining* for the set `P` (standard notion, e.g.
Nemhauser–Wolsey): it is valid on `P`, its face `F = P ∩ {g = 0}` is nonempty, and
`dim F = dim P − 1`, written `dim F + 1 = dim P` to avoid natural-number subtraction. The dimension
of a set is the dimension of its affine hull, i.e. the `finrank` of its `vectorSpan`.
In this mission `g` is always the affine function `(x, y, z) ↦ y − ReluMIP.Ideal.rhs6b(I; x, z)` of an
inequality (6b), and `P` a convex set. -/
def IsFacetDefining {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (g : E → ℝ) : Prop :=
  (∀ p ∈ P, g p ≤ 0) ∧ (P ∩ {p | g p = 0}).Nonempty ∧
    Module.finrank ℝ (vectorSpan ℝ (P ∩ {p | g p = 0})) + 1 = Module.finrank ℝ (vectorSpan ℝ P)

/-- The sign `σᵢ ∈ {+1, −1}` by which a step from `L̆ᵢ` moves into `[Lᵢ, Uᵢ]` (and a step from
`Ŭᵢ` moves out of `[Lᵢ, Uᵢ]`): `σᵢ = 1` if `wᵢ ≥ 0`, `σᵢ = −1` if `wᵢ < 0`. -/
def inward {η : ℕ} (w : Fin η → ℝ) (i : Fin η) : ℝ := if 0 ≤ w i then 1 else -1

/-- The `η + 2` points of the proof of Proposition 2 (App. A.2, p. 15), in general-sign form
(the page takes `w ≥ 0`, so `L̆ = L`, `Ŭ = U`, `σ = 1`), for a subset `I` and a step `ε`:
* `Sum.inl 0 ↦ p⁰ = (L̆, 0, 0)`;
* `Sum.inl 1 ↦ p¹ = (Ŭ, f(Ŭ), 1)`;
* `Sum.inr i ↦ p̃ⁱ = (L̆ + ε σᵢ eⁱ, 0, 0)` for `i ∉ I`, and
  `p̃ⁱ = (Ŭ − ε σᵢ eⁱ, f(Ŭ − ε σᵢ eⁱ), 1)` for `i ∈ I`. -/
def facetPts {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (I : Finset (Fin η)) (ε : ℝ) : Fin 2 ⊕ Fin η → (Fin η → ℝ) × ℝ × ℝ
  | Sum.inl k =>
      if k = 0 then (ReluMIP.Ideal.Lbrev w L U, 0, 0)
      else (ReluMIP.Ideal.Ubrev w L U, ReluMIP.Ideal.affineFn w b (ReluMIP.Ideal.Ubrev w L U), 1)
  | Sum.inr i =>
      if i ∈ I then
        (ReluMIP.Ideal.Ubrev w L U - Pi.single i (ε * inward w i),
          ReluMIP.Ideal.affineFn w b (ReluMIP.Ideal.Ubrev w L U - Pi.single i (ε * inward w i)), 1)
      else (ReluMIP.Ideal.Lbrev w L U + Pi.single i (ε * inward w i), 0, 0)

end

end ReluMIP.Facet


