-- Prove2me | Definitions.Def_RobertsonSeymour2010_GM23_Immersion_QuasiOrders
-- name    : RobertsonSeymour2010_GM23_Immersion_QuasiOrders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:46.96399+00:00
-- url     : https://prove2.me/theorems/1802b5e5-0ea3-4871-aa6b-69b8859b51ac
-- title:
--   Quasi-orders, well-quasi-orders and ideals (pp. 3, 6); proper quasi-orders (p. 4); shadows and their lexicographic order (pp. 6–7)
-- statement:
--   This module fixes the order-theoretic objects of Section 3 of *Graph Minors XXIII*. All quasi-orders live inside one ambient set $X$, so that different quasi-orders can be compared by inclusion.
--
--   1. **Quasi-order.** A quasi-order $\Omega$ is a pair $(E(\Omega),\le)$ where $E(\Omega)\subseteq X$ and $\le$ is reflexive and transitive on $E(\Omega)$. It is a **well-quasi-order** if for every sequence $x_1,x_2,\dots$ of elements of $E(\Omega)$ there are $j>i\ge1$ with $x_i\le x_j$.
--
--   2. **Sub-order and ideal.** $\Omega\subseteq\Omega'$ means $E(\Omega)\subseteq E(\Omega')$ and, for $x,y\in E(\Omega)$, $x\le y$ in $\Omega$ iff $x\le y$ in $\Omega'$. $\Omega$ is an **ideal** of $\Omega'$, written $\Omega\le\Omega'$, if $\Omega\subseteq\Omega'$ and there are no $x\in E(\Omega')\setminus E(\Omega)$ and $y\in E(\Omega)$ with $x\le y$ in $\Omega'$. $\Omega<\Omega'$ means $\Omega\le\Omega'$ and $\Omega\ne\Omega'$; two quasi-orders are equal when they have the same ground set and the same order on it.
--
--   3. **Proper quasi-order.** Fix two disjoint countably infinite sets $\Gamma_1,\Gamma_2\subseteq X$ of "new" elements. A quasi-order $\Omega$ is **proper** if $E(\Omega)\cap(\Gamma_1\cup\Gamma_2)$ is finite and there are no $\gamma\in E(\Omega)\cap(\Gamma_1\cup\Gamma_2)$ and $x\in E(\Omega)$ with $x\ne\gamma$ and $x\le\gamma$ or $\gamma\le x$.
--
--   4. **Shadow.** A shadow is a finite sequence
--   $$\Sigma=(\Omega_\infty, m, \Omega_m,\Omega_{m-1},\dots,\Omega_1, R_2, R_1)$$
--   where $m\ge2$ is an integer, $R_2$ is a finite subset of $\Gamma_2$, $R_1$ a finite subset of $\Gamma_1$, and $\Omega_\infty,\Omega_m,\dots,\Omega_1$ are proper well-quasi-orders, none with an element in $\Gamma_1\cup\Gamma_2$.
--
--   5. **Order on shadows.** For shadows $\Sigma,\Sigma'$ (primed components for $\Sigma'$), $\Sigma\le\Sigma'$ if one of the following holds:
--      - $\Omega_\infty<\Omega'_\infty$;
--      - $\Omega_\infty=\Omega'_\infty$ and $m<m'$;
--      - $\Omega_\infty=\Omega'_\infty$, $m=m'$, and for some $1\le k\le m$, $\Omega_k<\Omega'_k$ and $\Omega_i=\Omega'_i$ for $k<i\le m$;
--      - $\Omega_\infty=\Omega'_\infty$, $m=m'$, $\Omega_i=\Omega'_i$ for $1\le i\le m$, and $R_2\subsetneq R'_2$;
--      - $\Omega_\infty=\Omega'_\infty$, $m=m'$, $\Omega_i=\Omega'_i$ for $1\le i\le m$, $R_2=R'_2$ and $R_1\subseteq R'_1$.
--
--      $\Sigma<\Sigma'$ means $\Sigma\le\Sigma'$ and $\Sigma\ne\Sigma'$.
--
--   These notions are the well-foundedness devices of the paper's induction (results 3.1 and 3.2).
--
--   **Formalization Note.** A quasi-order is the structure `QO X` with a ground set `carrier : Set X` and a relation `le : X → X → Prop`; only the restriction of `le` to `carrier` matters, so equality of quasi-orders is the predicate `QO.Same` (same ground set, same order on it) rather than equality of structures. Sequences are indexed from $0$. In a shadow, $\Omega_1,\dots,\Omega_m$ is a family `Ω : ℕ → QO X`, read only at the indices $1,\dots,m$; equality of shadows (`Shadow.Same`) compares only those indices. Properness is redundant once no element lies in $\Gamma_1\cup\Gamma_2$, but it is kept as the paper states it.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), Section 1, p. 3 (quasi-order); Section 2, p. 4 (proper); Section 3, pp. 6–7 (ideal, shadow, order on shadows)

import Mathlib

namespace RobertsonSeymour2010.GM23.Immersion

/-- A quasi-order (p. 3) whose ground set `E(Ω)` is a subset `carrier` of an ambient type `X`,
with a relation `le` that is reflexive and transitive on `carrier`. Values of `le` outside
`carrier` are irrelevant. The ambient type lets different quasi-orders be compared by inclusion of
their ground sets, as Section 3 does. -/
structure QO (X : Type) where
  /-- The ground set `E(Ω)`. -/
  carrier : Set X
  /-- The relation `≤` (only its restriction to `carrier` matters). -/
  le : X → X → Prop
  /-- Reflexive on the ground set. -/
  le_refl : ∀ x ∈ carrier, le x x
  /-- Transitive on the ground set. -/
  le_trans : ∀ x ∈ carrier, ∀ y ∈ carrier, ∀ z ∈ carrier, le x y → le y z → le x z

namespace QO

variable {X : Type}

/-- `Ω` is a well-quasi-order (p. 3): for every sequence `x₀, x₁, …` of elements of `E(Ω)` there
are `i < j` with `xᵢ ≤ xⱼ`. -/
def IsWQO (Ω : QO X) : Prop :=
  ∀ x : ℕ → X, (∀ n, x n ∈ Ω.carrier) → ∃ i j, i < j ∧ Ω.le (x i) (x j)

/-- `Ω ⊆ Ω'` (p. 6): `E(Ω) ⊆ E(Ω')` and the two orders agree on `E(Ω)`. -/
def Sub (Ω Ω' : QO X) : Prop :=
  Ω.carrier ⊆ Ω'.carrier ∧
    ∀ x ∈ Ω.carrier, ∀ y ∈ Ω.carrier, (Ω.le x y ↔ Ω'.le x y)

/-- Equality of quasi-orders as pairs `(E(Ω), ≤)`: same ground set and the same order on it. -/
def Same (Ω Ω' : QO X) : Prop :=
  Ω.carrier = Ω'.carrier ∧
    ∀ x ∈ Ω.carrier, ∀ y ∈ Ω.carrier, (Ω.le x y ↔ Ω'.le x y)

/-- `Ω ≤ Ω'`, "Ω is an ideal of Ω'" (p. 6): `Ω ⊆ Ω'` and `Ω` is closed downwards, i.e. there are no
`x ∈ E(Ω') \ E(Ω)` and `y ∈ E(Ω)` with `x ≤ y` in `Ω'`. -/
def IsIdeal (Ω Ω' : QO X) : Prop :=
  Sub Ω Ω' ∧ ¬ ∃ x ∈ Ω'.carrier \ Ω.carrier, ∃ y ∈ Ω.carrier, Ω'.le x y

/-- `Ω < Ω'` (p. 6): `Ω ≤ Ω'` and `Ω ≠ Ω'` (as quasi-orders, i.e. `¬ Same Ω Ω'`). -/
def IsProperIdeal (Ω Ω' : QO X) : Prop :=
  IsIdeal Ω Ω' ∧ ¬ Same Ω Ω'

/-- A quasi-order is proper with respect to the "new" sets `Γ₁, Γ₂` (p. 4) if
`E(Ω) ∩ (Γ₁ ∪ Γ₂)` is finite and there are no `γ ∈ E(Ω) ∩ (Γ₁ ∪ Γ₂)` and `x ∈ E(Ω)` with
`x ≠ γ` such that `x ≤ γ` or `γ ≤ x`. -/
def IsProper (Γ₁ Γ₂ : Set X) (Ω : QO X) : Prop :=
  (Ω.carrier ∩ (Γ₁ ∪ Γ₂)).Finite ∧
    ¬ ∃ γ ∈ Ω.carrier ∩ (Γ₁ ∪ Γ₂), ∃ x ∈ Ω.carrier, x ≠ γ ∧ (Ω.le x γ ∨ Ω.le γ x)

end QO

/-- A shadow (p. 6) relative to the "new" sets `Γ₁, Γ₂ ⊆ X`: a finite sequence
`(Ω_∞, m, Ω_m, …, Ω_1, R₂, R₁)` where `m ≥ 2`, `R₂` is a finite subset of `Γ₂`, `R₁` a finite
subset of `Γ₁`, and `Ω_∞, Ω_m, …, Ω_1` are proper well-quasi-orders, each with no element in
`Γ₁ ∪ Γ₂`. The family `Ω` is indexed by `ℕ` and only its values at `1, …, m` are part of the
shadow. -/
structure Shadow (X : Type) (Γ₁ Γ₂ : Set X) where
  /-- `Ω_∞`. -/
  Ωinf : QO X
  /-- The integer `m`. -/
  m : ℕ
  /-- `Ω_h` for `1 ≤ h ≤ m` (other indices are ignored). -/
  Ω : ℕ → QO X
  /-- `R₂`. -/
  R₂ : Set X
  /-- `R₁`. -/
  R₁ : Set X
  two_le_m : 2 ≤ m
  R₂_finite : R₂.Finite
  R₂_subset : R₂ ⊆ Γ₂
  R₁_finite : R₁.Finite
  R₁_subset : R₁ ⊆ Γ₁
  Ωinf_wqo : Ωinf.IsWQO
  Ωinf_proper : Ωinf.IsProper Γ₁ Γ₂
  Ωinf_avoid : ∀ x ∈ Ωinf.carrier, x ∉ Γ₁ ∪ Γ₂
  Ω_wqo : ∀ h, 1 ≤ h → h ≤ m → (Ω h).IsWQO
  Ω_proper : ∀ h, 1 ≤ h → h ≤ m → (Ω h).IsProper Γ₁ Γ₂
  Ω_avoid : ∀ h, 1 ≤ h → h ≤ m → ∀ x ∈ (Ω h).carrier, x ∉ Γ₁ ∪ Γ₂

namespace Shadow

variable {X : Type} {Γ₁ Γ₂ : Set X}

/-- Equality of shadows as finite sequences: `Ω_∞` agree (as quasi-orders), `m = m'`, `Ω_i` and
`Ω'_i` agree for `1 ≤ i ≤ m`, `R₂ = R'₂` and `R₁ = R'₁`. -/
def Same (S T : Shadow X Γ₁ Γ₂) : Prop :=
  S.Ωinf.Same T.Ωinf ∧ S.m = T.m ∧ (∀ i, 1 ≤ i → i ≤ S.m → (S.Ω i).Same (T.Ω i)) ∧
    S.R₂ = T.R₂ ∧ S.R₁ = T.R₁

/-- The lexicographic order `Σ ≤ Σ'` on shadows (pp. 6–7): one of
* `Ω_∞ < Ω'_∞`;
* `Ω_∞ = Ω'_∞` and `m < m'`;
* `Ω_∞ = Ω'_∞`, `m = m'`, and for some `1 ≤ k ≤ m`, `Ω_k < Ω'_k` and `Ω_i = Ω'_i` for `k < i ≤ m`;
* `Ω_∞ = Ω'_∞`, `m = m'`, `Ω_i = Ω'_i` for `1 ≤ i ≤ m`, and `R₂ ⊊ R'₂`;
* `Ω_∞ = Ω'_∞`, `m = m'`, `Ω_i = Ω'_i` for `1 ≤ i ≤ m`, `R₂ = R'₂` and `R₁ ⊆ R'₁`. -/
def Le (S T : Shadow X Γ₁ Γ₂) : Prop :=
  S.Ωinf.IsProperIdeal T.Ωinf ∨
  (S.Ωinf.Same T.Ωinf ∧ S.m < T.m) ∨
  (S.Ωinf.Same T.Ωinf ∧ S.m = T.m ∧
    ∃ k, 1 ≤ k ∧ k ≤ S.m ∧ (S.Ω k).IsProperIdeal (T.Ω k) ∧
      ∀ i, k < i → i ≤ S.m → (S.Ω i).Same (T.Ω i)) ∨
  (S.Ωinf.Same T.Ωinf ∧ S.m = T.m ∧ (∀ i, 1 ≤ i → i ≤ S.m → (S.Ω i).Same (T.Ω i)) ∧
    S.R₂ ⊂ T.R₂) ∨
  (S.Ωinf.Same T.Ωinf ∧ S.m = T.m ∧ (∀ i, 1 ≤ i → i ≤ S.m → (S.Ω i).Same (T.Ω i)) ∧
    S.R₂ = T.R₂ ∧ S.R₁ ⊆ T.R₁)

/-- `Σ < Σ'` (p. 7): `Σ ≤ Σ'` and `Σ ≠ Σ'`. -/
def Lt (S T : Shadow X Γ₁ Γ₂) : Prop := Le S T ∧ ¬ Same S T

end Shadow

end RobertsonSeymour2010.GM23.Immersion


