-- Prove2me | Definitions.Def_AKSSorting_Core_Rbeta
-- name    : AKSSorting_Core_Rbeta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:57:51.41728+00:00
-- url     : https://prove2.me/theorems/eb11110c-f84e-4da3-8c3a-3b4541ea8d3a
-- title:
--   Trimmed sets A^{−β} and the separation relation R^β_G(t₁, t₂) (Definition 8.1)
-- statement:
--   Let $A=\{a_0<a_1<\dots<a_m\}$ be a finite subset of a linearly ordered set and $\beta>0$. The **trimmed set** is
--   $$ A^{-\beta}=\{a_{[\beta]},a_{[\beta]+1},\dots,a_{m-[\beta]}\}, $$
--   where $[\beta]$ is the integer part of $\beta$: the $[\beta]$ smallest and the $[\beta]$ largest elements are removed (the set is empty when $2[\beta]>m$).
--
--   Let $G$ be a **position**, an injective assignment of contents to registers, and write $\mathrm{Cont}_G(X)=\{G(R): R\in X\}$. For a chain $C$ and nodes $t_1<t_2$ of its level, $R^\beta_G(t_1,t_2)$ is the statement
--   $$ \forall x\in \mathrm{Cont}_G(C(t_1))^{-\beta},\ \forall y\in\mathrm{Cont}_G(C(t_2))^{-\beta}:\ x<y . $$
--
--   It says that, up to $[\beta]$ outliers at each end, the contents of the node $t_1$ lie below those of $t_2$.
--
--   **Formalization Note** The element $a\in A$ has index $\#\{b\in A: b<a\}$; it is kept iff $[\beta]\le$ index and index $+[\beta]+1\le|A|$ (i.e. index $\le m-[\beta]$). $[\beta]$ is `Nat.floor`, which equals the integer part for $\beta>0$. The paper typesets the trimmed set in $R^\beta_G$ as an overlined $\mathrm{Cont}_G(C(t))^\beta$; it is read as $\mathrm{Cont}_G(C(t))^{-\beta}$ of the same definition.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 13, Definition 8.1

import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain

namespace AKSSorting.Core

variable {α : Type} [LinearOrder α]

/-- `A^{-β}` (Ajtai–Komlós–Szemerédi 1983, Definition 8.1, p. 13): writing
`A = {a₀ < a₁ < ⋯ < a_m}`, `A^{-β} = {a_{[β]}, a_{[β]+1}, …, a_{m-[β]}}`, i.e. `A` with its `[β]`
smallest and `[β]` largest elements removed (`[β] = ⌊β⌋`). An element `a ∈ A` has index
`#{b ∈ A | b < a}`; it is kept iff `[β] ≤ index` and `index ≤ m - [β]`, i.e.
`index + [β] + 1 ≤ |A|`. -/
noncomputable def trimmed (β : ℝ) (A : Finset α) : Finset α :=
  A.filter fun a =>
    ⌊β⌋₊ ≤ (A.filter fun b => b < a).card ∧ (A.filter fun b => b < a).card + ⌊β⌋₊ + 1 ≤ A.card

/-- `R^β_G(t₁, t₂)` (Definition 8.1, p. 13): for a position `G`, a chain `C` and nodes `t₁, t₂`,
every element of `Cont_G(C(t₁))^{-β}` is smaller than every element of `Cont_G(C(t₂))^{-β}`,
where `Cont_G(X) = G(X)` is the set of contents of the registers in `X`. -/
def Rbeta {R : Type} [DecidableEq R] {i : ℕ} (G : R → α) (C : Fin (2 ^ i) → Finset R) (β : ℝ)
    (t₁ t₂ : Fin (2 ^ i)) : Prop :=
  ∀ x ∈ trimmed β ((C t₁).image G), ∀ y ∈ trimmed β ((C t₂).image G), x < y

end AKSSorting.Core


