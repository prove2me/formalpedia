-- Prove2me | Definitions.Def_ModularCurve_X0MqResolvedTable
-- name    : ModularCurve_X0MqResolvedTable
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/7740c03f-af51-54ea-a459-df8e4522290a
-- title:
--   Component table of the resolved special fibre of X0​(Mq)
-- statement:
--   Fix a finite type $\iota$ and a function $e : \iota \to \mathbb{N}$. [`ModularCurve.X0MqComponents e`](../def/ModularCurve_X0MqResolvedTable.html#L11) is the index type $\mathrm{Fin}\,2 \oplus \bigl(\Sigma_{x:\iota}\,\mathrm{Fin}(e_x-1)\bigr)$: two distinguished components, written here $Z_0, Z_1$, together with, for each $x \in \iota$, a chain of $e_x - 1$ further components indexed by $0,\dots,e_x-2$ (truncated natural subtraction, so $e_x \le 1$ contributes nothing).
--
--   [`ModularCurve.x0MqAdj e`](../def/ModularCurve_X0MqResolvedTable.html#L13) is the $\mathbb{N}$-valued adjacency function on this index type: $a(Z_i,Z_j)$ for $i \ne j$ is the number of $x \in \iota$ with $e_x = 1$, and $a(Z_i,Z_i) = 0$; $a(Z_i,(x,k)) = a((x,k),Z_i)$ equals $1$ exactly when $i = 0$ and $k = 0$, or $i = 1$ and $k = e_x - 2$, and is $0$ otherwise; $a((x,k),(x',k'))$ equals $1$ exactly when $x = x'$ and $k,k'$ are consecutive, so that in particular the diagonal vanishes. The lemma [`ModularCurve.x0MqAdj_symm`](../def/ModularCurve_X0MqResolvedTable.html#L19) records that $a$ is symmetric.
--
--   [`ModularCurve.x0MqResolvedTable e`](../def/ModularCurve_X0MqResolvedTable.html#L31) is the resulting term of the project's structure [`MazurRapoportAppendix.SpecialFibreComponentTable`](../def/AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers.html#L42): all multiplicities are $1$, and the intersection pairing is $\mathrm{inter}(i,j) = a(i,j)$ for $i \ne j$ and $\mathrm{inter}(i,i) = -\sum_{j} a(i,j)$. The structure's fields are discharged as part of the definition: positivity of the multiplicities, symmetry of the pairing, and the relation $\sum_j \mathrm{inter}(i,j)\,\mathrm{mult}(j) = 0$ for every $i$, which here reduces to the fact that each row of $\mathrm{inter}$ sums to zero. No geometric interpretation is asserted: the declarations produce purely combinatorial data of the shape required by the component-group machinery.
--
--   **Relation to Mathlib.** Mathlib has no notion of a special-fibre component table or of the associated component group; `SpecialFibreComponentTable` is the project's own structure, and this module supplies one particular such table.
--
--   **Where it is used.** This table is the combinatorial input to the Mazur–Rapoport construction of [`MazurRapoportAppendix.AppendixComponentGroup`](../def/AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers.html#L122), the quotient $\ker\beta / \operatorname{im}\alpha$ attached to a component table. The shape chosen here — two components meeting at the points $x$ with $e_x = 1$, joined by chains of length $e_x - 1$ elsewhere — is that of the minimal regular model of $X_0(Mq)$ at $q$, whose component group enters the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_X0MqResolvedTable.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve
open MazurRapoportAppendix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev X0MqComponents (e : ι → ℕ) : Type _ := Fin 2 ⊕ (Σ x : ι, Fin (e x - 1))

def x0MqAdj (e : ι → ℕ) : X0MqComponents e → X0MqComponents e → ℕ
  | .inl i, .inl j => if i ≠ j then (Finset.univ.filter fun x => e x = 1).card else 0
  | .inl i, .inr p => if (i = 0 ∧ p.2.val = 0) ∨ (i = 1 ∧ p.2.val = e p.1 - 2) then 1 else 0
  | .inr p, .inl i => if (i = 0 ∧ p.2.val = 0) ∨ (i = 1 ∧ p.2.val = e p.1 - 2) then 1 else 0
  | .inr p, .inr p' => if p.1 = p'.1 ∧ (p.2.val + 1 = p'.2.val ∨ p'.2.val + 1 = p.2.val) then 1 else 0

theorem x0MqAdj_symm (e : ι → ℕ) (i j : X0MqComponents e) : x0MqAdj e i j = x0MqAdj e j i := by
  rcases i with i | p <;> rcases j with j | p'
  · simp only [x0MqAdj, ne_comm]
  · rfl
  · rfl
  · simp only [x0MqAdj]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩

def x0MqResolvedTable (e : ι → ℕ) :
    SpecialFibreComponentTable (X0MqComponents e) where
  mult _ := 1
  inter i j := (x0MqAdj e i j : ℤ) - if i = j then ∑ j', (x0MqAdj e i j' : ℤ) else 0
  mult_pos _ := Nat.one_pos
  inter_symm i j := by
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), x0MqAdj_symm]
  fibre_inter_zero i := by
    simp only [Nat.cast_one, mul_one, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

end ModularCurve


