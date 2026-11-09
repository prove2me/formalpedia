-- Prove2me | Definitions.Def_WeldedPath_InjDb
-- name    : WeldedPath_InjDb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:42.044642+00:00
-- url     : https://prove2.me/theorems/f780a46b-bdbd-4d95-a04b-7c1878f340f9
-- title:
--   Injective databases $\mathcal I_s$, their size and the record projectors
-- statement:
--   An **injective database** over $[s]$ is a partial injective function $I:[s]\to[s]\cup\{\bot\}$; $\mathcal I_s$ is the set of them, $\mathrm{Dom}(I)$ and $\mathrm{Im}(I)$ exclude $\bot$, and the **size** is $|I|=|\mathrm{Dom}(I)|$. For $x\notin\mathrm{Dom}(I)$ and $y\notin\mathrm{Im}(I)$, $I[x\to y]$ adds the record $x\mapsto y$. A permutation $\phi$ **extends** $I$ ($\phi\succeq I$) when $\phi(x)=I(x)$ for all $x\in\mathrm{Dom}(I)$. The Hilbert space $\mathcal H(\mathcal I_s)$ has basis $\{|I\rangle\}$, and
--   $$
--   \Pi_{\le t,\mathrm I}=\sum_{I:|I|\le t}|I\rangle\langle I|
--   $$
--   projects on databases with at most $t$ records.
--
--   Databases record what an algorithm has learned about a random permutation in the compressed-oracle method.
--
--   **Formalization Note** $[s]$ is `Fin s` (0-based); a database is Mathlib's `PEquiv`. The source defines $I[x\to y]$ for all $x$ and $y$; this file defines only the case of adding a fresh record, the only one used. Record projectors are diagonal projectors `diagProj` on the full register.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §2, p.9

import Mathlib
import Definitions.Def_WeldedPath_opTensor

namespace WeldedPath

/-- The injective databases `I_s` over `[s]`: partial injective functions `I : [s] → [s] ∪ {⊥}`
(Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, arXiv:2611.05912 (sha256 b31400a0…),
§2, p.9).

**Formalization Note.** `[s]` is `Fin s` (0-based). A database is Mathlib's `PEquiv`: `I x = some y`
says `x ∈ Dom(I)` and `I(x) = y`, `I x = none` says `I(x) = ⊥`, and `I.symm` is `I^{-1}`. -/
abbrev InjDb (s : ℕ) := PEquiv (Fin s) (Fin s)

/-- The finite type of injective databases. -/
instance instFintypeInjDb (s : ℕ) : Fintype (InjDb s) :=
  Fintype.ofEquiv
    {p : (Fin s → Option (Fin s)) × (Fin s → Option (Fin s)) //
      ∀ a b, p.2 b = some a ↔ p.1 a = some b}
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun f => ⟨(f.toFun, f.invFun), f.inv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

namespace InjDb

variable {s : ℕ}

/-- The size `|I| = |Dom(I)|` (arXiv:2611.05912 (sha256 b31400a0…), p.9). -/
def size (I : InjDb s) : ℕ := (Finset.univ.filter fun x => (I x).isSome).card

/-- `I[x → y]` for `x ∉ Dom(I)` and `y ∉ Im(I)`: the database `I` with the record `x ↦ y` added
(arXiv:2611.05912 (sha256 b31400a0…), p.9).

**Formalization Note.** The source defines `I[x → y]` for all `x` and `y ∈ [s] ∪ {⊥}`, overwriting
`x` and deleting a colliding record. Every use in this mission has `x ∉ Dom(I)` and
`y ∉ Im(I)`, where the definition adds the pair; outside these conditions this total function
returns `I`, a value that is never used. -/
def addPair (I : InjDb s) (x y : Fin s) : InjDb s :=
  if hc : I x = none ∧ I.symm y = none then
    { toFun := fun u => if u = x then some y else I u
      invFun := fun v => if v = y then some x else I.symm v
      inv := by
        intro a b
        have key : ∀ a b, I.symm b = some a ↔ I a = some b := fun a b => I.inv a b
        show (if b = y then some x else I.symm b) = some a ↔
          (if a = x then some y else I a) = some b
        by_cases hb : b = y <;> by_cases ha : a = x
        · simp [hb, ha]
        · subst hb
          have hax : ¬ x = a := fun h => ha h.symm
          simp only [if_true, ha, if_false, Option.some.injEq, hax, false_iff]
          intro h
          have := (key a b).2 h
          rw [hc.2] at this
          exact absurd this (by simp)
        · subst ha
          have hby : ¬ y = b := fun h => hb h.symm
          simp only [hb, if_false, if_true, Option.some.injEq, hby, iff_false]
          intro h
          have := (key a b).1 h
          rw [hc.1] at this
          exact absurd this (by simp)
        · simp only [hb, ha, if_false]
          exact key a b }
  else I

/-- `ϕ ⪰ I`: the permutation `ϕ` extends the database `I` (arXiv:2611.05912 (sha256 b31400a0…),
p.9 and p.12). -/
def Extends (ϕ : Equiv.Perm (Fin s)) (I : InjDb s) : Prop := ∀ x y, I x = some y → ϕ x = y

instance (ϕ : Equiv.Perm (Fin s)) (I : InjDb s) : Decidable (Extends ϕ I) :=
  inferInstanceAs (Decidable (∀ x y, I x = some y → ϕ x = y))

end InjDb

/-- The diagonal projector `Σ_{p : P p} |p⟩⟨p|` onto the basis states satisfying `P`; with
`P p := |I| ≤ t` for the database component `I` of `p` it is `Π_{≤t,I}` (arXiv:2611.05912
(sha256 b31400a0…), p.9), tensored with the identity on the other registers. -/
noncomputable def diagProj {X : Type*} [Fintype X] [DecidableEq X] (P : X → Prop)
    [DecidablePred P] : Hil X →L[ℂ] Hil X :=
  ∑ p ∈ Finset.univ.filter P, ketBra (ket p) (ket p)

end WeldedPath


