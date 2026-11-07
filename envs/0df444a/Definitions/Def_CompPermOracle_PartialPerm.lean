-- Prove2me | Definitions.Def_CompPermOracle_PartialPerm
-- name    : CompPermOracle_PartialPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:49:35.418204+00:00
-- url     : https://prove2.me/theorems/dafa84ef-a36c-4259-b8d2-7bcaaa8b0ea5
-- title:
--   Partial permutations of $[N]$, their size, levels and the extension $f[x\mapsto y]$
-- statement:
--   A **partial permutation** is an injective partial function $f:D\hookrightarrow[N]$ with $D\subseteq[N]$. Write $\mathrm{dom}(f)=D$, $\mathrm{im}(f)=f(D)$ and $|f|=|D|$. The set $\mathcal I_r$ consists of the partial permutations of size $r$. For $h$ a partial permutation, $X_h=[N]\setminus\mathrm{dom}(h)$ and $Y_h=[N]\setminus\mathrm{im}(h)$. If $x\notin\mathrm{dom}(f)$ and $y\notin\mathrm{im}(f)$, then $f[x\mapsto y]$ adds the pair $(x,y)$ to $f$.
--
--   Partial permutations are the basis of the database register of the compressed oracle.
--
--   **Formalization Note** $[N]$ is `Fin N`, and a partial permutation is Mathlib's `PEquiv (Fin N) (Fin N)`, whose `symm` is $f^{-1}$. The file gives it a `Fintype` instance. `addPair` is total: it returns $f$ when $x\in\mathrm{dom}(f)$ or $y\in\mathrm{im}(f)$, and no statement of the mission reaches that branch.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Definition 3.4, p.7; p.20

import Mathlib

namespace CompPermOracle

/-- A partial permutation of `[N]`: an injective partial function `f : D ↪ [N]`, `D ⊆ [N]`
(Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Definition 3.4, p.7).

**Formalization Note.** `[N]` is `Fin N` (0-based). A partial permutation is Mathlib's `PEquiv`:
`f x = some y` says `x ∈ dom(f)` and `f(x) = y`, and `f.symm` is `f⁻¹`. -/
abbrev PartialPerm (N : ℕ) := PEquiv (Fin N) (Fin N)

/-- The finite type of partial permutations: pairs of mutually inverse partial functions. -/
instance instFintypePartialPerm (N : ℕ) : Fintype (PartialPerm N) :=
  Fintype.ofEquiv
    {p : (Fin N → Option (Fin N)) × (Fin N → Option (Fin N)) //
      ∀ a b, p.2 b = some a ↔ p.1 a = some b}
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun f => ⟨(f.toFun, f.invFun), f.inv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `x ∉ dom(f)`. -/
def NotInDom {N : ℕ} (f : PartialPerm N) (x : Fin N) : Prop := f x = none

instance {N : ℕ} (f : PartialPerm N) (x : Fin N) : Decidable (NotInDom f x) :=
  inferInstanceAs (Decidable (f x = none))

/-- `y ∉ im(f)`. -/
def NotInIm {N : ℕ} (f : PartialPerm N) (y : Fin N) : Prop := f.symm y = none

instance {N : ℕ} (f : PartialPerm N) (y : Fin N) : Decidable (NotInIm f y) :=
  inferInstanceAs (Decidable (f.symm y = none))

/-- The level or degree `|f| = |dom(f)|`. -/
def size {N : ℕ} (f : PartialPerm N) : ℕ :=
  (Finset.univ.filter fun x => ¬ NotInDom f x).card

/-- `ℐ_r`, the partial permutations of size `r` (arXiv:2609.28469, Definition 3.4, p.7). -/
def levelSet (N r : ℕ) : Finset (PartialPerm N) :=
  Finset.univ.filter fun f => size f = r

/-- `X_h = [N] \ dom(h)` (arXiv:2609.28469, p.20). -/
def freeDom {N : ℕ} (h : PartialPerm N) : Finset (Fin N) :=
  Finset.univ.filter fun x => NotInDom h x

/-- `Y_h = [N] \ im(h)` (arXiv:2609.28469, p.7). -/
def freeIm {N : ℕ} (h : PartialPerm N) : Finset (Fin N) :=
  Finset.univ.filter fun y => NotInIm h y

/-- `f[x ↦ y]`: the partial permutation obtained by adding the pair `(x, y)` to `f`
(arXiv:2609.28469, Definition 3.4, p.7).

**Formalization Note.** The source defines it only when `x ∉ dom(f)` and `y ∉ im(f)`, and every
use in this mission has those two conditions. Outside them this total function returns `f`. -/
def addPair {N : ℕ} (f : PartialPerm N) (x y : Fin N) : PartialPerm N :=
  if hc : f x = none ∧ f.symm y = none then
    { toFun := fun u => if u = x then some y else f u
      invFun := fun v => if v = y then some x else f.symm v
      inv := by
        intro a b
        have key : ∀ a b, f.symm b = some a ↔ f a = some b := fun a b => f.inv a b
        show (if b = y then some x else f.symm b) = some a ↔
          (if a = x then some y else f a) = some b
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
  else f

end CompPermOracle


