-- Prove2me | Definitions.Def_MSKleene_Recognizable
-- name    : MSKleene_Recognizable
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:27:15.871069+00:00
-- url     : https://prove2.me/theorems/0d5b6026-36b6-48ef-9349-aca7eff9cc75
-- title:
--   Recognizable and $s$-recognizable languages
-- statement:
--   **Recognizability** for subsets of a many-sorted $\Sigma$-algebra (Definitions 2.28, 2.55).
--
--   A full $S$-sorted subset `L` of `A` is **recognizable** (`IsRecognizable`) when there are a finite $\Sigma$-algebra `B`, a homomorphism `f : A → B`, and an $S$-sorted subset `M` of `B` with `f⁻¹[M] = L` sortwise. For a single sort `s`, a language `L ⊆ A_s` is **$s$-recognizable** (`sRecognizable`) when there are a finite `B`, a homomorphism `f`, and `M ⊆ B_s` with `f_s⁻¹[M] = L`.
--
--   `Recognizable A` and `RecS A s` collect these. The mission goal concerns `RecS (freeAlgebra sig X) s`, i.e. $\mathrm{Rec}_s(\mathbf{T}_\Sigma(X))$.
--
--   **Formalization Note** A $\Sigma$-algebra is finite (`Algebra.Finite`) when the disjoint union of its carrier is finite; with `S` finite this is equivalent to every component being finite.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026, https://arxiv.org/abs/1808.08217 (predecessor CVCL20)

/-
Recognizability for subsets of a many-sorted `Σ`-algebra (Definitions 2.28, 2.55).

A subset is **recognizable** when it is the sortwise preimage of a subset of a
*finite* `Σ`-algebra under a homomorphism; **`s`-recognizable** is the same at a
single sort `s`. `Rec_s(𝐓_Σ(X))` is the object of interest for the mission goal.
-/
import Definitions.Def_MSKleene_Core
import Mathlib.Data.Set.Basic

namespace MSKleene

universe u

variable {S : Type u} {sig : Signature S}

/-- A `Σ`-algebra is finite when the disjoint union of its carrier is finite
(Definition 2.31). -/
def Algebra.Finite (B : Algebra sig) : Prop := SFinite B.carrier

/-- `L` (a full `S`-sorted subset of `A`) is **recognizable**: there are a
finite `Σ`-algebra `B`, a homomorphism `f : A → B`, and an `S`-sorted subset
`M` of `B` with `f⁻¹[M] = L` sortwise (Definition 2.28). -/
def IsRecognizable (A : Algebra sig) (L : SSub A.carrier) : Prop :=
  ∃ B : Algebra sig, B.Finite ∧
    ∃ (f : Hom A B) (M : SSub B.carrier), ∀ s, f.toFun s ⁻¹' (M s) = L s

/-- `L ⊆ A_s` is **`s`-recognizable**: there are a finite `Σ`-algebra `B`, a
homomorphism `f : A → B`, and `M ⊆ B_s` with `f_s⁻¹[M] = L` (Definition 2.55). -/
def sRecognizable (A : Algebra sig) (s : S) (L : Set (A.carrier s)) : Prop :=
  ∃ B : Algebra sig, B.Finite ∧
    ∃ (f : Hom A B) (M : Set (B.carrier s)), f.toFun s ⁻¹' M = L

/-- `Rec(A)` — the set of recognizable `S`-sorted subsets of `A`. -/
def Recognizable (A : Algebra sig) : Set (SSub A.carrier) :=
  { L | IsRecognizable A L }

/-- `Rec_s(A)` — the set of `s`-recognizable languages of `A` at sort `s`. -/
def RecS (A : Algebra sig) (s : S) : Set (Set (A.carrier s)) :=
  { L | sRecognizable A s L }

end MSKleene


