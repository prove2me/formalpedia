-- Prove2me | Definitions.Def_MSKleene_Iteration
-- name    : MSKleene_Iteration
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:27:58.659852+00:00
-- url     : https://prove2.me/theorems/a58f9464-8446-4e26-afb5-a5cc8b6f2d30
-- title:
--   The $z$-iteration $L^{\star z}$
-- statement:
--   The **$z$-iteration** of a language (Definition 3.26; many-sorted counterpart of Gécseg–Steinby 1984, Definition 4.7).
--
--   For a sort `s`, a variable `z ∈ X_s`, and a language `L ⊆ T_Σ(X)_s`, the finite stages are
--   $$L^{0\,z} = \{z\}, \qquad L^{(i+1)\,z} = L^{i\,z} \cup \langle z/L^{i\,z}\rangle^{\sharp\mathsf{p}}_s(L),$$
--   and `iterate z L` is $L^{\star z} = \bigcup_{i \in \mathbb{N}} L^{i\,z}$. Intuitively, one starts from `z` and repeatedly substitutes, at every occurrence of `z` in a term of `L`, a term already known to lie in $L^{\star z}$.
--
--   The simp lemmas `iterStage_zero` and `iterStage_succ` expose the recursion.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026, https://arxiv.org/abs/1808.08217 (predecessor CVCL20)

/-
The `z`-iteration of a language (Definition 3.26; many-sorted counterpart of
Gécseg–Steinby 1984, Definition 4.7).

For a sort `s`, a variable `z ∈ X_s`, and a language `L ⊆ T_Σ(X)_s`:
  `L^{0 z} = {z}`,   `L^{(i+1) z} = L^{i z} ∪ ⟨z/L^{i z}⟩^♯ᵖ_s (L)`,
  `L^{⋆ z} = ⋃_{i ∈ ℕ} L^{i z}`.
New members of `L^{⋆z}` are obtained by substituting, at every occurrence of `z`
in some term of `L`, a term already known to be in `L^{⋆z}`.
-/
import Definitions.Def_MSKleene_Subst

namespace MSKleene

universe u

variable {S : Type u} {sig : Signature S} {X : SSet S}

/-- The finite stages `L^{i z}` of the `z`-iteration (Definition 3.26). -/
noncomputable def iterStage {s : S} (z : X s) (L : Set (Term sig X s)) :
    ℕ → Set (Term sig X s)
  | 0 => {Term.var z}
  | i + 1 => iterStage z L i ∪ substP z (iterStage z L i) s L

/-- The `z`-iteration `L^{⋆ z} = ⋃_{i} L^{i z}` (Definition 3.26). -/
noncomputable def iterate {s : S} (z : X s) (L : Set (Term sig X s)) :
    Set (Term sig X s) :=
  ⋃ i : ℕ, iterStage z L i

@[simp] theorem iterStage_zero {s : S} (z : X s) (L : Set (Term sig X s)) :
    iterStage z L 0 = {Term.var z} := rfl

theorem iterStage_succ {s : S} (z : X s) (L : Set (Term sig X s)) (i : ℕ) :
    iterStage z L (i + 1) = iterStage z L i ∪ substP z (iterStage z L i) s L := rfl

end MSKleene


