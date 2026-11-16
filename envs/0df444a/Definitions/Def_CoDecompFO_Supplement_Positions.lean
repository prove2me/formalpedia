-- Prove2me | Definitions.Def_CoDecompFO_Supplement_Positions
-- name    : CoDecompFO_Supplement_Positions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:45:58.622116+00:00
-- url     : https://prove2.me/theorems/7d78cbd3-f7ec-49ee-9f06-b81553f6d359
-- title:
--   The category $\mathrm{Pos}^\sigma_m$ of $m$-positions
-- statement:
--   Fix a finite relational signature $\sigma$ and $k\in\mathbb N$ (in the paper $k=2(\ell-m)$). An **$m$-position** is a pair $(G,\beta)$ of a $\sigma$-structure $G$ and an assignment $\beta:[k]\to G$. A morphism $f:(G,\beta)\to(H,\gamma)$ is a homomorphism of $\sigma$-structures $f:G\to H$ with
--
--   $$f\circ\beta=\gamma .$$
--
--   Identities and composition are those of functions. This is the base category over which the total categories of strategies and hypotheticals sit (the slice of $\sigma$-structures under $[k]$).
--
--   **Formalization Note** The carrier of $G$ is any type in `Type` (empty and infinite structures included); the length $2(\ell-m)$ of the assignment is the parameter $k$.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶5.48, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_CoDecompFO_Sig

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

open CategoryTheory FirstOrder

/-- An **`m`-position** (Bumpus, Gomes, Larios-Jones, Turner, *Co-Decompositions and FO Model Checking*,
arXiv:2611.04658, held file sha256 d550d7af…, ¶5.48, p.27): "The category Pos^σ_m of m-positions has as its
objects pairs (G, β), where G is a σ-structure and β : [2(ℓ−m)] → G is an assignment."

**Formalization Note** The length `2(ℓ−m)` of the assignment is the parameter `k`; the statements instantiate
`k := 2 * (ℓ - m)`. The carrier of `G` is a type in `Type` (universe `0`, as for the limit `CoDecomp.Lim`); any
σ-structure is allowed, empty or infinite. -/
structure Pos (σ : Sig) (k : ℕ) : Type 1 where
  /-- The point set of the structure `G`. -/
  carrier : Type
  /-- The σ-structure on `G`. -/
  [str : σ.lang.Structure carrier]
  /-- The assignment `β : [k] → G`. -/
  pt : Fin k → carrier

attribute [instance] Pos.str

variable {σ : Sig} {k : ℕ}

/-- **The category of positions** (¶5.48, p.27): "A morphism f : (G, β) → (H, γ) is a morphism f : G → H
satisfying fβ = γ … Identities and composition are inherited from the category of σ-structures." A morphism of
σ-structures is a homomorphism (A.4, p.53), `IsHom`. -/
instance Pos.category : Category.{0} (Pos σ k) where
  Hom P Q := {f : P.carrier → Q.carrier // IsHom σ f ∧ f ∘ P.pt = Q.pt}
  id P := ⟨id, fun _ _ h => h, rfl⟩
  comp f g := ⟨g.1 ∘ f.1, fun i args h => g.2.1 i (f.1 ∘ args) (f.2.1 i args h),
    by rw [Function.comp_assoc, f.2.2, g.2.2]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem Pos.comp_val {P Q R : Pos σ k} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).1 = g.1 ∘ f.1 := rfl

@[simp] theorem Pos.id_val (P : Pos σ k) : (𝟙 P : P ⟶ P).1 = id := rfl

end Supplement

end CoDecompFO


