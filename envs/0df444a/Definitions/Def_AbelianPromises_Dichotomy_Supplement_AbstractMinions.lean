-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Supplement_AbstractMinions
-- name    : AbelianPromises_Dichotomy_Supplement_AbstractMinions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:52:21.956228+00:00
-- url     : https://prove2.me/theorems/3519edb6-85bb-41d6-9d66-0eb45bba955f
-- title:
--   Abstract minions and the published polymorphism bridge
-- statement:
--   An abstract minion assigns a set $N^{(X)}$ to every nonempty finite coordinate set $X$, with minor operations for every map $\pi:X\to Y$. These obey
--
--   $$
--   f^{\mathrm{id}_X}=f,\qquad (f^\pi)^\rho=f^{\rho\circ\pi}.
--   $$
--
--   A minion homomorphism is an arity-preserving family that commutes with all minors. The sets of members may be infinite or empty; no representation by functions is imposed on an arbitrary abstract minion. The polymorphism bridge reindexes the published function minion $\operatorname{Pol}(R,Q)$ on the actual domains of its two relations.
--
--   **Formalization Note** Nonempty finite subsets of the natural numbers form a small indexing skeleton with all finite arities and all maps. A graph presentation records the exact graph of a minor operation; the derived omega construction uses this presentation to expose its formula without assuming closure or minion-homomorphism results.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, STOC 2027 submission #967 (October 2026). Canonical submission artifact; no arXiv pin or acceptance claim. printed p. 18 (PDF p. 19), Definition C.9; function-minion bridge also Section 4, printed p. 10 (PDF p. 11).

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Relations
import Definitions.Def_AlgebraicPCSP_Theory_Minion

set_option autoImplicit false

namespace AbelianPromises.Dichotomy.Supplement

/-- A small skeleton containing every nonempty finite coordinate set, with no size bound. -/
abbrev Arity := {X : Finset ℕ // X.Nonempty}

instance : CoeSort Arity Type := ⟨fun X => {x : ℕ // x ∈ X.val}⟩

instance (X : Arity) : Fintype X := inferInstanceAs (Fintype {x : ℕ // x ∈ X.val})
instance (X : Arity) : DecidableEq X := inferInstanceAs (DecidableEq {x : ℕ // x ∈ X.val})

/-- Definition C.9, on a skeleton of all nonempty finite arities. The member sets may be empty. -/
structure AbstractMinion where
  Obj : Arity → Type
  minor : {X Y : Arity} → (X → Y) → Obj X → Obj Y
  identity : ∀ (X : Arity) (f : Obj X), minor id f = f
  composition : ∀ {X Y Z : Arity} (π : X → Y) (ρ : Y → Z) (f : Obj X),
    minor ρ (minor π f) = minor (ρ ∘ π) f

/-- Graph presentation of a minor operation. This lets constructions expose their actual
minor formula without putting derived closure theorems in a definition upload. -/
structure MinionPresentation where
  Obj : Arity → Type
  IsMinor : {X Y : Arity} → (X → Y) → Obj X → Obj Y → Prop

def AbstractMinion.presentation (N : AbstractMinion) : MinionPresentation where
  Obj := N.Obj
  IsMinor π f g := g = N.minor π f

/-- Arity-preserving maps commuting with every minor, not only bijective minors. -/
def HasMinionHom (M N : MinionPresentation) : Prop :=
  ∃ ξ : (X : Arity) → M.Obj X → N.Obj X,
    ∀ (X Y : Arity) (π : X → Y) (f : M.Obj X) (g : M.Obj Y),
      M.IsMinor π f g → N.IsMinor π (ξ X f) (ξ Y g)

noncomputable instance carrierFintype {A : Type} [Fintype A] (R : Relation A) :
    Fintype (Carrier R) := by
  classical
  unfold Carrier
  exact Fintype.ofFinite _

/-- Reindex the existing published function minion Pol(R,Q) along X ≃ Fin |X|.
No new polymorphism predicate or additional template condition is introduced. -/
noncomputable def polPresentation {A B : Type} (R : Relation A) (Q : Relation B)
    (h : Hom R Q) : MinionPresentation where
  Obj X := {f : (X → Carrier R) → Carrier Q //
    (fun u : Fin (Fintype.card X) → Carrier R => f (u ∘ Fintype.equivFin X)) ∈
      (AlgebraicPCSP.Theory.Pol (actual R) (actual Q) h).mem (Fintype.card X)}
  IsMinor π f g := g.val = fun u => f.val (u ∘ π)

end AbelianPromises.Dichotomy.Supplement


