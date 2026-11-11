-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Algebra
-- name    : AbelianPromises_Dichotomy_Algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:09:18.639132+00:00
-- url     : https://prove2.me/theorems/cde88671-68eb-4369-ba96-0e8e9af06922
-- title:
--   Polymorphism minion maps, restrictions and essential unarity
-- statement:
--   The published minion and polymorphism definitions are used with positive arities and every minor map. A polymorphism maps coordinatewise related rows to a related output triple. A minion map preserves arity and minors and has no requirement to preserve composition.
--
--   For a subset S of the domain, the restricted minion consists of restrictions of full operations:
--   $$
--   M|_S^{(n)}=\{f|_{S^n}:f\in M^{(n)}\}.
--   $$
--   The restriction map is defined on each actual operation. A restricted binary polymorphism over ℤ_p must extend to a polymorphism on all of ℤ_p, including zero. A function is essentially unary if one fixed coordinate i and one unary function h satisfy f(x)=h(xᵢ) for every input x. These definitions allow arbitrary minors, including dummy coordinates and identifications, and exclude no full-domain polymorphisms.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, Abelian embeddings make useful promises: approximation of detrivialised equations, STOC 2027 submission #967 (October 2026), printed p. 10 (PDF p. 11), Definitions 4.1–4.2 and 4.16

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Relations
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition

set_option autoImplicit false

namespace AbelianPromises.Dichotomy

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.Theory

/-- Arity and minor preserving map, using the published minion definitions. -/
def PolMap {A B C D : Type} (R : Relation A) (Q : Relation B)
    (R' : Relation C) (Q' : Relation D) : Prop :=
  ∃ (h : Hom R Q) (h' : Hom R' Q'),
    ∃ ξ : (n : ℕ) → {f // f ∈ (Pol (actual R) (actual Q) h).mem n} →
      {f // f ∈ (Pol (actual R') (actual Q') h').mem n},
      IsMinionHom (Pol (actual R) (actual Q) h) (Pol (actual R') (actual Q') h') ξ

/-- Actual restrictions of full operations, rather than operations preserving an induced relation. -/
def restrictMinion {A B : Type} (M : Minion A B) (S : Set A) : Minion S B where
  mem n := {f | ∃ g ∈ M.mem n, f = fun x => g (fun i => (x i).val)}
  mem_zero := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨g, hg, _⟩
    rw [M.mem_zero] at hg
    exact hg
  nonempty := by
    obtain ⟨n, g, hg⟩ := M.nonempty
    exact ⟨n, fun x => g (fun i => (x i).val), g, hg, rfl⟩
  minor_mem := by
    rintro m n π f ⟨g, hg, rfl⟩
    exact ⟨fun x => g (x ∘ π), M.minor_mem π g hg, rfl⟩

def restriction {A B : Type} (M : Minion A B) (S : Set A) (n : ℕ)
    (f : {f // f ∈ M.mem n}) : {f // f ∈ (restrictMinion M S).mem n} :=
  ⟨fun x => f.val (fun i => (x i).val), f.val, f.property, rfl⟩

/-- Binary restrictions that extend to full-domain polymorphisms. -/
def RestrictedBinary {p : ℕ} (f : (Fin 2 → {x : ZMod p // x ≠ 0}) → Fin 3) : Prop :=
  ∃ g : (Fin 2 → ZMod p) → Fin 3,
    IsPolymorphism (eqnStar (ZMod p)) (nae 3) g ∧
      ∀ x, f x = g (fun i => (x i).val)

def EssentiallyUnary {A B : Type} {n : ℕ} (f : (Fin n → A) → B) : Prop :=
  ∃ (i : Fin n) (h : A → B), ∀ x, f x = h (x i)

end AbelianPromises.Dichotomy


