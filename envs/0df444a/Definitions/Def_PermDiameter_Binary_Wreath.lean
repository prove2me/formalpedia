-- Prove2me | Definitions.Def_PermDiameter_Binary_Wreath
-- name    : PermDiameter_Binary_Wreath
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:09:46.768006+00:00
-- url     : https://prove2.me/theorems/629d5af9-b92c-4de1-8966-97065be10544
-- title:
--   The wreath product $G\wr H$ with the multiplication of Definition 2.2, and the cyclic position group $C_r$
-- statement:
--   Let $G$ and $H$ be groups. The **wreath product** $G\wr H$ consists of all pairs $(f,t)$ with $f:H\to G$ and $t\in H$, multiplied by
--   $$(f,t)\cdot(f',t')=(f\cdot{}^{t}\!f',\,t t'),\qquad (f\cdot{}^{t}\!f')(x)=f(x)\,f'(xt).$$
--   The identity is $(1,1)$ and $(f,t)^{-1}=(x\mapsto f(xt^{-1})^{-1},\,t^{-1})$. An element of $H$ is a **position** when it is an argument of $f$ and a **shift** when it is the second component; $(f,t)$ has shift $t$ and **value** $f(x)$ at the position $x$.
--
--   The cyclic group $C_r$ of order $r$ is modelled as $\mathbb Z/r\mathbb Z$ written multiplicatively; its elements are the positions of the wreath product $G_1\wr C_r$ of Section 3, and the position $1\in C_r$ is the residue $0$.
--
--   The wreath product is the central construction of Step 2 of the paper's reduction, where generators with prescribed values and shifts (fillers and bridges) are designed.
--
--   **Formalization Note.** `Wreath G H` is a structure with fields `f : H → G` and `t : H`, and the `Group` instance implements exactly the formula above (the right-action convention of the paper). Mathlib's `RegularWreathProduct` uses $f'(t^{-1}x)$ instead and is not used.
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 10, Definition 2.2

import Mathlib

namespace PermDiameter.Binary

/-!
# The wreath product `G ≀ H` (Lohrey–Thumm, §2.2, p. 10, Definition 2.2)

Pairs `(f, t)` with `f : H → G` and `t ∈ H`, multiplied by
`(f, t) · (f', t') = (f · ᵗf', t t')` with `(f · ᵗf')(x) = f(x) f'(x t)`.
This is the paper's (right-action) convention; Mathlib's `RegularWreathProduct` uses
`f'(t⁻¹ x)` instead and is not used here.
-/

/-- An element `(f, t)` of the wreath product `G ≀ H`: values `f x ∈ G` at the positions
`x ∈ H`, and the shift `t ∈ H`. -/
@[ext]
structure Wreath (G H : Type) where
  /-- the value `f(x)` at every position `x` -/
  f : H → G
  /-- the shift -/
  t : H

namespace Wreath

variable {G H : Type} [Group G] [Group H]

/-- Definition 2.2: `(f, t) · (f', t') = (x ↦ f(x) f'(x t), t t')`. -/
instance : Mul (Wreath G H) := ⟨fun p p' => ⟨fun x => p.f x * p'.f (x * p.t), p.t * p'.t⟩⟩

/-- The identity `(1, 1)`: constant value `1`, trivial shift. -/
instance : One (Wreath G H) := ⟨⟨fun _ => 1, 1⟩⟩

/-- The inverse `(f, t)⁻¹ = (x ↦ f(x t⁻¹)⁻¹, t⁻¹)`. -/
instance : Inv (Wreath G H) := ⟨fun p => ⟨fun x => (p.f (x * p.t⁻¹))⁻¹, p.t⁻¹⟩⟩

@[simp] lemma mul_f (p p' : Wreath G H) (x : H) : (p * p').f x = p.f x * p'.f (x * p.t) := rfl
@[simp] lemma mul_t (p p' : Wreath G H) : (p * p').t = p.t * p'.t := rfl
@[simp] lemma one_f (x : H) : (1 : Wreath G H).f x = 1 := rfl
@[simp] lemma one_t : (1 : Wreath G H).t = 1 := rfl
@[simp] lemma inv_f (p : Wreath G H) (x : H) : (p⁻¹).f x = (p.f (x * p.t⁻¹))⁻¹ := rfl
@[simp] lemma inv_t (p : Wreath G H) : (p⁻¹).t = p.t⁻¹ := rfl

instance : Group (Wreath G H) where
  mul_assoc a b c := by
    ext x
    · simp [mul_assoc]
    · simp [mul_assoc]
  one_mul a := by
    ext x
    · simp
    · simp
  mul_one a := by
    ext x
    · simp
    · simp
  inv_mul_cancel a := by
    ext x
    · simp
    · simp

end Wreath

/-- The cyclic group `C_r`, written multiplicatively as `ℤ/rℤ`; its elements serve as
**positions** (arguments of `f`) and as **shifts**. The position `1 ∈ C_r` is the residue `0`. -/
abbrev Pos (r : ℕ) : Type := Multiplicative (ZMod r)

end PermDiameter.Binary


