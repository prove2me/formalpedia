-- Prove2me | Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
-- name    : AlgebraicGeometry_SquareZeroRelTangent
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a74fe094-5c10-50af-a4bc-5c9722fc3702
-- title:
--   Relative tangent points of a pointed scheme over a parameter base
-- statement:
--   The context is a field $k$, a scheme $X$ with structure morphism $x : X \to \operatorname{Spec} k$, a section $pt : \operatorname{Spec} k \to X$ of it, and a $k$-vector space $V$ (carried as a left and right $k$-module with central scalars, so that the trivial square-zero extension $k \oplus V$ is available). Write $D_V = \operatorname{Spec}(k \oplus V)$, with $\mathrm{toBase} : D_V \to \operatorname{Spec} k$ induced by $k \to k \oplus V$ and $\mathrm{basePoint} : \operatorname{Spec} k \to D_V$ induced by the projection $k \oplus V \to k$.
--
--   First, `TangentPoints.zero` produces the zero element of $\mathrm{TangentPoints}\,x\,pt\,V$ — the set of $k$-morphisms $v : D_V \to X$ with $x \circ v = \mathrm{toBase}$ and $v \circ \mathrm{basePoint} = pt$ — namely the constant morphism $pt \circ \mathrm{toBase}$; this uses the hypothesis $x \circ pt = \mathrm{id}$. The companion lemma records its underlying morphism.
--
--   Next, for $f_0 : Z_0 \to \operatorname{Spec} k$ together with $q_1 : Z \to Z_0$, $q_2 : Z \to D_V$ and a hypothesis `hZ` that the resulting square is cartesian (so $Z$ is a chosen fibre product $Z_0 \times_{\operatorname{Spec} k} D_V$), `SquareZero.zeroSection` is the morphism $Z_0 \to Z$ with components $\mathrm{id}_{Z_0}$ and $\mathrm{basePoint} \circ f_0$; two lemmas (also in re-associated form) identify its composites with $q_1$ and $q_2$.
--
--   Finally, `RelTangentPoints` is the subtype of morphisms $w : Z \to X$ satisfying $x \circ w = \mathrm{toBase} \circ q_2$ and $w \circ \mathrm{zeroSection} = pt \circ f_0$: first-order deformations, parametrised by $Z_0$, of the constant morphism $Z_0 \to X$ at $pt$. Extensionality is subtype extensionality, and the two defining conditions are made available as named projections. The map `const` sends $v \in \mathrm{TangentPoints}\,x\,pt\,V$ to the constant family $v \circ q_2$. Note that `RelTangentPoints` depends on the chosen cartesian square, not on a canonically constructed product.
--
--   **Relation to Mathlib.** Mathlib supplies the trivial square-zero extension `TrivSqZeroExt` and the pullback machinery for schemes; the functor-of-points description of $V$-valued tangent vectors at a $k$-point and its $Z_0$-parametrised relative version are the project's own notions.
--
--   **Where it is used.** These carriers belong to the deformation-theoretic infrastructure of the formalisation: they express first-order deformations of a constant morphism into a pointed $k$-scheme, in the form needed to compare two lifts of a morphism over a small surjection of Artinian local rings, and they are used alongside the relative Picard and Néron model material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SquareZeroRelTangent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

def TangentPoints.zero (x : X ⟶ Spec (CommRingCat.of k)) (pt : Spec (CommRingCat.of k) ⟶ X)
    (hpt : pt ≫ x = 𝟙 (Spec (CommRingCat.of k)))
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] : TangentPoints x pt V :=
  ⟨SquareZero.toBase k V ≫ pt, by rw [Category.assoc, hpt, Category.comp_id],
    by rw [SquareZero.basePoint_toBase_assoc]⟩

@[simp] theorem TangentPoints.zero_coe (x : X ⟶ Spec (CommRingCat.of k)) (pt : Spec (CommRingCat.of k) ⟶ X)
    (hpt : pt ≫ x = 𝟙 (Spec (CommRingCat.of k)))
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] :
    (TangentPoints.zero x pt hpt V).1 = SquareZero.toBase k V ≫ pt := rfl

variable (x : X ⟶ Spec (CommRingCat.of k)) (pt : Spec (CommRingCat.of k) ⟶ X)
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
  (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))

def SquareZero.zeroSection : Z₀ ⟶ Z :=
  hZ.lift (𝟙 Z₀) (f₀ ≫ SquareZero.basePoint k V)
    (by rw [Category.id_comp, Category.assoc, SquareZero.basePoint_toBase, Category.comp_id])

@[reassoc (attr := simp)]
theorem SquareZero.zeroSection_fst : SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ q₁ = 𝟙 Z₀ :=
  hZ.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem SquareZero.zeroSection_snd :
    SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ q₂ = f₀ ≫ SquareZero.basePoint k V :=
  hZ.lift_snd _ _ _

def RelTangentPoints : Type u :=
  { w : Z ⟶ X // w ≫ x = q₂ ≫ SquareZero.toBase k V ∧
      SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w = f₀ ≫ pt }

namespace RelTangentPoints

variable {x pt V f₀ q₁ q₂ hZ}

@[ext] theorem ext {w w' : RelTangentPoints x pt V f₀ q₁ q₂ hZ} (h : w.1 = w'.1) : w = w' := Subtype.ext h

theorem comp_base (w : RelTangentPoints x pt V f₀ q₁ q₂ hZ) : w.1 ≫ x = q₂ ≫ SquareZero.toBase k V := w.2.1

theorem zeroSection_comp (w : RelTangentPoints x pt V f₀ q₁ q₂ hZ) :
    SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w.1 = f₀ ≫ pt := w.2.2

variable (x pt V f₀ q₁ q₂ hZ) in

def const (v : TangentPoints x pt V) : RelTangentPoints x pt V f₀ q₁ q₂ hZ :=
  ⟨q₂ ≫ v.1, by rw [Category.assoc, v.2.1],
    by rw [SquareZero.zeroSection_snd_assoc, v.2.2]⟩

@[simp] theorem const_coe (v : TangentPoints x pt V) : (const x pt V f₀ q₁ q₂ hZ v).1 = q₂ ≫ v.1 := rfl

end RelTangentPoints

end

end AlgebraicGeometry

end


