-- Prove2me | Definitions.Def_ModularCurve_LevelModuliPackageAbs
-- name    : ModularCurve_LevelModuliPackageAbs
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/d0a5e2bc-0531-5708-9b99-a96ec90a1eb4
-- title:
--   Abstract representing algebra for a level moduli datum
-- statement:
--   The ambient notion is that of a level moduli datum $D$ over a commutative ring $A$: an assignment $T \mapsto D.\mathrm{Pt}\,T$ of a type of points to each commutative $A$-algebra $T$, together with a pushforward $D.\mathrm{map}$ along $A$-algebra homomorphisms satisfying the identity and composition laws, and a $j$-coordinate $D.\mathrm{jOf} : D.\mathrm{Pt}\,T \to T$ compatible with pushforward. This module introduces the structure [`ModularCurve.LevelModuliPackageAbs A D`](../def/ModularCurve_LevelModuliPackageAbs.html#L10), an abstract representing object for such a datum. An inhabitant consists of a type `B₀` carrying a commutative ring structure and an $A$-algebra structure (both recorded as fields of the structure and registered as instances), a point `univ : D.Pt B₀`, and a field `represents` asserting that for every commutative $A$-algebra $T$ and every $x : D.\mathrm{Pt}\,T$ there is a unique $A$-algebra homomorphism $\varphi : B_0 \to T$ with $D.\mathrm{map}\ \varphi\ \mathrm{univ} = x$. Thus the universal property $\operatorname{Hom}_{A\text{-alg}}(B_0,T) \xrightarrow{\sim} D(T)$, $\varphi \mapsto \varphi_*(\mathrm{univ})$, is carried as a field of the structure: producing an inhabitant is exactly proving representability of the moduli problem, and no ambient field or prescribed $j$-invariant is fixed.
--
--   The accompanying declarations extract the content of this universal property. The element `j₀` is the $j$-coordinate $D.\mathrm{jOf}$ of the universal point, an element of `B₀`. For a point $x$ over $T$, `classify x` is the classifying $A$-algebra homomorphism $B_0 \to T$ obtained from `represents`; `map_classify` states that pushing `univ` forward along it returns $x$, and `classify_unique` states that any $\varphi$ with $D.\mathrm{map}\ \varphi\ \mathrm{univ} = x$ coincides with `classify x`.
--
--   **Relation to Mathlib.** Mathlib has no notion of a moduli problem of level structures or of its representing algebra; these structures are the project's own. Representability is phrased directly as a universal property on commutative $A$-algebras rather than through Mathlib's category-theoretic corepresentability machinery.
--
--   **Where it is used.** This is the presentation-free counterpart of `LevelModuliPackage`, which instead realises the representing algebra as a subalgebra of an ambient field containing a prescribed $j$; abstract packages are the form in which representability of the level structure problems used for modular curves is established, and they are subsequently transported into an ambient function field where $j$-coordinates and induced (semi)endomorphisms are available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelModuliPackageAbs.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace ModularCurve

structure LevelModuliPackageAbs (A : Type u) [CommRing A] (D : LevelModuliDatum.{u} A) where

  B₀ : Type u

  [instCommRing : CommRing B₀]

  [instAlgebra : Algebra A B₀]

  univ : D.Pt B₀

  represents : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : D.Pt T), ∃! φ : B₀ →ₐ[A] T, D.map φ univ = x

attribute [instance] LevelModuliPackageAbs.instCommRing LevelModuliPackageAbs.instAlgebra

namespace LevelModuliPackageAbs

variable {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)

def j₀ : P.B₀ := D.jOf P.univ

noncomputable def classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : P.B₀ →ₐ[A] T :=
  (P.represents T x).choose

theorem map_classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : D.map (P.classify x) P.univ = x :=
  (P.represents T x).choose_spec.1

theorem classify_unique {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) (φ : P.B₀ →ₐ[A] T)
    (h : D.map φ P.univ = x) : φ = P.classify x :=
  (P.represents T x).unique h (P.map_classify x) ▸ rfl

end LevelModuliPackageAbs

end ModularCurve


