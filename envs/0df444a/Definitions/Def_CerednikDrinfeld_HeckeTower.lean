-- Prove2me | Definitions.Def_CerednikDrinfeld_HeckeTower
-- name    : CerednikDrinfeld_HeckeTower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d3a46e8e-ff1c-5a00-937b-d8aee642665a
-- title:
--   Index data for a two-arrow Hecke tower of function fields
-- statement:
--   Fix natural numbers $q,q'$. `AwayPrime q q'` is the type of primes $\ell$ with $\ell \ne q$ and $\ell \ne q'$; `Obj q q'` is `Option (AwayPrime q q')`, i.e. a base object `none` together with one object for each such prime; and `Arr q q'` is `AwayPrime q q' × Fin 2`, so that over each prime $\ell$ there are exactly two arrows, with `dom (ℓ, i) = some ℓ` and `cod (ℓ, i) = none` — two parallel arrows from the object $\ell$ to the base object. For $N : \mathbb{N}$, `arrowDegree N (ℓ, i)` is the numerical invariant $\ell$ if $\ell \mid N$ and $\ell + 1$ otherwise; it depends only on $\ell$ and not on $i$, and is attached to an arrow without any claim that it is the degree of a field extension.
--
--   The structure `TowerData q q' Fbase`, for a field $F_\ast =$ `Fbase` that is an algebra over `AlgebraicClosure ℚ`, packages: a field $F_\ell$ for each $\ell \in$ `AwayPrime q q'`, each an algebra over $\overline{\mathbb{Q}}$ satisfying `IsCurveOver` (the principal-divisor axiom `HasPrincipalDivisors`, finiteness of the residue field of every place over $\overline{\mathbb{Q}}$, and freeness of $\Omega_{F_\ell/\overline{\mathbb{Q}}}$ of rank one over $F_\ell$) and `Algebra.EssFiniteType` over $\overline{\mathbb{Q}}$; for each arrow $(\ell, i)$ a $\overline{\mathbb{Q}}$-algebra homomorphism $\varphi_{(\ell,i)} : F_\ast \to F_\ell$; and the requirements `FiniteAlong` (finiteness of $F_\ell$ as a module over $F_\ast$ via $\varphi_{(\ell,i)}$) and integrality of the underlying ring homomorphism. Thus the two maps over a given $\ell$ are recorded as data rather than as a single canonical algebra structure. Auxiliary declarations assemble this into a functor-like package: `objField` sends `none` to $F_\ast$ and `some ℓ` to $F_\ell$, with its field, $\overline{\mathbb{Q}}$-algebra, curve and essentially-finite-type structures transported objectwise (the last two under the corresponding hypotheses on $F_\ast$); `algF α` is the algebra structure on `objField (dom α)` over `objField (cod α)` obtained from $\varphi_\alpha$ by `algebraAlong`; and `isScalarTower_algF`, `finiteDimensional_algF` record that this algebra is compatible with the $\overline{\mathbb{Q}}$-structures and finite-dimensional.
--
--   **Relation to Mathlib.** Mathlib has no notion of a Hecke tower of function fields; the index data and `TowerData` are the project's own, built on the project's `IsCurveOver`, `FiniteAlong` and `algebraAlong` and on Mathlib's `Algebra.EssFiniteType`, `Module.Finite` and `RingHom.IsIntegral`.
--
--   **Where it is used.** The intended instance is the tower of geometric function fields of Shimura curves attached to an indefinite quaternion algebra of discriminant $qq'$, with the two arrows over a prime $\ell$ given by pullback of functions along the two degeneracy maps from level $N\ell$ to level $N$; `arrowDegree` records the expected degrees $\ell$ or $\ell+1$. Divisor pushforward along one arrow composed with pullback along the other yields the Hecke correspondences on Jacobians used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_HeckeTower.lean

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CerednikDrinfeld
namespace HeckeTower

open AlgebraicCurve

abbrev AwayPrime (q q' : ℕ) : Type := {ℓ : Nat.Primes // (ℓ : ℕ) ≠ q ∧ (ℓ : ℕ) ≠ q'}

abbrev Obj (q q' : ℕ) : Type := Option (AwayPrime q q')

abbrev Arr (q q' : ℕ) : Type := AwayPrime q q' × Fin 2

variable {q q' : ℕ}

abbrev dom (α : Arr q q') : Obj q q' := some α.1

abbrev cod (_α : Arr q q') : Obj q q' := none

def arrowDegree (N : ℕ) (α : Arr q q') : ℕ :=
  if (α.1.1 : ℕ) ∣ N then (α.1.1 : ℕ) else (α.1.1 : ℕ) + 1

structure TowerData (q q' : ℕ) (Fbase : Type) [Field Fbase] [Algebra (AlgebraicClosure ℚ) Fbase] : Type 1 where

  F : AwayPrime q q' → Type
  [instField : ∀ ℓ, Field (F ℓ)]
  [instAlgebra : ∀ ℓ, Algebra (AlgebraicClosure ℚ) (F ℓ)]
  [instCurve : ∀ ℓ, IsCurveOver (AlgebraicClosure ℚ) (F ℓ)]
  [instEss : ∀ ℓ, Algebra.EssFiniteType (AlgebraicClosure ℚ) (F ℓ)]

  φ : ∀ α : Arr q q', Fbase →ₐ[AlgebraicClosure ℚ] F α.1

  finite : ∀ α : Arr q q', FiniteAlong (AlgebraicClosure ℚ) (φ α)

  integral : ∀ α : Arr q q', (φ α).toRingHom.IsIntegral

attribute [instance] TowerData.instField TowerData.instAlgebra TowerData.instCurve TowerData.instEss

namespace TowerData

variable {Fbase : Type} [Field Fbase] [Algebra (AlgebraicClosure ℚ) Fbase] (T : TowerData q q' Fbase)

@[reducible] def objField : Obj q q' → Type
  | none => Fbase
  | some ℓ => T.F ℓ

instance instFieldObj : ∀ j : Obj q q', Field (T.objField j)
  | none => inferInstanceAs (Field Fbase)
  | some ℓ => inferInstanceAs (Field (T.F ℓ))

instance instAlgebraObj : ∀ j : Obj q q', Algebra (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (Algebra (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (Algebra (AlgebraicClosure ℚ) (T.F ℓ))

instance instCurveObj [IsCurveOver (AlgebraicClosure ℚ) Fbase] : ∀ j : Obj q q', IsCurveOver (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (IsCurveOver (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (IsCurveOver (AlgebraicClosure ℚ) (T.F ℓ))

instance instEssFiniteTypeObj [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbase] :
    ∀ j : Obj q q', Algebra.EssFiniteType (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (Algebra.EssFiniteType (AlgebraicClosure ℚ) (T.F ℓ))

@[reducible] noncomputable def algF (α : Arr q q') : Algebra (T.objField (cod α)) (T.objField (dom α)) :=
  algebraAlong (T.φ α)

theorem isScalarTower_algF (α : Arr q q') :
    letI := T.algF α
    IsScalarTower (AlgebraicClosure ℚ) (T.objField (cod α)) (T.objField (dom α)) :=
  isScalarTower_along (T.φ α)

theorem finiteDimensional_algF (α : Arr q q') :
    letI := T.algF α
    FiniteDimensional (T.objField (cod α)) (T.objField (dom α)) :=
  T.finite α

end TowerData

end HeckeTower
end CerednikDrinfeld


