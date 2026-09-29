-- Prove2me | Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
-- name    : AlgebraicGeometry_GradedOAlgebraSectionRing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/9e35710b-7d20-562f-adb0-475a3e5b57dc
-- title:
--   Tensor-power isomorphisms and the graded section-ring predicate
-- statement:
--   Let $X$ be a scheme and $L$ an object of `X.Modules`, the symmetric monoidal category of sheaves of modules on $X$. Three helper isomorphisms are defined by recursion on the exponent, matching the recursion defining `tensorPow` (degree $0$ is the monoidal unit, and passing from $n$ to $n+1$ tensors on the right by $L$). `tensorPowAdd L m n` is the isomorphism $L^{\otimes m}\otimes L^{\otimes n}\cong L^{\otimes(m+n)}$, given at $n=0$ by the right unitor and otherwise by reassociating and whiskering the previous case on the right by $L$. `tensorPowMapIso` turns an isomorphism $e:L_1\cong L_2$ into $L_1^{\otimes n}\cong L_2^{\otimes n}$ by tensoring $n$ copies of $e$. `pullbackTensorPowIso c L`, for $c:X\to Y$ and $L$ on $Y$, is $c^*(L^{\otimes n})\cong (c^*L)^{\otimes n}$, assembled from the comparison isomorphisms `pullbackTensorUnitObjIso` and `pullbackTensorObjIso` of the monoidal functor `Modules.pullback c`.
--
--   For a commutative ring $S$ and a morphism $f:X\to \operatorname{Spec} S$, `baseScalar f s` is the global section of $X$ obtained by transporting $s\in S$ through the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism and then applying $f$ on global sections; it is the structural $S$-algebra action on $\Gamma(X,\top)$.
--
--   `IsSectionRing f L R 𝓡 ι` is a Prop-valued structure on the data of such an $f$, an object $L$ of `X.Modules`, a commutative $S$-algebra $R$ with an $\mathbb N$-grading $𝓡$ by $S$-submodules making it a graded algebra, and a family of bare functions $\iota_n:𝓡_n\to\Gamma(L^{\otimes n},\top)$. Its fields assert: each $\iota_n$ is bijective; each $\iota_n$ is additive; $\iota_n(s\cdot x)=\mathrm{baseScalar}(f)(s)\cdot\iota_n(x)$; $\iota_0(1)$ is the unit global section `unitSection ⊤`; and for homogeneous $x\in 𝓡_m$, $y\in 𝓡_n$, $\iota_{m+n}(xy)$ is the image of `tensorSections (ι m x) (ι n y)` under `tensorPowAdd L m n` evaluated on $\top$. Thus the predicate records that the given presentation $(R,𝓡,\iota)$ identifies $R$ degreewise and multiplicatively with $\bigoplus_n\Gamma(X,L^{\otimes n})$; it is a condition on the chosen maps $\iota$, not the assertion that some isomorphism exists.
--
--   **Relation to Mathlib.** Mathlib has no monoidal structure on `SheafOfModules`, nor a notion of the graded ring of sections of a sheaf of modules; the monoidal structure, the tensor powers and `IsSectionRing` are the project's own.
--
--   **Where it is used.** These definitions form part of the scheme-theoretic infrastructure by which a graded ring is recognised as the ring of sections of a sheaf of modules on a scheme over $\operatorname{Spec} S$, allowing graded-ring computations to be transferred to the geometry of $X$ in the modules-and-sheaves layer of the formalisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_GradedOAlgebraSectionRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

def tensorPowAdd (L : X.Modules) (m : ℕ) : (n : ℕ) → (L.tensorPow m ⊗ L.tensorPow n ≅ L.tensorPow (m + n))
  | 0 => ρ_ (L.tensorPow m)
  | n + 1 => (α_ (L.tensorPow m) (L.tensorPow n) L).symm ≪≫ whiskerRightIso (tensorPowAdd L m n) L

def tensorPowMapIso {L₁ L₂ : X.Modules} (e : L₁ ≅ L₂) : (n : ℕ) → (L₁.tensorPow n ≅ L₂.tensorPow n)
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowMapIso e n) e

def pullbackTensorPowIso {Y : Scheme.{u}} (c : X ⟶ Y) (L : Y.Modules) :
    (n : ℕ) → ((Modules.pullback c).obj (L.tensorPow n) ≅ ((Modules.pullback c).obj L).tensorPow n)
  | 0 => pullbackTensorUnitObjIso c
  | n + 1 => pullbackTensorObjIso c (L.tensorPow n) L ≪≫ whiskerRightIso (pullbackTensorPowIso c L n) ((Modules.pullback c).obj L)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GradedOAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {S : Type u} [CommRing S] {X : Scheme.{u}}

def baseScalar (f : X ⟶ Spec (CommRingCat.of S)) (s : S) : Γ(X, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s)

structure IsSectionRing (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) : Prop where

  bijective : ∀ n, Function.Bijective (ι n)

  map_add : ∀ n (x y : 𝓡 n), ι n (x + y) = ι n x + ι n y

  map_smul : ∀ n (s : S) (x : 𝓡 n), ι n (s • x) = baseScalar f s • ι n x

  map_one : ι 0 ⟨1, SetLike.GradedOne.one_mem⟩ = unitSection ⊤

  map_mul : ∀ m n (x : 𝓡 m) (y : 𝓡 n),
    ι (m + n) ⟨(x : R) * (y : R), SetLike.GradedMul.mul_mem x.2 y.2⟩ =
      ((tensorPowAdd L m n).hom.app ⊤) (tensorSections (ι m x) (ι n y))

end AlgebraicGeometry.GradedOAlgebra

end


