-- Prove2me | Definitions.Def_DrinfeldCurve_TateRep
-- name    : DrinfeldCurve_TateRep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/6b5e2b4a-787a-51a6-9a4f-6abd391eba73
-- title:
--   Tate-module representations of `hSubgroup` on the Drinfeld Jacobian
-- statement:
--   Fix a prime $q$, a field $k$ that is an algebra over $\mathbb{F}_{q^2}$ (written `GaloisField q 2`) and for which the coordinate ring `CoordRing q k` of the Drinfeld curve is a domain, a prime $\ell$, and a field $E$ that is a $\mathbb{Q}_\ell$-algebra. Let $F =$ `drinfeldFunctionField q k`, the fraction field of `CoordRing q k`, and let $J =$ [`AlgebraicCurve.Pic0 k F`](../def/AlgebraicCurve_DivisorClassGroup.html#L223) be the group of degree-zero divisor classes of $F$ over $k$: divisors are finitely supported $\mathbb{Z}$-valued functions on the places of $F/k$ (valuation subrings of $F$ containing $k$, proper and with principal ideals, hence discrete valuation rings), the degree uses the residue degrees $\dim_k$ of the residue fields, and principal divisors are those of the form $v \mapsto \mathrm{ord}_v(f)$ for some $f \neq 0$. The group $F \simeq_k F$ of $k$-algebra automorphisms acts on $J$ by transport of places.
--
--   The first definition, `tateRep`, is the monoid homomorphism from `hSubgroup q` to the $E$-linear endomorphisms of $E \otimes_{\mathbb{Q}_\ell} \mathrm{RationalTateModule}_\ell(J)$, where $\mathrm{RationalTateModule}_\ell(J) = \mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} \mathrm{TateModule}_\ell(J)$. It is the composite of the action `hFunctionFieldAction q k` of `hSubgroup q` on $F$ by $k$-algebra automorphisms (induced from its action on the coordinate ring, and containing the automorphisms attached to elements of $\mathrm{SL}_2(\mathbb{Z}/q)$ and to $(q+1)$-st roots of unity in $\mathbb{F}_{q^2}$), the resulting representation on the rational Tate module of $J$, and extension of scalars from $\mathbb{Q}_\ell$ to $E$.
--
--   For an arbitrary index type $S$, `tateProd` abbreviates the $E$-module of $S$-indexed families of elements of that base-changed Tate module, and `tateProdRep` is the representation of `hSubgroup q` acting diagonally: the index is untouched and each component is acted on by `tateRep`. The accompanying equality `tateProdRep_apply` records the componentwise formula, which holds by definition.
--
--   **Relation to Mathlib.** Mathlib provides the tensor product and the base-change homomorphism `Module.End.baseChangeHom` on endomorphism rings; the Drinfeld curve and its function field, the place/divisor/degree-zero-class-group formalism, and the Tate module and its rational version are the project's own definitions.
--
--   **Where it is used.** These representations package the $\ell$-adic Tate module of the Jacobian of the Drinfeld curve $xy^q - x^qy = 1$, with coefficients extended to a $\mathbb{Q}_\ell$-algebra $E$, as a representation of `hSubgroup q`, and the product version allows a family of such modules indexed by an arbitrary type; both are used by the statements in the tree concerning this action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DrinfeldCurve_TateRep.lean

import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace DrinfeldCurve

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
  (ℓ : ℕ) [Fact ℓ.Prime] (E : Type*) [Field E] [Algebra ℚ_[ℓ] E]

def tateRep : hSubgroup q →*
    Module.End E (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :=
  (Module.End.baseChangeHom ℚ_[ℓ] E
      (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :
    Module.End ℚ_[ℓ]
        (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) →*
      Module.End E (E ⊗[ℚ_[ℓ]]
        ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))).comp
    ((ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
        (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)).comp (hFunctionFieldAction q k))

abbrev tateProd (S : Type) : Type _ :=
  S → E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))

def tateProdRep (S : Type) : hSubgroup q →* Module.End E (tateProd q k ℓ E S) where
  toFun h := LinearMap.pi fun s => (tateRep q k ℓ E h).comp (LinearMap.proj s)
  map_one' := LinearMap.ext fun v => funext fun s => by simp
  map_mul' x y := LinearMap.ext fun v => funext fun s => by simp

theorem tateProdRep_apply (S : Type) (h : hSubgroup q) (v : tateProd q k ℓ E S) (s : S) :
    tateProdRep q k ℓ E S h v s = tateRep q k ℓ E h (v s) :=
  rfl

end DrinfeldCurve

end


