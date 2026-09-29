-- Prove2me | Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
-- name    : AlgebraicCurve_FibreResidueIdentityAlong
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/896d9922-7f7b-5843-9ae5-e4dab89bcc37
-- title:
--   Fibre residue identity along an integral algebra map
-- statement:
--   The module introduces a single Prop-valued predicate, [`AlgebraicCurve.FibreResidueIdentityAlong`](../def/AlgebraicCurve_FibreResidueIdentityAlong.html#L16), expressing compatibility of local residues with pull-back of differentials and trace along a map of function fields. The context is a field $K$ and two $K$-algebra fields $F$, $F'$, with $F'$ equipped with the predicate `HasPrincipalDivisors K F'` and both $F$ and $F'$ equipped with `HasCanonicalLocalResidueKStar`, i.e. with a chosen family assigning to each place $v$ a canonical residue datum: a $K$-linear map $\mathrm{res}_v \colon F \to \kappa(v)$ into the residue field of $v$ that vanishes on the valuation subring of $v$, sends $f$ with $\pi_v f$ integral to the residue class of $\pi_v f$, and kills the monomials $(\pi_v^{n+1})^{-1}$ for $n \ge 1$ ($\pi_v$ the chosen uniformiser). For a $K$-algebra map $\varphi \colon F \to F'$ together with a proof `hφ` that the underlying ring homomorphism is integral, `FibreResidueIdentityAlong φ hφ` asserts: for every place $v$ of $F$ over $K$, every $\omega \in \Omega_{F/K}$ and every $f' \in F'$,
--   $$\sum_{w \in \mathrm{fiberAlong}\,\varphi\,v} \mathrm{Tr}_{\kappa(w)/K}\,\mathrm{res}_w\!\big(f' \cdot \partial_w(\varphi^*\omega)\big) \;=\; \mathrm{Tr}_{\kappa(v)/K}\,\mathrm{res}_v\!\big(\mathrm{Tr}_{F'/F}(f') \cdot \partial_v \omega\big),$$
--   where the sum runs over the finite fibre `Place.fiberAlong φ hφ v` of places $w$ of $F'$ restricting to $v$, $\varphi^*$ is `Differential.pullbackAlong φ` on Kähler differentials, $\partial_v \omega$ denotes `v.differentialCoeff ω` (the coefficient of $\omega$ relative to the local differential coordinate at $v$), $\mathrm{Tr}_{F'/F}$ is `traceFunAlong φ`, the algebra trace for the $F$-algebra structure on $F'$ induced by $\varphi$, and each side is a value of `kaehlerResidueTerm`, whose argument families are the constant (diagonal) families $\mathrm{diagonalHom}$ of $f'$ and of $\mathrm{Tr}_{F'/F}(f')$ respectively. Thus the predicate is a hypothesis about the chosen residue data on $F$ and $F'$, to be assumed where needed rather than established here.
--
--   **Relation to Mathlib.** Mathlib has no notion of local residue of a differential at a place or of residues along a map of function fields; the predicate is the project's own, phrased in terms of Mathlib's `KaehlerDifferential` and `Algebra.trace`.
--
--   **Where it is used.** The predicate is used as a hypothesis in the construction of the Serre-duality pairing for curves and its adjunction properties for maps of curves, where pull-back of differentials must be adjoint to the trace on functions; this underlies the push-pull formalism for correspondences on modular curves and hence the action on their Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_FibreResidueIdentityAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def FibreResidueIdentityAlong [HasPrincipalDivisors K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) : Prop :=
  ∀ (v : Place K F) (ω : Ω[F⁄K]) (f' : F'),
    ∑ w ∈ Place.fiberAlong φ hφ v,
        kaehlerResidueTerm (Differential.pullbackAlong φ ω) (diagonalHom K F' f') w
      = kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong φ f')) v

end AlgebraicCurve

end


