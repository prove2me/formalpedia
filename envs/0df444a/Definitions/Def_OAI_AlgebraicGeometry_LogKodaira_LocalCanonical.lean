-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
-- name    : OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:35.361953+00:00
-- url     : https://prove2.me/theorems/f1bf7c1c-d36b-4b7e-8624-93bf5cf8b80f
-- title:
--   Pullback of algebraic $n$-forms and pluricanonical forms from a ring to a field
-- statement:
--   Let $R\to A\to K$ be homomorphisms of commutative rings with $K$ a field, the composite being the structure map $R\to K$. Write $\Omega_{A/R}$ for the Kähler differentials, $d$ for the universal derivation, $\Omega^n_{A/R}=\bigwedge^n_A\Omega_{A/R}$, and $(\Omega^n_{A/R})^{\otimes m}$ for the $m$-fold tensor product over $A$; similarly for $K$, with tensor products over $K$.
--
--   1. **Canonical and pluricanonical modules.** The $A$-modules $\Omega^n_{A/R}$ and $(\Omega^n_{A/R})^{\otimes m}$, for $n,m\in\mathbb{N}$.
--   2. **Exterior pullback.** The $A$-linear map $e_n\colon\Omega^n_{A/R}\to\Omega^n_{K/R}$ induced by the map of differentials $\Omega_{A/R}\to\Omega_{K/R}$, $da\mapsto d\bar a$, where $\bar a$ is the image of $a$ in $K$:
--   $$da_1\wedge\cdots\wedge da_n\longmapsto d\bar a_1\wedge\cdots\wedge d\bar a_n .$$
--   3. **Pluricanonical pullback.** The $A$-linear map $\iota\colon(\Omega^n_{A/R})^{\otimes m}\to(\Omega^n_{K/R})^{\otimes m}$ that applies the exterior pullback of item 2 to each tensor factor: $\eta_1\otimes\cdots\otimes\eta_m\mapsto e_n(\eta_1)\otimes\cdots\otimes e_n(\eta_m)$.
--
--   In the main application $R=\mathbb{C}$, $A=\mathcal{O}_X(V)$ is the coordinate ring of a nonempty affine open $V$ of a smooth variety $X$ and $K=K(X)$ is its function field. Then $\iota$ sends algebraic pluricanonical forms on $V$ to rational pluricanonical forms on $X$, and the forms of the shape $\iota(q)$ are the ones that are regular on $V$; dividing $\iota(q)$ by a power of a local boundary equation produces the forms with logarithmic poles.
--
--   **Formalization Note** `Canonical` and `Pluricanonical` (here written as `⨂[A] (_ : Fin m), Canonical R A n`) restate in this namespace the modules of the same names used for general change of rings. `alternatingRestriction R A K n` is the wedge map into $\Omega^n_{K/R}$ regarded as an alternating $A$-multilinear map; `exteriorPullback R A K n` and `pluricanonicalPullback R A K n m` are items 2 and 3, built from Mathlib's `KaehlerDifferential.map R R A K`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/LocalCanonical.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/LocalCanonical.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LogKodairaFiberNegative mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
open scoped TensorProduct

namespace ReverseLogKodaira.LocalCanonical

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]

abbrev Canonical (n : ℕ) := ⋀[A]^n (KaehlerDifferential R A)
abbrev Pluricanonical (n m : ℕ) := ⨂[A] (_ : Fin m), Canonical R A n

 
def alternatingRestriction (n : ℕ) :
    (KaehlerDifferential R K) [⋀^Fin n]→ₗ[A] Canonical R K n where
  toMultilinearMap := (exteriorPower.ιMulti K n).toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' := (exteriorPower.ιMulti K n).map_eq_zero_of_eq

 
def exteriorPullback (n : ℕ) : Canonical R A n →ₗ[A] Canonical R K n :=
  exteriorPower.alternatingMapLinearEquiv
    ((alternatingRestriction R A K n).compLinearMap (KaehlerDifferential.map R R A K))

 
def pluricanonicalPullback (n m : ℕ) :
    Pluricanonical R A n m →ₗ[A] Pluricanonical R K n m :=
  PiTensorProduct.lift (((PiTensorProduct.tprod K).restrictScalars A).compLinearMap
    fun _ : Fin m => exteriorPullback R A K n)

 

end ReverseLogKodaira.LocalCanonical

end
end

end OAI


