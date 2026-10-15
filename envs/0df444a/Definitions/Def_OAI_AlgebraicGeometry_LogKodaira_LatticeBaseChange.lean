-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange
-- name    : OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:52:20.094793+00:00
-- url     : https://prove2.me/theorems/2371c838-1d53-43a5-bf54-1cb0fdc938a3
-- title:
--   The $A$-lattice spanned by pluricanonical symbols $\bigotimes_j(da_{j,1}\wedge\cdots\wedge da_{j,n})$ with entries from a ring $A$ mapping to $K$
-- statement:
--   Let $R\to A\to K$ be homomorphisms of commutative rings, the composite being the structure map $R\to K$, and let $n,m\in\mathbb{N}$. Write $\Omega_{K/R}$ for the Kähler differentials of $K$ over $R$, $d\colon K\to\Omega_{K/R}$ for the universal derivation, and
--   $$\omega^{n,m}_{K/R}:=\big(\textstyle\bigwedge^n_K\Omega_{K/R}\big)^{\otimes_K m}$$
--   for the module of pluricanonical forms of degree $n$ and weight $m$. The *rational lattice* of $A$ in $\omega^{n,m}_{K/R}$ is the $A$-submodule
--   $$\Lambda^{n,m}_A:=\operatorname{span}_A\Big\{\textstyle\bigotimes_{j=1}^m\big(d\bar a_{j,1}\wedge\cdots\wedge d\bar a_{j,n}\big)\ :\ a_{j,i}\in A\ \text{for } 1\le j\le m,\ 1\le i\le n\Big\}\subseteq\omega^{n,m}_{K/R},$$
--   where $\bar a$ is the image of $a$ in $K$ and $A$ acts on $\omega^{n,m}_{K/R}$ through $A\to K$.
--
--   For a smooth projective variety $X$ over $\mathbb{C}$ with function field $K=K(X)$, a nonempty affine open $W\subseteq X$, $A=\mathcal{O}_X(W)$ and $n=\dim X$, this is the lattice $L_m(W)$ of rational $m$-pluricanonical forms regular on $W$; log pluriforms are defined by the condition $t^m s\in L_m(W)$ for local equations $t$ of the boundary. Formulating the lattice for an arbitrary ring $A$ mapping to $K$ makes it possible to compare the lattices of different rings, for instance of $A$ and of a localization of $A$, which is how regularity of pluricanonical forms is shown to be a local property.
--
--   **Formalization Note** The lattice is `rationalLattice R A K n m`, a `Submodule A (Pluricanonical R K n m)`; here $K$ is only required to be a commutative ring, and the generators are indexed by the matrices `a : Fin m → Fin n → A`. With $R=\mathbb{C}$, $A=\mathcal{O}_X(W)$, $K=K(X)$ and $n=\dim X$ it has the same generators as `regularPluriformLattice` from the basic definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/LatticeBaseChange.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/LatticeBaseChange.lean by skeleton subtraction
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
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts

-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
end TensorProduct
end Lean433TensorProductCompatibility

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.DifferentialBaseChange
section Span
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N]

end Span

 

end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.DifferentialBaseChange

 

def rationalLattice (R A K : Type*) [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    (n m : ℕ) : Submodule A (Pluricanonical R K n m) :=
  Submodule.span A (Set.range fun a : Fin m → Fin n → A =>
    PiTensorProduct.tprod K fun j => exteriorPower.ιMulti K n fun i =>
      KaehlerDifferential.D R K (algebraMap A K (a j i)))

section LatticeProofs
variable (R A K : Type*) [CommRing R] [CommRing A] [CommRing K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]

end LatticeProofs

 

end ReverseLogKodaira.DifferentialBaseChange

end

end OAI


