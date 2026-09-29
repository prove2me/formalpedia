-- Prove2me | Definitions.Def_MvFormalGroup_FirstOrderDeformation
-- name    : MvFormalGroup_FirstOrderDeformation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/6d23db7f-7dcc-5a41-9794-7613de473cb9
-- title:
--   First-order deformations of a multivariate formal group law
-- statement:
--   Throughout, $k$ is a field and $d$ a natural number, and $k$ is viewed as an algebra over the dual numbers $k[\varepsilon] =$ `DualNumber k` through the ring homomorphism `TrivSqZeroExt.fstHom` sending $a + b\varepsilon$ to $a$; this algebra structure is recorded by `dualNumberResidueAlgebra` and installed as a local instance, so that `Deformation G₀ (DualNumber k)` is available for a $d$-dimensional formal group law $G_0$ over $k$ — a law $F$ over $k[\varepsilon]$ together with the equality `F.map (algebraMap _ _) = G₀` of laws over $k$.
--
--   For such a deformation $D$, `epsPart G₀ D` is the $d$-tuple of multivariate power series in the variable set $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ over $k$ defined coefficientwise: the coefficient at a monomial $n$ of its $i$-th component is the $\varepsilon$-part (`TrivSqZeroExt.snd`) of the coefficient of $n$ in the $i$-th component series of $D.F$. Thus $D.F = G_0 + \varepsilon\,\mathrm{epsPart}(D)$.
--
--   `firstOrderCocycles G₀` is the $k$-submodule of $(\mathrm{Fin}\,d \to k[[X,Y]])$ spanned by the image under `epsPart G₀` of the set of deformations $D$ whose law $D.F$ satisfies the commutativity relation `IsComm` (invariance of the components under swapping the two blocks of variables). `firstOrderCoboundaries G₀` is the $k$-span of the `epsPart` of those commutative $D$ for which there exists a deformation $D'$ with `epsPart G₀ D' = 0` and `D.IsIso D'`, i.e. a homomorphism $D.F \to D'.F$ admitting a two-sided inverse homomorphism and reducing to the identity $X_i \mapsto X_i$ modulo $\varepsilon$. Finally `firstOrderDeformationSpace G₀` is the quotient type $Z/(B \cap Z)$, the quotient of `firstOrderCocycles G₀` by the preimage of `firstOrderCoboundaries G₀` under its inclusion. Both $Z$ and $B$ are taken as spans, so no closure property of the sets of $\varepsilon$-parts is presupposed.
--
--   **Relation to Mathlib.** Dual numbers and the trivial square-zero extension, including `TrivSqZeroExt.fstHom` and `TrivSqZeroExt.snd`, are Mathlib's; multivariate formal group laws, their deformations and the present first-order objects are the project's own, built on Mathlib's `MvPowerSeries` substitution API.
--
--   **Where it is used.** These are the objects occurring in the tangent-space bound for the deformation functor of a commutative formal group law of finite height, $\dim_k Z/B \le d(h-d)$, and in the Serre–Tate-style analysis of lifts of a formal group along a small surjection that feeds the deformation theory used in the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_FirstOrderDeformation.lean

import Mathlib
import Definitions.Def_MvFormalGroup_Deformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace MvFormalGroup

variable {k : Type} [Field k] {d : ℕ}

@[reducible] def dualNumberResidueAlgebra (k : Type) [Field k] : Algebra (DualNumber k) k :=
  (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra

attribute [local instance] dualNumberResidueAlgebra

def epsPart (G₀ : MvFormalGroup d k) (D : Deformation G₀ (DualNumber k)) :
    Fin d → MvPowerSeries (Fin d ⊕ Fin d) k :=
  fun i n => TrivSqZeroExt.snd (MvPowerSeries.coeff n (D.F.toPowerSeries i))

def firstOrderCocycles (G₀ : MvFormalGroup d k) : Submodule k (Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :=
  Submodule.span k (epsPart G₀ '' {D | D.F.IsComm})

def firstOrderCoboundaries (G₀ : MvFormalGroup d k) : Submodule k (Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :=
  Submodule.span k (epsPart G₀ ''
    {D | D.F.IsComm ∧ ∃ D' : Deformation G₀ (DualNumber k), D.IsIso D' ∧ epsPart G₀ D' = 0})

abbrev firstOrderDeformationSpace (G₀ : MvFormalGroup d k) : Type :=
  ↥(firstOrderCocycles G₀) ⧸ (firstOrderCoboundaries G₀).comap (firstOrderCocycles G₀).subtype

end MvFormalGroup

end


