-- Prove2me | Definitions.Def_AutomorphicForm_UnipotentQuotient
-- name    : AutomorphicForm_UnipotentQuotient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/53fde1cc-66e2-5240-8695-db039052a043
-- title:
--   Adelic unipotent subgroup, its Haar measure, quotient measure
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring and $\mathrm{GL}_2(\mathbb{A}_K)$ the adelic general linear group, both carrying the Borel $\sigma$-algebras of their adelic topologies. Four objects are introduced. First, `adelicUnipotent K` is the range of the homomorphism `unipotentGL2Hom` over $\mathbb{A}_K$, i.e. the subgroup $N(\mathbb{A}_K)=\{\,n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix} : x\in\mathbb{A}_K\,\}$ of $\mathrm{GL}_2(\mathbb{A}_K)$, obtained from the additive group $\mathbb{A}_K$ viewed multiplicatively via $n(x+y)=n(x)n(y)$. Second, `UnipotentQuotient K` is the orbit space of the left multiplication action of that subgroup on $\mathrm{GL}_2(\mathbb{A}_K)$, that is the coset space $N(\mathbb{A}_K)\backslash\mathrm{GL}_2(\mathbb{A}_K)$, with the quotient measurable structure. Third, `toAdelicUnipotent K` is the surjection $x\mapsto n(x)$ from $\mathbb{A}_K$ onto $N(\mathbb{A}_K)$, the homomorphism $n$ restricted to its range. Fourth, `unipotentHaar K` is the image under this surjection of the additive Haar measure `adelicAddHaar` of $\mathbb{A}_K$ rescaled by the factor $\bigl(\mathrm{vol}(\mathtt{adelicBox}\,K)\bigr)^{-1}$, where `adelicBox K` consists of the adeles whose infinite component lies in the preimage of the fundamental domain of the lattice basis of $K$ in the mixed space and whose finite component is integral at every finite place; thus the scaling is the one making that box have total mass one.
--
--   Finally, `unipotentQuotientMeasure K` is the measure on $N(\mathbb{A}_K)\backslash\mathrm{GL}_2(\mathbb{A}_K)$ given by [`HaarQuotient.measure`](../def/HaarQuotient.html#L28) applied to the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb{A}_K)$, the subgroup $N(\mathbb{A}_K)$ and the measure `unipotentHaar K`: the pushforward along the quotient map of `adelicGLHaar` weighted by the density $g\mapsto w(g)\big/\int_{N(\mathbb{A}_K)} w(xg)\,d\,\mathtt{unipotentHaar}(x)$, with $w$ the weight function built from a compact exhaustion of the group.
--
--   **Relation to Mathlib.** The underlying Haar measures are Mathlib's `Measure.addHaar` and `Measure.haar` for the adelic topologies; the coset space is Mathlib's orbit-space quotient. The density-and-pushforward construction [`HaarQuotient.measure`](../def/HaarQuotient.html#L28) used for the quotient measure is the project's own, rather than Mathlib's quotient-Haar machinery for discrete subgroups with a fundamental domain.
--
--   **Where it is used.** These objects provide the adelic unipotent group and the measures in which the constant term of an adelic automorphic form on $\mathrm{GL}_2$ (integration over $N(\mathbb{A}_K)$, normalised as here) and the $L^2$ condition on $N(\mathbb{A}_K)\backslash\mathrm{GL}_2(\mathbb{A}_K)$ are formulated, on the automorphic side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_UnipotentQuotient.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type*) [Field K] [NumberField K]

abbrev adelicUnipotent : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (unipotentGL2Hom (R := AdeleRing (𝓞 K) K)).range

abbrev UnipotentQuotient : Type _ :=
  MulAction.orbitRel.Quotient (adelicUnipotent K) (AdelicGL2 (𝓞 K) K)

def toAdelicUnipotent (x : AdeleRing (𝓞 K) K) : adelicUnipotent K :=
  (unipotentGL2Hom (R := AdeleRing (𝓞 K) K)).rangeRestrict (Multiplicative.ofAdd x)

def unipotentHaar : Measure (adelicUnipotent K) :=
  Measure.map (toAdelicUnipotent K)
    (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K)

def unipotentQuotientMeasure : Measure (UnipotentQuotient K) :=
  HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) (adelicUnipotent K) (unipotentHaar K)

end AutomorphicForm

end


