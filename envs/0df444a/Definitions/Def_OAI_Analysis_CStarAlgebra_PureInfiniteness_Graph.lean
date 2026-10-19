-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:38:55.208999+00:00
-- url     : https://prove2.me/theorems/5adbff6f-a745-44a8-bc68-00d64d859ef2
-- title:
--   Graph words over six orthogonal slots and measurements that recover four contractions
-- statement:
--   Let $A$ be a $C^*$-algebra, not necessarily unital, and $D$ a unital $C^*$-algebra, both with their usual orders. For $h$ in either algebra, $\operatorname{Her}(h)$ is the norm closure of $\{hah^*\}$, $a$ ranging over the algebra. A system of $n$ orthogonal slots from $h$ to $v$ is a family of bounded linear maps $S_0,\dots,S_{n-1}$ from $\operatorname{Her}(h)$ to the algebra with $S_i(k)^*S_j(l)=\delta_{ij}k^*l$, $S_i(k)S_j(l)^*\in\operatorname{Her}(v)$ and $S_i(kl)=S_i(k)l$ for all $k,l\in\operatorname{Her}(h)$, where $\delta_{ij}$ is the Kronecker delta.
--
--   1. **Graph word.** Given $n$ orthogonal slots $S$ from $h$ to $v$ in $A$ and coefficients $R_0,\dots,R_{n-1}\in A$ with $R_ik\in\operatorname{Her}(h)$ for all $k\in\operatorname{Her}(h)$, the graph word of $k\in\operatorname{Her}(h)$ is
--
--      $$
--      G_S(R;k)=\sum_{i=0}^{n-1}S_i(R_ik).
--      $$
--
--   2. **Graph complement and coefficients.** For $T_0,\dots,T_3\in D$ let
--
--      $$
--      C(T)=\sqrt{\frac{15-\sum_{i=0}^{3}T_i^*T_i}{16}},
--      $$
--
--      computed by the continuous functional calculus of the self-adjoint element $\sum_iT_i^*T_i$ with the convention $\sqrt{s}=0$ for $s<0$, and let the six graph coefficients be
--
--      $$
--      c(T)=\bigl(\tfrac14\cdot1,\ \tfrac14T_0,\ \tfrac14T_1,\ \tfrac14T_2,\ \tfrac14T_3,\ C(T)\bigr).
--      $$
--
--      When every $\|T_i\|\le1$, the radicand is bounded below by $\tfrac{11}{16}$ and $\sum_jc_j(T)^*c_j(T)=1$. If $T_i\in\operatorname{Her}(h)$ for all $i$, then $c_j(T)k\in\operatorname{Her}(h)$ for all $j$ and all $k\in\operatorname{Her}(h)$; more generally $f(q)k\in\operatorname{Her}(h)$ for every self-adjoint $q\in\operatorname{Her}(h)$, continuous $f:\mathbb{R}\to\mathbb{R}$ and $k\in\operatorname{Her}(h)$.
--
--   3. **Regularised inverse.** Let $g(t)=t/\max(\tfrac1{32},t)^2$, so that $g(t)=1/t$ for $t\ge\tfrac1{32}$ and $g(t)=1024\,t$ for $t\le\tfrac1{32}$. For self-adjoint $X\in A$, $X^{\dagger}=g(X)$ by the continuous functional calculus.
--
--   4. **Graph construction.** Let $h,a,t\in D$ with $t\ge0$ and $t\in\operatorname{Her}(h)$, let $V_0,\dots,V_5$ be six orthogonal slots from $h$ to $a$, and put $w_i=V_i(t)$. For $T_0,\dots,T_3\in\operatorname{Her}(h)$ and $F\in D$ define
--
--      $$
--      Z=\sum_{i=0}^{5}V_i\bigl(c_i(T)\sqrt t\bigr),\qquad P=ZZ^*,\qquad X_F=16\,w_0^*Fw_0,\qquad B_{F,i}=16\,w_{i+1}^*\,F\,w_0\,X_F^{\dagger}\quad(i=0,\dots,3).
--      $$
--
--   5. **Abstract measurements.** For arbitrary $w_0,\dots,w_5,F\in D$ the same formulas define $\mathsf{X}(w_0,F)=16\,w_0^*Fw_0$ and $\mathsf{B}_i(w,F)=16\,w_{i+1}^*Fw_0\,\mathsf{X}(w_0,F)^{\dagger}$ for $i=0,\dots,3$.
--
--   The element $Z$ encodes the column $\bigl(\tfrac14,\tfrac14T_0,\dots,\tfrac14T_3,C(T)\bigr)$, the graph of the quadruple $T$, in six orthogonal copies of $\operatorname{Her}(h)$ inside $\operatorname{Her}(a)$, and the measurements read it back. In the surrounding development it is shown that if $z^*z=t$ for a positive contraction $t$, the slot relations $w_0^*z=\tfrac14t\sqrt t$ and $w_{i+1}^*z=\tfrac14tT_i\sqrt t$ hold, $y\ge0$, $\|c\|\le1$, the $T_i$ satisfy a support condition, and $y\bigl(1-c^*(zz^*)^2c\bigr)y=0$, then $\|\mathsf{X}(w_0,cyc^*)\|=\|y\|$ and $\mathsf{B}_i(w,cyc^*)=T_i$ for every $i$. Combined with four-choice avoidance this yields the following: in a unital $C^*$-algebra, if $a,y\ge0$, $\|c\|\le1$ and every positive element $h$ of $\operatorname{Her}(a)$ is properly infinite ($\operatorname{diag}(h,h)$ is a norm limit of $r_j^*hr_j$ with row vectors $r_j$ of length $2$), then there is a positive contraction $p\in\operatorname{Her}(a)$ with $\|\pi(p)\|=1$ for every unital Hilbert-space representation $\pi$ with $\|\pi(a)\|>\tfrac12$, while every such representation that kills $y(1-c^*p^2c)y$ has $\|\pi(y)\|\le\tfrac14$.
--
--   **Formalization Note** Lean names: `OrthogonalSlots.graphWord`, `cfc_mul_mem_Her`, `graphComplement`, `graphComplement_mul_mem`, `graphCoeffs` (a 6-tuple indexed by `Fin 6`), `graphCoeffs_mem`, `graphInverseFn`, `graphInverse` (non-unital functional calculus, $0$ for non-self-adjoint input), `graphSlot`, `graphZ`, `graphP`, `graphX`, `graphB`, `measurementX` and `measurementB`. The index $i+1$ is written `i.castSucc.succ`. The coefficient $\tfrac14$ and the factor $16$ are real scalars. Where an order is needed, the sections work with any order making the algebra a star-ordered ring (for a $C^*$-algebra, the usual one); the final local instances fix Mathlib's spectral order on a unital `A` and on operator algebras of Hilbert spaces for the lemmas of the module. The identity for $\sum_jc_j^*c_j$ is proved elsewhere in the development.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Graph.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Graph.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndividualStrongInfiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
namespace OrthogonalSlots
section GraphAlgebra
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

def graphWord (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (k : Her h) : A := ∑ i, S.carrier i ⟨R i * (k : A), hR i k⟩

end GraphAlgebra
end OrthogonalSlots

section UnitalGraph
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma cfc_mul_mem_Her {h q : D} (hq : q ∈ Her h) (hqa : IsSelfAdjoint q)
    (f : ℝ → ℝ) (hf : Continuous f) {k : D} (hk : k ∈ Her h) :
    cfc f q * k ∈ Her h := by
  have hm : cfcₙ (fun x => f x - f 0) q ∈ Her h := cfcₙ_mem (𝕜' := ℂ) _ hq
  have he : cfcₙ (fun x => f x - f 0) q = cfc f q - (f 0) • (1 : D) := by
    rw [cfcₙ_eq_cfc (f := fun x => f x - f 0) (a := q) ((hf.sub continuous_const).continuousOn) (by simp),
      cfc_sub f (fun _ => f 0) q hf.continuousOn continuous_const.continuousOn,
      cfc_const _ q hqa, Algebra.algebraMap_eq_smul_one]
  have he' : cfc f q = cfcₙ (fun x => f x - f 0) q + (f 0) • (1 : D) := by rw [he]; abel
  rw [he', add_mul, smul_mul_assoc, one_mul]
  exact (Her h).add_mem ((Her h).mul_mem hm hk) (real_smul_mem_Her hk _)

def graphComplement (S : Fin 4 → D) : D :=
  cfc (fun t : ℝ => Real.sqrt ((15-t)/16)) (∑ i, star (S i)*S i)

lemma graphComplement_mul_mem {h : D} (S : Fin 4 → D) (hS : ∀ i, S i ∈ Her h)
    {k : D} (hk : k ∈ Her h) : graphComplement S * k ∈ Her h := by
  apply cfc_mul_mem_Her ?_ ?_ _ (by fun_prop) hk
  · exact (Her h).sum_mem fun i _ => (Her h).mul_mem (StarMemClass.star_mem (s := Her h) (hS i)) (hS i)
  · exact (Finset.sum_nonneg fun i _ => star_mul_self_nonneg (S i)).isSelfAdjoint

def graphCoeffs (T : Fin 4 → D) : Fin 6 → D :=
  ![(1/4 : ℝ) • 1, (1/4 : ℝ) • T 0, (1/4 : ℝ) • T 1,
    (1/4 : ℝ) • T 2, (1/4 : ℝ) • T 3, graphComplement T]

lemma graphCoeffs_mem {h : D} (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h)
    (i : Fin 6) (k : Her h) : graphCoeffs T i * (k : D) ∈ Her h := by
  fin_cases i <;> dsimp [graphCoeffs] <;> try simp only [smul_mul_assoc, one_mul]
  · exact real_smul_mem_Her k.property _
  · exact real_smul_mem_Her ((Her h).mul_mem (hT 0) k.property) _
  · exact real_smul_mem_Her ((Her h).mul_mem (hT 1) k.property) _
  · exact real_smul_mem_Her ((Her h).mul_mem (hT 2) k.property) _
  · exact real_smul_mem_Her ((Her h).mul_mem (hT 3) k.property) _
  · exact graphComplement_mul_mem T hT k.property

end UnitalGraph
def graphInverseFn (t : ℝ) : ℝ := t / (max (1/32 : ℝ) t)^2

def graphInverse (X : A) : A := cfcₙ graphInverseFn X

section InverseOrder
variable [PartialOrder A] [StarOrderedRing A]

end InverseOrder
section GraphDefect
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end GraphDefect

section GraphConstruction
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable {h a t : D} (V : OrthogonalSlots 6 h a) (ht : 0 ≤ t) (htH : t ∈ Her h)

def graphSlot (i : Fin 6) : D := V.carrier i ⟨t, htH⟩

def graphZ (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) : D :=
  V.graphWord (graphCoeffs T) (graphCoeffs_mem T hT) ⟨CFC.sqrt t, sqrt_mem_Her htH ht⟩

def graphP (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) : D :=
  graphZ V ht htH T hT * star (graphZ V ht htH T hT)

def graphX (F : D) : D := (16 : ℝ) • (star (graphSlot V htH 0) * F * graphSlot V htH 0)

def graphB (F : D) (i : Fin 4) : D := (16 : ℝ) •
  (star (graphSlot V htH i.castSucc.succ) * F * graphSlot V htH 0 * graphInverse (graphX V htH F))

end GraphConstruction

section AbstractMeasurements
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def measurementX (w F : D) : D := (16 : ℝ) • (star w*F*w)
def measurementB (w : Fin 6 → D) (F : D) (i : Fin 4) : D :=
  (16 : ℝ) • (star (w i.castSucc.succ)*F*w 0*graphInverse (measurementX (w 0) F))

end AbstractMeasurements

section RepresentedGraph
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
variable (π : D →⋆ₐ[ℂ] E) {h a t : D} (V : OrthogonalSlots 6 h a)
  (ht : 0 ≤ t) (htH : t ∈ Her h)

end RepresentedGraph

end MainGap

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
local instance graphNonvanishingOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance graphNonvanishingStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance graphOperatorOrder (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] :
    PartialOrder (J →L[ℂ] J) := CStarAlgebra.spectralOrder _
local instance graphOperatorStarOrder (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J] :
    StarOrderedRing (J →L[ℂ] J) := CStarAlgebra.spectralOrderedRing _

end MainGap

end

end OAI


