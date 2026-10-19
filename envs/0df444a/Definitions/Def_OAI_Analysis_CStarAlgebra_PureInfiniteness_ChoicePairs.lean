-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:28:01.217462+00:00
-- url     : https://prove2.me/theorems/ce2a0d15-ed23-4286-a562-abdf5633e2e1
-- title:
--   Sandwiches, scaling isometries, defects and cut-downs used to choose four test elements
-- statement:
--   Let $A$ be a unital $C^*$-algebra with its usual order. Notation: for self-adjoint $d\in A$ and $\varepsilon\ge0$, $(d-\varepsilon)_+$ is $d$ under the continuous functional calculus with $t\mapsto\max(t-\varepsilon,0)$; for $0\le l<u$, $\theta_{l,u}(d)$ is $d$ under the ramp $t\mapsto\min\bigl(1,\max(t-l,0)/(u-l)\bigr)$; $\sqrt{\cdot}$ is the positive square root of a positive element; and $\operatorname{Her}(h)=\overline{hAh^*}$ is the norm closure of $\{hah^*: a\in A\}$. The file defines the following elements.
--
--   1. **First sandwich.** For $U,V\in A$, $\eta\in\mathbb{R}$ and a finite set $E\subseteq A$,
--
--      $$
--      \Sigma(U,V,\eta,E)=(U-\eta)_+\Bigl(\sum_{w\in E}wVw^*\Bigr)(U-\eta)_+ .
--      $$
--
--   2. **Scaling isometry and defect.** For $H,r\in A$,
--
--      $$
--      \gamma(H)=\sqrt{1-H^2},\qquad W(H,r)=r+\gamma(H),\qquad P(H,r)=1-W(H,r)\,W(H,r)^* .
--      $$
--
--      If $H$ is a self-adjoint contraction and $r$ satisfies $Hr=r$ and $r^*r=H^2$, then $W(H,r)$ is an isometry and $P(H,r)$ is a projection, the defect projection of $W(H,r)$.
--
--   3. **Deficiency.** For self-adjoint $d$, $\delta(d)=\max(\tfrac12-d,0)$, that is, $d$ under the functional calculus with $t\mapsto\max(\tfrac12-t,0)$.
--
--   4. **First-pair data.** For $X,B\in A$,
--
--      $$
--      X_1=(X-\tfrac1{16})_+,\quad V_1=(X-\tfrac18)_+,\quad U_1=X_1\,\delta(BB^*)^2\,X_1,\quad H_1=\theta_{3/32,\,1/8}(X),\quad K_1=\theta_{3/64,\,1/16}(X),\quad R_1=\sqrt2\,B^*H_1 .
--      $$
--
--   5. **Prospective defect.** $Q(X,B)=\theta_{0,1}\bigl(K_1\,P(H_1,R_1)\,K_1\bigr)$, the compression of the scaling defect by $K_1$, clipped to $[0,1]$ by $\theta_{0,1}(t)=\min(1,\max(t,0))$.
--
--   6. **Last-pair data.** For $X,B_1,B_3\in A$,
--
--      $$
--      X_2=\bigl(Q(X,B_1)-\tfrac12\bigr)_+,\qquad R_2(X,B_1,B_3)=X_2\,\delta(B_3B_3^*)^2\,X_2 .
--      $$
--
--   7. **Working hereditary subalgebra.** $\operatorname{Her}_4(X)=\operatorname{Her}\bigl((X-\tfrac1{32})_+\bigr)$.
--
--   These elements are the explicit ingredients of the four-choice avoidance argument. Given a positive $X$ and four elements $B_0,\dots,B_3$ (of which $B_0$ and $B_2$ enter the formulas, through $U_1$, $Q(X,B_0)$ and $R_2(X,B_0,B_2)$), one chooses four contractions in $\operatorname{Her}_4(X)$ whose moduli are controlled by $\Sigma(U_1,V_1,\eta,E)$ and by $(R_2-\eta)_+$. For positive $X$ the elements $X_1,V_1,U_1,K_1,Q,X_2,R_2$ all lie in $\operatorname{Her}_4(X)$.
--
--   **Formalization Note** Lean names: `firstSandwich U V η E`, `scalingComplement H` (written with `H * H` and Mathlib's `CFC.sqrt`, which is $0$ on non-positive arguments), `scalingIsometry`, `scalingDefect`, `deficiency` (unital functional calculus, $0$ for non-self-adjoint input), `firstX`, `firstV`, `firstU`, `firstH`, `firstK`, `firstR` (with the real scalar $\sqrt2$), `prospectiveDefect`, `lastX X B`, `lastR X B₁ B₃` and `fourHer X`; cut-downs and ramps are the functions `cut` and `ramp` of earlier files. The first four definitions are stated for any order making `A` a star-ordered ring, the others for Mathlib's spectral order. The facts quoted above (isometry, projection, membership in the working subalgebra) are proved in the surrounding development.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/ChoicePairs.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/ChoicePairs.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance choicePairsPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance choicePairsStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def firstSandwich (U V : A) (η : ℝ) (E : Finset A) : A :=
  cut U η * (∑ w ∈ E, w * V * star w) * cut U η

end MainGap

namespace MainGap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def scalingComplement (H : A) : A := CFC.sqrt (1 - H * H)

def scalingIsometry (H r : A) : A := r + scalingComplement H

def scalingDefect (H r : A) : A := 1 - scalingIsometry H r * star (scalingIsometry H r)

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance instPartialOrder_oAI : PartialOrder A := CStarAlgebra.spectralOrder A
local instance instStarOrderedRing_oAI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

def deficiency (d : A) : A := cfc (fun t : ℝ => max ((1/2 : ℝ)-t) 0) d

def firstX (X : A) : A := cut X (1/16)
def firstV (X : A) : A := cut X (1/8)
def firstU (X B : A) : A := firstX X * deficiency (B * star B) *
  deficiency (B * star B) * firstX X

def firstH (X : A) : A := ramp X (3/32) (1/8)
def firstK (X : A) : A := ramp X (3/64) (1/16)
def firstR (X B : A) : A := (Real.sqrt 2) • (star B * firstH X)
def prospectiveDefect (X B : A) : A :=
  ramp (firstK X * scalingDefect (firstH X) (firstR X B) * firstK X) 0 1

def lastX (X B : A) : A := cut (prospectiveDefect X B) (1/2)
def lastR (X B₁ B₃ : A) : A := lastX X B₁ * deficiency (B₃ * star B₃) *
  deficiency (B₃ * star B₃) * lastX X B₁

def fourHer (X : A) : NonUnitalStarSubalgebra ℂ A := Her (cut X (1/32))

end MainGap

end

end OAI


