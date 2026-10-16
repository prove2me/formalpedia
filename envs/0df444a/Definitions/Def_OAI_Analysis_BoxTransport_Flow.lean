-- Prove2me | Definitions.Def_OAI_Analysis_BoxTransport_Flow
-- name    : OAI_Analysis_BoxTransport_Flow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T13:06:29.360984+00:00
-- url     : https://prove2.me/theorems/981d20f9-35a7-488e-bcd1-21ed14842ed8
-- title:
--   Spatial curl, affine vector potentials and smooth cutoffs around moving boxes
-- statement:
--   This file sets up the building blocks of divergence-free velocity fields that move finitely many boxes, each by a translation combined with a diagonal stretching. Space-time points are written $p=(t,x)\in\mathbb{R}\times\mathbb{R}^3$ with $x=(x_0,x_1,x_2)$, a vector field is a map $\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$, and $e_0,e_1,e_2$ is the standard basis of $\mathbb{R}^3$. Let $\psi(y)=e^{-1/y}$ for $y>0$ and $\psi(y)=0$ for $y\le 0$, and let
--   $$S(y)=\frac{\psi(y)}{\psi(y)+\psi(1-y)}$$
--   be the standard smooth transition function: $S$ is $C^\infty$, takes values in $[0,1]$, vanishes on $(-\infty,0]$ and equals $1$ on $[1,\infty)$.
--
--   1. **Curl.** For a linear map $L:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ write $L_{ji}=\bigl(L(0,e_i)\bigr)_j$ and set
--   $$\operatorname{curl}L=\bigl(L_{21}-L_{12},\ L_{02}-L_{20},\ L_{10}-L_{01}\bigr),$$
--   a continuous linear function of $L$. The spatial curl of a vector field $A$ is $(\nabla_x\times A)(p)=\operatorname{curl}\bigl(DA(p)\bigr)$, where $DA(p)$ is the derivative of $A$ at $p$; for differentiable $A$ this is the usual $\bigl(\partial_{x_1}A_2-\partial_{x_2}A_1,\ \partial_{x_2}A_0-\partial_{x_0}A_2,\ \partial_{x_0}A_1-\partial_{x_1}A_0\bigr)$.
--
--   2. **Affine potential.** For $c,v,l\in\mathbb{R}^3$, indices $i,j\in\{0,1,2\}$ and $p=(t,x)$ let
--   $$\phi^{c,v,l}_{ij}(p)=\tfrac12\bigl(v_i(x_j-c_j)-v_j(x_i-c_i)\bigr)+\tfrac13(l_i-l_j)(x_i-c_i)(x_j-c_j),$$
--   and let $A^{c,v,l}=\bigl(\phi^{c,v,l}_{12},\ \phi^{c,v,l}_{20},\ \phi^{c,v,l}_{01}\bigr)$, a vector field that does not depend on $t$. A direct computation shows that if $l_0+l_1+l_2=0$ then $\nabla_x\times A^{c,v,l}(t,x)=v+\operatorname{diag}(l)\,(x-c)$, so $A^{c,v,l}$ is a vector potential for this affine velocity field.
--
--   3. **Moving potential.** For time-dependent parameters $c,v,l:\mathbb{R}\to\mathbb{R}^3$ the moving potential is $A_{c,v,l}(t,x)=A^{c(t),v(t),l(t)}(t,x)$.
--
--   4. **Moving box cutoff and plateau.** For a center path $c:\mathbb{R}\to\mathbb{R}^3$, a half-width path $r:\mathbb{R}\to\mathbb{R}^3$ and $\eta\in\mathbb{R}$,
--   $$\chi_{c,r,\eta}(t,x)=\prod_{j=0}^{2}S\Bigl(\frac{r_j(t)+2\eta+(x_j-c_j(t))}{\eta}\Bigr)\,S\Bigl(\frac{r_j(t)+2\eta-(x_j-c_j(t))}{\eta}\Bigr),$$
--   and the plateau is the set $P_{c,r,\eta}=\{(t,x):\ |x_j-c_j(t)|<r_j(t)+\eta\ \text{for } j=0,1,2\}$. The cutoff takes values in $[0,1]$; for $\eta>0$ it equals $1$ whenever $|x_j-c_j(t)|\le r_j(t)+\eta$ for all $j$ (in particular on the plateau) and vanishes as soon as $|x_j-c_j(t)|\ge r_j(t)+2\eta$ for some $j$.
--
--   5. **Localized and family potentials.** The localized potential is the product $\chi_{c,r,\eta}\,A_{c,v,l}$. For $n$ families of paths $c_i,v_i,l_i,r_i:\mathbb{R}\to\mathbb{R}^3$, $i=0,\dots,n-1$, the family potential is
--   $$\mathcal{A}(p)=\sum_{i=0}^{n-1}\chi_{c_i,r_i,\eta}(p)\,A_{c_i,v_i,l_i}(p).$$
--
--   6. **Affine trajectory and logarithmic velocity.** For paths $c,d:\mathbb{R}\to\mathbb{R}^3$ and points $a,x\in\mathbb{R}^3$, the affine trajectory is $T_{c,d,a}(x,t)_j=c_j(t)+d_j(t)\,(x_j-a_j)$, the image of $x$ under the diagonal affine map that sends $a$ to $c(t)$ and stretches the $j$-th coordinate by $d_j(t)$. The diagonal logarithmic velocity of $d$ is $\lambda_d(t)_j=d_j'(t)/d_j(t)$.
--
--   These objects are combined into a velocity field as the spatial curl of a family potential with $v_i=c_i'$ and $l_i=\lambda_{d_i}$; being a curl, such a field is divergence-free. If $d_{i,0}(t)d_{i,1}(t)d_{i,2}(t)=1$ for all $t$, then $l_{i,0}+l_{i,1}+l_{i,2}=0$, and at points of the plateau of the $i$-th box near which all other cutoffs vanish, the field equals $c_i'(t)+\operatorname{diag}(\lambda_{d_i}(t))\,(x-c_i(t))$, which is exactly the velocity of the affine trajectories $t\mapsto T_{c_i,d_i,a}(x,t)$. The cutoffs keep the contributions of different boxes apart as long as their enlarged boxes stay disjoint.
--
--   **Formalization Note** `spatialCurl A p = curlLinear (fderiv ℝ A p)` uses the Fréchet derivative on `ℝ × (Fin 3 → ℝ)`, which Lean takes to be $0$ where $A$ is not differentiable; `derivativeEntry i j` is the functional $L\mapsto L_{ji}$, and `derivativeEntry_apply`, `curlLinear_apply` are its evaluation lemmas. The potential pieces are `potentialComponent`, `affinePotential`, `movingAffinePotential`, `localizedPotential` and `familyPotential`; the cutoff `movingBoxCutoff` uses Mathlib's `Real.smoothTransition` (built from `expNegInvGlue`, which is $\psi$), and for $\eta=0$ Lean's convention $y/0=0$ makes it identically $0$. The plateau `movingPlateau` is defined through the enlarged open box `openBox`. `diagonalLogVelocity` uses `deriv`, also $0$ at points of non-differentiability, together with $y/0=0$; `affineTrajectory` is $T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Flow.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Flow.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedBoxRouting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry

namespace OAI

/-! Localized solenoidal moving fields and their unique global flows. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
noncomputable def derivativeEntry (i j : Fin 3) :
    (SpaceTime →L[ℝ] Space) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.apply ℝ Space) (coordinateDirection (some i)))

@[simp] theorem derivativeEntry_apply (i j : Fin 3) (L : SpaceTime →L[ℝ] Space) :
    derivativeEntry i j L = L (coordinateDirection (some i)) j := rfl

noncomputable def curlLinear : (SpaceTime →L[ℝ] Space) →L[ℝ] Space :=
  ContinuousLinearMap.pi
    ![derivativeEntry 1 2 - derivativeEntry 2 1,
      derivativeEntry 2 0 - derivativeEntry 0 2,
      derivativeEntry 0 1 - derivativeEntry 1 0]

@[simp] theorem curlLinear_apply (L : SpaceTime →L[ℝ] Space) :
    curlLinear L =
      ![L (coordinateDirection (some 1)) 2 - L (coordinateDirection (some 2)) 1,
        L (coordinateDirection (some 2)) 0 - L (coordinateDirection (some 0)) 2,
        L (coordinateDirection (some 0)) 1 - L (coordinateDirection (some 1)) 0] := by
  ext j
  fin_cases j <;> rfl

noncomputable def spatialCurl (A : Field) : Field := fun p => curlLinear (fderiv ℝ A p)

noncomputable def potentialComponent (c v l : Space) (i j : Fin 3) (p : SpaceTime) : ℝ :=
  (1 / 2 : ℝ) * (v i * (p.2 j - c j) - v j * (p.2 i - c i)) +
    ((1 / 3 : ℝ) * (l i - l j)) * ((p.2 i - c i) * (p.2 j - c j))

noncomputable def affinePotential (c v l : Space) : Field := fun p =>
  ![potentialComponent c v l 1 2 p, potentialComponent c v l 2 0 p,
    potentialComponent c v l 0 1 p]

noncomputable def movingAffinePotential (c v l : ℝ → Space) : Field :=
  fun p => affinePotential (c p.1) (v p.1) (l p.1) p

noncomputable def movingBoxCutoff (c r : ℝ → Space) (η : ℝ) (p : SpaceTime) : ℝ :=
  ∏ j : Fin 3,
    Real.smoothTransition ((r p.1 j + 2 * η + (p.2 j - c p.1 j)) / η) *
    Real.smoothTransition ((r p.1 j + 2 * η - (p.2 j - c p.1 j)) / η)

def movingPlateau (c r : ℝ → Space) (η : ℝ) : Set SpaceTime :=
  {p | p.2 ∈ openBox (c p.1) (r p.1) η}

noncomputable def localizedPotential (c v l r : ℝ → Space) (η : ℝ) : Field :=
  fun p => movingBoxCutoff c r η p • movingAffinePotential c v l p

noncomputable def familyPotential {n : ℕ}
    (c v l r : Fin n → ℝ → Space) (η : ℝ) : Field :=
  fun p => ∑ i, localizedPotential (c i) (v i) (l i) (r i) η p

def affineTrajectory (c d : ℝ → Space) (a x : Space) (t : ℝ) : Space :=
  fun j => c t j + d t j * (x j - a j)

noncomputable def diagonalLogVelocity (d : ℝ → Space) (t : ℝ) : Space :=
  fun j => deriv d t j / d t j

end BoxTransport.Routing

end

end OAI


