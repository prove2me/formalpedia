-- Prove2me | Definitions.Def_OAI_Analysis_BoxTransport_Routing
-- name    : OAI_Analysis_BoxTransport_Routing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T13:10:48.8725+00:00
-- url     : https://prove2.me/theorems/c47fd407-3aa2-4487-abcb-5ada7869c664
-- title:
--   Expression-representability of the box-routing potentials and their spatial curl
-- statement:
--   Throughout, $p=(t,x)$ is a point of space-time $\mathbb{R}\times\mathbb{R}^3$ and the coordinates of $x\in\mathbb{R}^3$ are numbered $1,2,3$. Let $\psi(y)=e^{-1/y}$ for $y>0$ and $\psi(y)=0$ for $y\le 0$, and put
--
--   $$S(y)=\frac{\psi(y)}{\psi(y)+\psi(1-y)},\qquad \phi_m(y)=y^{-m}\psi(y)\quad(m\in\mathbb{N}).$$
--
--   $S$ is the standard smooth transition function ($C^\infty$, with values in $[0,1]$, equal to $0$ on $(-\infty,0]$ and to $1$ on $[1,\infty)$), and $\phi_m$ is a flat function vanishing on $(-\infty,0]$.
--
--   **Representable functions.** An *expression* is a finite tree whose leaves are the coordinate functions $t,x_1,x_2,x_3$ and whose internal nodes are sums, products, negations, rational constants, flat functions $\phi_m(e)$ of a subexpression $e$, and reciprocals $1/e$, each reciprocal node carrying a guard $b\in\mathbb{N}$. An expression is *valid* if for every reciprocal node with guard $b$ the subexpression $e$ below it satisfies $|e(p)|\ge 1/(b+1)$ at every point $p\in\mathbb{R}\times\mathbb{R}^3$. A function $f:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$ is *representable* if it is the value function of a valid expression; a function of $t$ alone is called representable if $(t,x)\mapsto f(t)$ is.
--
--   **Routing data.** Fix $n$ boxes indexed by $i\in\{0,\dots,n-1\}$, with rational centers $a_i,b_i\in\mathbb{Q}^3$ and rational half-widths $h_i,k_i\in\mathbb{Q}^3$. Put $\sigma_s(t)=S(10t-\tfrac52-s)$ for $s=0,1,2,3,4$ (the stage switches), $s_{ij}=k_{ij}/h_{ij}$ (scale ratios) and $\lambda_{ij}(t)=1-\sigma_2(t)+\sigma_2(t)\,s_{ij}$. Let $\rho^a_i$ be the number of indices $i'$ with $(a_{i'1},i')<(a_{i1},i)$ in the lexicographic order of $\mathbb{Q}\times\mathbb{N}$ (the rank of box $i$ by first coordinate, ties broken by index), and define $\rho^b_i$ in the same way from the numbers $b_{i'1}$. For $D\in\mathbb{R}$ the route center $c_i(t)$ and the route scale $d_i(t)$ of box $i$ are
--
--   $$c_{i1}(t)=a_{i1}+\sigma_0(t)\,D\rho^a_i+\sigma_2(t)\big(b_{i1}+D\rho^b_i-a_{i1}-D\rho^a_i\big)-\sigma_4(t)\,D\rho^b_i,$$
--
--   $$c_{i2}(t)=a_{i2}+\sigma_2(t)\,(b_{i2}-a_{i2}),\qquad c_{i3}(t)=a_{i3}+\sigma_1(t)\,(Di-a_{i3})+\sigma_3(t)\,(b_{i3}-Di),$$
--
--   $$d_i(t)=\Big(\lambda_{i1}(t),\ \lambda_{i2}(t),\ \big(\lambda_{i1}(t)\,\lambda_{i2}(t)\big)^{-1}\Big).$$
--
--   **Potentials and curl.** For curves $c,v,l,r:\mathbb{R}\to\mathbb{R}^3$ and $\eta\in\mathbb{R}$ write $y=x-c(t)$ and
--
--   $$P_{jk}(t,x)=\tfrac12\big(v_j(t)\,y_k-v_k(t)\,y_j\big)+\tfrac13\big(l_j(t)-l_k(t)\big)\,y_j\,y_k,\qquad A_{c,v,l}=(P_{23},P_{31},P_{12}),$$
--
--   $$\chi_{c,r,\eta}(t,x)=\prod_{j=1}^{3}S\Big(\frac{r_j(t)+2\eta+y_j}{\eta}\Big)\,S\Big(\frac{r_j(t)+2\eta-y_j}{\eta}\Big).$$
--
--   For $A:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ the spatial curl is $\operatorname{curl}_xA=(\partial_2A_3-\partial_3A_2,\ \partial_3A_1-\partial_1A_3,\ \partial_1A_2-\partial_2A_1)$, where $\partial_j$ is the partial derivative in $x_j$.
--
--   The file establishes the following facts.
--
--   1. **Stage switches.** Each $\sigma_s$, $s=0,\dots,4$, is representable.
--   2. **Route centers.** For every rational $D$, every box $i$ and every coordinate $j$, the function $t\mapsto c_{ij}(t)$ is representable.
--   3. **Scale blends and route scales.** Every blend $\lambda_{ij}$ is representable, for arbitrary rational data. If $h_{ij}>0$ and $k_{ij}>0$ for all $i,j$, then every coordinate $t\mapsto d_i(t)_j$ of every route scale is representable.
--   4. **Separation from zero.** If $h_{ij}>0$ and $k_{ij}>0$ for all $i,j$, then for every $i$ and $j$ there is $\varepsilon>0$ with $|d_i(t)_j|\ge\varepsilon$ for all $t\in\mathbb{R}$.
--   5. **Time derivatives of curves.** If $c:\mathbb{R}\to\mathbb{R}^3$ is $C^\infty$, then at every $(t,x)$ the partial derivative of $(t,x)\mapsto c_j(t)$ in the time direction equals $c_j'(t)$. Consequently, if moreover every coordinate of $c$ is representable, then every coordinate $t\mapsto c_j'(t)$ of the velocity is representable.
--   6. **Logarithmic velocities of route scales.** If $h_{ij}>0$ and $k_{ij}>0$ for all $i,j$, then $t\mapsto d_i'(t)_j/d_i(t)_j$ is representable for all $i,j$.
--   7. **Moving affine potential.** If all coordinates of $c,v,l$ are representable, then every component of $A_{c,v,l}$ is representable.
--   8. **Moving box cutoff.** If all coordinates of $c$ and $r$ are representable and $\eta\in\mathbb{Q}$, then $\chi_{c,r,\eta}$ is representable.
--   9. **Family potential.** If $(c_i,v_i,l_i,r_i)_{i<n}$ are curves all of whose coordinates are representable and $\eta\in\mathbb{Q}$, then every component of $\sum_{i}\chi_{c_i,r_i,\eta}\,A_{c_i,v_i,l_i}$ is representable.
--   10. **Spatial curl.** If every component of $A$ is representable, then every component of $\operatorname{curl}_xA$ is representable.
--
--   The routed velocity field of the balanced box-routing construction is the spatial curl of a family potential of exactly this shape, built from the route centers $c_i$ (with $D$ a rational multiple of a bound on the box data), their velocities $c_i'$, the logarithmic velocities of the route scales $d_i$, and the radii $t\mapsto d_i(t)_j\,h_{ij}$. Chaining items 1–10 shows that every component of that field is the value of a valid expression. Valid expressions can be differentiated symbolically and evaluated in exact rational arithmetic with explicit error bounds, so this is the bridge to the effectivity requirement (computable rational approximation of all mixed partial derivatives) in the definition of an admissible field.
--
--   **Formalization Note** `Representable f` asserts that some `e : Expr` satisfies `Valid e` and `value e = f`, where `Expr` reuses the constructors of `Nat.Partrec.Code` as the syntax of expressions. All lemmas except `routeScales_separated_from_zero` and `time_partial_curve` carry the `fun_prop` attribute, so that representability goals are discharged automatically. Lean indexes coordinates by `Fin 3` (here $1,2,3$) and stages by `Fin 5`; functions of time are written `fun p : SpaceTime => c p.1 j`, and the separation bound of item 4 is stated for all space-time points. The ratios $k_{ij}/h_{ij}$ are computed in $\mathbb{Q}$ and then cast to $\mathbb{R}$. The cutoff and family-potential lemmas assume nothing about the sign of $\eta$ (Lean's convention $y/0=0$ makes them meaningful for every rational $\eta$). The time derivative in item 5 is the Fréchet derivative applied to the time direction $(1,0)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Routing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Routing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedBoxRouting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
import Definitions.Def_OAI_Analysis_BoxTransport_Expressions

namespace OAI

/-! Effective realization of every balanced finite box instruction. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

@[fun_prop] theorem representable_stageSwitch (j : Fin 5) :
    Representable (fun p : SpaceTime => stageSwitch j p.1) := by
  unfold stageSwitch
  fun_prop

@[fun_prop] theorem representable_routeCenters {n : ℕ} (a b : Fin n → RationalSpace) (D : ℚ)
    (i : Fin n) (j : Fin 3) :
    Representable (fun p : SpaceTime => routeCenters a b (D : ℝ) i p.1 j) := by
  fin_cases j <;> dsimp [routeCenters, routeCenterParameters] <;> fun_prop

@[fun_prop] theorem representable_linearBlend {n : ℕ} (h k : Fin n → RationalSpace)
    (i : Fin n) (j : Fin 3) : Representable (fun p : SpaceTime =>
      1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i j) := by
  unfold scaleRatio
  fun_prop

@[fun_prop] theorem representable_routeScales {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (j : Fin 3) :
    Representable (fun p : SpaceTime => routeScales h k i p.1 j) := by
  fin_cases j
  · exact representable_linearBlend h k i 0
  · exact representable_linearBlend h k i 1
  · change Representable (fun p : SpaceTime =>
      ((1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i 0) *
        (1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i 1))⁻¹)
    apply ((representable_linearBlend h k i 0).mul (representable_linearBlend h k i 1)).inv
    refine ⟨min 1 (scaleRatio h k i 0) * min 1 (scaleRatio h k i 1),
      mul_pos (lt_min zero_lt_one (scaleRatio_pos hh hk i 0))
        (lt_min zero_lt_one (scaleRatio_pos hh hk i 1)), fun p => ?_⟩
    have hp (j : Fin 3) := linearBlend_pos (scaleRatio_pos hh hk i j) (stageSwitch_mem 2 p.1)
    rw [abs_of_pos (mul_pos (hp 0) (hp 1))]
    exact mul_le_mul (linearBlend_between (stageSwitch_mem 2 p.1)).1
      (linearBlend_between (stageSwitch_mem 2 p.1)).1
      (le_of_lt (lt_min zero_lt_one (scaleRatio_pos hh hk i 1))) (hp 0).le

theorem routeScales_separated_from_zero {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (j : Fin 3) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : SpaceTime, ε ≤ |routeScales h k i p.1 j| := by
  have hs := scaleRatio_pos hh hk i
  fin_cases j <;> simp only [Fin.reduceFinMk]
  · refine ⟨min 1 (scaleRatio h k i 0), lt_min zero_lt_one (hs 0), fun p => ?_⟩
    rw [abs_of_pos (routeScales_pos hh hk i p.1 0)]
    exact (linearBlend_between (stageSwitch_mem 2 p.1)).1
  · refine ⟨min 1 (scaleRatio h k i 1), lt_min zero_lt_one (hs 1), fun p => ?_⟩
    rw [abs_of_pos (routeScales_pos hh hk i p.1 1)]
    exact (linearBlend_between (stageSwitch_mem 2 p.1)).1
  · refine ⟨(max 1 (scaleRatio h k i 0) * max 1 (scaleRatio h k i 1))⁻¹,
      inv_pos.mpr (mul_pos (lt_max_of_lt_left zero_lt_one) (lt_max_of_lt_left zero_lt_one)), fun p => ?_⟩
    rw [abs_of_pos (routeScales_pos hh hk i p.1 2)]
    change _ ≤ ((1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i 0) *
      (1 - stageSwitch 2 p.1 + stageSwitch 2 p.1 * scaleRatio h k i 1))⁻¹
    have hp (j : Fin 3) := linearBlend_pos (hs j) (stageSwitch_mem 2 p.1)
    apply inv_anti₀ (mul_pos (hp 0) (hp 1))
    exact mul_le_mul (linearBlend_between (stageSwitch_mem 2 p.1)).2
      (linearBlend_between (stageSwitch_mem 2 p.1)).2 (hp 1).le
      (le_of_lt (lt_max_of_lt_left zero_lt_one))

theorem time_partial_curve {c : ℝ → Space} (hc : ContDiff ℝ ∞ c) (p : SpaceTime) (j : Fin 3) :
    fderiv ℝ (fun p : SpaceTime => c p.1 j) p (coordinateDirection none) = deriv c p.1 j := by
  have hs : ContDiff ℝ ∞ (fun p : SpaceTime => c p.1) := hc.comp contDiff_fst
  rw [fderiv_apply (hs.differentiable (by simp) p)]
  have hd := ((hc.differentiable (by simp) p.1).hasFDerivAt.comp p hasFDerivAt_fst).fderiv
  change fderiv ℝ (fun p : SpaceTime => c p.1) p = _ at hd
  rw [hd]
  rfl

@[fun_prop] theorem representable_curve_deriv {c : ℝ → Space} (hc : ContDiff ℝ ∞ c)
    (hrep : ∀ j, Representable (fun p : SpaceTime => c p.1 j)) (j : Fin 3) :
    Representable (fun p : SpaceTime => deriv c p.1 j) := by
  have h := (hrep j).directional none
  simpa only [time_partial_curve hc] using h

@[fun_prop] theorem representable_diagonalLogVelocity {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (j : Fin 3) :
    Representable (fun p : SpaceTime => diagonalLogVelocity (routeScales h k i) p.1 j) := by
  exact (representable_curve_deriv (contDiff_routeScales hh hk i) (representable_routeScales hh hk i) j).div
    (representable_routeScales hh hk i j) (routeScales_separated_from_zero hh hk i j)

@[fun_prop] theorem representable_movingAffinePotential {c v l : ℝ → Space}
    (hc : ∀ j, Representable (fun p : SpaceTime => c p.1 j))
    (hv : ∀ j, Representable (fun p : SpaceTime => v p.1 j))
    (hl : ∀ j, Representable (fun p : SpaceTime => l p.1 j)) (j : Fin 3) :
    Representable (fun p => movingAffinePotential c v l p j) := by
  have hr (j : Fin 3) := (Representable.space j).sub (hc j)
  have hcomp (i j : Fin 3) : Representable
      (fun p : SpaceTime => potentialComponent (c p.1) (v p.1) (l p.1) i j p) := by
    exact ((Representable.one.div_nat 2).mul (((hv i).mul (hr j)).sub ((hv j).mul (hr i)))).add
      (((Representable.one.div_nat 3).mul ((hl i).sub (hl j))).mul ((hr i).mul (hr j)))
  fin_cases j
  · exact hcomp 1 2
  · exact hcomp 2 0
  · exact hcomp 0 1

@[fun_prop] theorem representable_movingBoxCutoff {c r : ℝ → Space}
    (hc : ∀ j, Representable (fun p : SpaceTime => c p.1 j))
    (hr : ∀ j, Representable (fun p : SpaceTime => r p.1 j)) (η : ℚ) :
    Representable (movingBoxCutoff c r η) := by
  unfold movingBoxCutoff
  apply Representable.prod
  intro j _
  have hrj := (hr j).add ((Representable.ofNat 2).mul (Representable.rational η))
  have hxj := (Representable.space j).sub (hc j)
  exact ((hrj.add hxj).div_rat η).transition.mul ((hrj.sub hxj).div_rat η).transition

@[fun_prop] theorem representable_familyPotential {n : ℕ} {c v l r : Fin n → ℝ → Space}
    (hc : ∀ i j, Representable (fun p : SpaceTime => c i p.1 j))
    (hv : ∀ i j, Representable (fun p : SpaceTime => v i p.1 j))
    (hl : ∀ i j, Representable (fun p : SpaceTime => l i p.1 j))
    (hr : ∀ i j, Representable (fun p : SpaceTime => r i p.1 j)) (η : ℚ) (j : Fin 3) :
    Representable (fun p => familyPotential c v l r η p j) := by
  simp only [familyPotential, Finset.sum_apply]
  apply Representable.sum
  intro i _
  change Representable (fun p => movingBoxCutoff (c i) (r i) η p * movingAffinePotential (c i) (v i) (l i) p j)
  exact (representable_movingBoxCutoff (hc i) (hr i) η).mul
    (representable_movingAffinePotential (hc i) (hv i) (hl i) j)

@[fun_prop] theorem representable_spatialCurl {A : Field}
    (hrep : ∀ j, Representable (fun p => A p j)) (j : Fin 3) :
    Representable (fun p => spatialCurl A p j) := by
  have hA : ContDiff ℝ ∞ A := contDiff_pi.mpr (fun j => (hrep j).smooth)
  have hd (d : Axis) (k : Fin 3) : Representable (fun p => fderiv ℝ A p (coordinateDirection d) k) := by
    have hh := (hrep k).directional d
    simpa only [fderiv_apply (hA.differentiable (by simp) _), ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using hh
  fin_cases j <;> simp only [spatialCurl, curlLinear_apply]
  · exact (hd (some 1) 2).sub (hd (some 2) 1)
  · exact (hd (some 2) 0).sub (hd (some 0) 2)
  · exact (hd (some 0) 1).sub (hd (some 1) 0)

end BoxTransport.Routing.Computation

namespace BoxTransport.Routing

end BoxTransport.Routing

end

end OAI


