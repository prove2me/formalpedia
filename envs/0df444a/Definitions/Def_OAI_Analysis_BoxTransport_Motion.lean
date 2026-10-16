-- Prove2me | Definitions.Def_OAI_Analysis_BoxTransport_Motion
-- name    : OAI_Analysis_BoxTransport_Motion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T13:07:19.919754+00:00
-- url     : https://prove2.me/theorems/bcac353d-35b3-42ed-855d-e1f26fbb8e23
-- title:
--   Five-stage smooth routing of box centers with volume-preserving diagonal rescaling
-- statement:
--   This file defines the explicit five-stage motion that routes $n$ source boxes to $n$ target boxes, and the velocity field associated with it. Fix $n\in\mathbb{N}$ and, for each index $i\in\{0,\dots,n-1\}$, rational vectors $a_i,b_i,h_i,k_i\in\mathbb{Q}^3$ (source center, target center, source half-widths, target half-widths), with coordinates $a_{i,j}$ etc. indexed by $j\in\{0,1,2\}$. Let $S$ be the standard smooth transition function, $S(y)=\psi(y)/(\psi(y)+\psi(1-y))$ with $\psi(y)=e^{-1/y}$ for $y>0$ and $\psi(y)=0$ for $y\le0$; it is $C^\infty$, takes values in $[0,1]$, vanishes on $(-\infty,0]$ and equals $1$ on $[1,\infty)$.
--
--   1. **Ranks and spread centers.** For $f:\{0,\dots,n-1\}\to\mathbb{Q}$ the rank of $i$ is
--   $$\operatorname{rk}_f(i)=\#\bigl\{q:\ f(q)<f(i)\ \text{or}\ \bigl(f(q)=f(i)\ \text{and}\ q<i\bigr)\bigr\},$$
--   the position of $i$ when the indices are sorted lexicographically by the key $(f(q),q)$. Write $\rho^a_i$ and $\rho^b_i$ for the ranks of $i$ with respect to the first coordinates $q\mapsto a_{q,0}$ and $q\mapsto b_{q,0}$. For $D,\theta\in\mathbb{R}$ the spread center of box $i$ is $(a_{i,0}+\theta D\rho^a_i,\ a_{i,1},\ a_{i,2})$; it equals $a_i$ when $\theta=0$.
--
--   2. **Stage switches.** For $j\in\{0,1,2,3,4\}$ let $\sigma_j(t)=S\bigl(10t-\tfrac52-j\bigr)$. Each $\sigma_j$ is $C^\infty$ with values in $[0,1]$; it vanishes for $t\le\frac14+\frac{j}{10}$ and equals $1$ for $t\ge\frac{7}{20}+\frac{j}{10}$.
--
--   3. **Routed centers.** For $D\in\mathbb{R}$ and switch values $u=(u_0,\dots,u_4)\in\mathbb{R}^5$ put
--   $$C_i(u)=\begin{pmatrix}a_{i,0}+u_0D\rho^a_i+u_2\bigl(b_{i,0}+D\rho^b_i-a_{i,0}-D\rho^a_i\bigr)-u_4D\rho^b_i\\ a_{i,1}+u_2\,(b_{i,1}-a_{i,1})\\ a_{i,2}+u_1\,(D\,i-a_{i,2})+u_3\,(b_{i,2}-D\,i)\end{pmatrix},$$
--   and define the center path $c_i(t)=C_i\bigl(\sigma_0(t),\dots,\sigma_4(t)\bigr)$.
--
--   4. **Balanced scales.** Let $s_{i,j}=k_{i,j}/h_{i,j}$, computed in $\mathbb{Q}$. For $s\in\mathbb{R}^3$ and $u\in\mathbb{R}$ set
--   $$\beta(s,u)=\Bigl(1-u+us_0,\ 1-u+us_1,\ \bigl((1-u+us_0)(1-u+us_1)\bigr)^{-1}\Bigr),$$
--   and define the scale path $d_i(t)=\beta\bigl(s_i,\sigma_2(t)\bigr)$. The file shows: $\beta(s,0)=(1,1,1)$; for $u\in[0,1]$ the blend $1-u+us$ lies between $\min(1,s)$ and $\max(1,s)$, hence is positive when $s>0$; consequently all coordinates of $\beta(s,u)$ are positive when $s_0,s_1,s_2>0$ and $u\in[0,1]$. If all $h_{i,j}>0$ and all $k_{i,j}>0$, then every ratio $s_{i,j}$ is positive, each $t\mapsto d_i(t)$ is $C^\infty$, and every $d_{i,j}(t)$ is positive.
--
--   5. **Data bound.** $B(h,k)=1+\sum_{i=0}^{n-1}\sum_{j=0}^{2}\bigl(|h_{i,j}|+|k_{i,j}|+|k_{i,j}/h_{i,j}|+1\bigr)\in\mathbb{Q}$.
--
--   6. **Motion field and routed field.** Given paths $c_i,d_i:\mathbb{R}\to\mathbb{R}^3$, vectors $\bar h_i\in\mathbb{R}^3$ and $\eta\in\mathbb{R}$, the motion field is
--   $$U=\nabla_x\times\sum_{i=0}^{n-1}\chi_i\,A_i .$$
--   Here, for $p=(t,x)$ and $y=x-c_i(t)$, the potential is $A_i(p)=(\phi_{12},\phi_{20},\phi_{01})$ with $\phi_{jm}=\frac12(v_jy_m-v_my_j)+\frac13(l_j-l_m)\,y_jy_m$, where $v=c_i'(t)$ and $l_j=d_{i,j}'(t)/d_{i,j}(t)$; the cutoff is $\chi_i(p)=\prod_{j=0}^{2}S\bigl((r_j+2\eta+y_j)/\eta\bigr)\,S\bigl((r_j+2\eta-y_j)/\eta\bigr)$ with $r_j=d_{i,j}(t)\,\bar h_{i,j}$; and $\nabla_x\times$ is the curl in the spatial variables, $\nabla_x\times F=(\partial_{x_1}F_2-\partial_{x_2}F_1,\ \partial_{x_2}F_0-\partial_{x_0}F_2,\ \partial_{x_0}F_1-\partial_{x_1}F_0)$. The routed field, for a rational $\eta$, is the motion field built from the center paths $c_i$ of item 3 with $D=30\,B(h,k)$, the scale paths $d_i$ of item 4, and $\bar h_i=h_i$.
--
--   For $t\le\frac14$ all switches vanish, so $c_i(t)=a_i$ and $d_i(t)=(1,1,1)$; for $t\ge\frac34$ all switches equal $1$, so $c_i(t)=b_i$ and $d_i(t)=\bigl(s_{i,0},s_{i,1},(s_{i,0}s_{i,1})^{-1}\bigr)$, which equals $(k_{i,j}/h_{i,j})_j$ exactly when the volume balance $s_{i,0}s_{i,1}s_{i,2}=1$ holds. In between, stage $j$ occupies the window $[\frac14+\frac{j}{10},\frac{7}{20}+\frac{j}{10}]$, during which only $\sigma_j$ varies: stage 0 spreads the boxes along $x_0$ in rank order, stage 1 moves box $i$ to the level $x_2=D\,i$, stage 2 moves the first two center coordinates to $b_{i,0}+D\rho^b_i$ and $b_{i,1}$ while rescaling, stage 3 moves $x_2$ to $b_{i,2}$, and stage 4 retracts $x_0$ to $b_{i,0}$. For positive ratios the product $d_{i,0}d_{i,1}d_{i,2}$ equals $1$ at all times, and the large spacing $D$ is meant to keep the moving boxes apart. The motion field is designed so that its flow carries the $i$-th source box along $x\mapsto c_i(t)+d_i(t)\odot(x-a_i)$ (coordinatewise product), so that under volume balance the time-one map on that box is the prescribed affine map $x_j\mapsto b_{i,j}+(k_{i,j}/h_{i,j})(x_j-a_{i,j})$.
--
--   **Formalization Note** The rank is `coordinateRank`, defined via the key `centerKey f i = toLex (f i, i)` in `ℚ ×ₗ ℕ`; the spread center is `spreadCenter` (with the simp lemma `spreadCenter_zero`); the switches are `stageSwitch` (`contDiff_stageSwitch`, `stageSwitch_mem`); $C_i$ and $c_i$ are `routeCenterParameters` and `routeCenters`. `scaleRatio` computes $k/h$ in $\mathbb{Q}$ before casting to $\mathbb{R}$, so it is $0$ when $h_{i,j}=0$. The scale facts are `balancedScale_zero`, `linearBlend_between`, `linearBlend_pos`, `balancedScale_pos`, `scaleRatio_pos`, `contDiff_routeScales` and `routeScales_pos`; $B$ is `boxDataBound`. `stationaryMotionField c d h η` is `spatialCurl` of `familyPotential` with velocities `deriv (c i)`, rates `diagonalLogVelocity (d i)` and half-widths `d i t j * h i j`; here `deriv` is $0$ at points of non-differentiability and $y/0=0$. `routedField a b h k η` is the routed field.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Motion.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Motion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedBoxRouting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Separated five-stage motions and explicit affine time-one delivery. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
def centerKey {n : ℕ} (f : Fin n → ℚ) (i : Fin n) : ℚ ×ₗ ℕ := toLex (f i, i.val)

def coordinateRank {n : ℕ} (f : Fin n → ℚ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => centerKey f j < centerKey f i).card

def spreadCenter {n : ℕ} (a : Fin n → RationalSpace) (D θ : ℝ) (i : Fin n) : Space :=
  fun j => if j = 0 then (a i 0 : ℝ) + θ * D * coordinateRank (fun q => a q 0) i
    else (a i j : ℝ)

@[simp] theorem spreadCenter_zero {n : ℕ} (a : Fin n → RationalSpace) (D : ℝ) (i : Fin n) :
    spreadCenter a D 0 i = realPoint (a i) := by
  ext j
  by_cases hj : j = 0 <;> simp [spreadCenter, hj, realPoint]

noncomputable def stageSwitch (j : Fin 5) (t : ℝ) : ℝ :=
  Real.smoothTransition (10 * t - 5 / 2 - (j : ℝ))

theorem contDiff_stageSwitch (j : Fin 5) : ContDiff ℝ ∞ (stageSwitch j) := by
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem stageSwitch_mem (j : Fin 5) (t : ℝ) : stageSwitch j t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

def routeCenterParameters {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    (u : Fin 5 → ℝ) (i : Fin n) : Space :=
  ![(a i 0 : ℝ) + u 0 * D * coordinateRank (fun q => a q 0) i +
      u 2 * ((b i 0 : ℝ) + D * coordinateRank (fun q => b q 0) i -
        (a i 0 : ℝ) - D * coordinateRank (fun q => a q 0) i) -
      u 4 * D * coordinateRank (fun q => b q 0) i,
    (a i 1 : ℝ) + u 2 * ((b i 1 : ℝ) - (a i 1 : ℝ)),
    (a i 2 : ℝ) + u 1 * (D * (i : ℝ) - (a i 2 : ℝ)) +
      u 3 * ((b i 2 : ℝ) - D * (i : ℝ))]

noncomputable def routeCenters {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    (i : Fin n) (t : ℝ) : Space := routeCenterParameters a b D (fun j => stageSwitch j t) i

def scaleRatio {n : ℕ} (h k : Fin n → RationalSpace) (i : Fin n) (j : Fin 3) : ℝ :=
  ((k i j / h i j : ℚ) : ℝ)

noncomputable def balancedScale (s : Space) (u : ℝ) : Space :=
  ![1 - u + u * s 0, 1 - u + u * s 1,
    ((1 - u + u * s 0) * (1 - u + u * s 1))⁻¹]

@[simp] theorem balancedScale_zero (s : Space) : balancedScale s 0 = 1 := by
  ext j; fin_cases j <;> simp [balancedScale]

theorem linearBlend_between {s u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    min 1 s ≤ 1 - u + u * s ∧ 1 - u + u * s ≤ max 1 s := by
  by_cases h : 1 ≤ s
  · rw [min_eq_left h, max_eq_right h]
    constructor
    · nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr h)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr h)]
  · have h' := le_of_not_ge h
    rw [min_eq_right h', max_eq_left h']
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr h')]
    · nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr h')]

theorem linearBlend_pos {s u : ℝ} (hs : 0 < s) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - u + u * s :=
  lt_of_lt_of_le (lt_min zero_lt_one hs) (linearBlend_between hu).1

theorem balancedScale_pos (s : Space) (hs : ∀ j, 0 < s j)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (j : Fin 3) :
    0 < balancedScale s u j := by
  fin_cases j
  · exact linearBlend_pos (hs 0) hu
  · exact linearBlend_pos (hs 1) hu
  · exact inv_pos.mpr (mul_pos (linearBlend_pos (hs 0) hu) (linearBlend_pos (hs 1) hu))

noncomputable def routeScales {n : ℕ} (h k : Fin n → RationalSpace) (i : Fin n) (t : ℝ) : Space :=
  balancedScale (scaleRatio h k i) (stageSwitch 2 t)

theorem scaleRatio_pos {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (j : Fin 3) :
    0 < scaleRatio h k i j := by
  unfold scaleRatio
  exact_mod_cast div_pos (hk i j) (hh i j)

theorem contDiff_routeScales {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) :
    ContDiff ℝ ∞ (routeScales h k i) := by
  have hp (j : Fin 3) (t : ℝ) := linearBlend_pos (scaleRatio_pos hh hk i j) (stageSwitch_mem 2 t)
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (fun t => 1 - stageSwitch 2 t + stageSwitch 2 t * scaleRatio h k i 0)
    exact (contDiff_const.sub (contDiff_stageSwitch 2)).add ((contDiff_stageSwitch 2).mul contDiff_const)
  · change ContDiff ℝ ∞ (fun t => 1 - stageSwitch 2 t + stageSwitch 2 t * scaleRatio h k i 1)
    exact (contDiff_const.sub (contDiff_stageSwitch 2)).add ((contDiff_stageSwitch 2).mul contDiff_const)
  · change ContDiff ℝ ∞ (fun t => ((1 - stageSwitch 2 t + stageSwitch 2 t * scaleRatio h k i 0) *
        (1 - stageSwitch 2 t + stageSwitch 2 t * scaleRatio h k i 1))⁻¹)
    apply ContDiff.inv
    · exact ((contDiff_const.sub (contDiff_stageSwitch 2)).add ((contDiff_stageSwitch 2).mul contDiff_const)).mul
        ((contDiff_const.sub (contDiff_stageSwitch 2)).add ((contDiff_stageSwitch 2).mul contDiff_const))
    · intro t; exact ne_of_gt (mul_pos (hp 0 t) (hp 1 t))

theorem routeScales_pos {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (t : ℝ) (j : Fin 3) :
    0 < routeScales h k i t j :=
  balancedScale_pos _ (scaleRatio_pos hh hk i) (stageSwitch_mem 2 t) j

def boxDataBound {n : ℕ} (h k : Fin n → RationalSpace) : ℚ :=
  1 + ∑ i : Fin n, ∑ j : Fin 3, (|h i j| + |k i j| + |k i j / h i j| + 1)

noncomputable def stationaryMotionField {n : ℕ} (c d : Fin n → ℝ → Space)
    (h : Fin n → Space) (η : ℝ) : Field :=
  spatialCurl (familyPotential c (fun i => deriv (c i))
    (fun i => diagonalLogVelocity (d i))
    (fun i t j => d i t j * h i j) η)

noncomputable def routedField {n : ℕ} (a b h k : Fin n → RationalSpace) (η : ℚ) : Field :=
  stationaryMotionField (routeCenters a b (30 * (boxDataBound h k : ℝ)))
    (routeScales h k) (fun i => realPoint (h i)) η

end BoxTransport.Routing

end

end OAI


