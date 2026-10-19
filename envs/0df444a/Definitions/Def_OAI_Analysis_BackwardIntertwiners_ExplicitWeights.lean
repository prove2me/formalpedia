-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
-- name    : OAI_Analysis_BackwardIntertwiners_ExplicitWeights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:57:14.750347+00:00
-- url     : https://prove2.me/theorems/6e2c6fdd-a47f-4db8-924e-98ef06a740f5
-- title:
--   Explicit bilateral weights with quadratic exponents and residue corrections
-- statement:
--   This file builds explicit two-sided weight sequences on $\mathbb{Z}$ whose logarithms are quadratic up to a lower-order correction driven by auxiliary digit sequences $t,u:\mathbb{N}\to\mathbb{N}$ (in the application $t(m)$ is the residue of a 2-adic integer modulo $2^m$). For $k\ge1$ let $\lfloor\log_8 k\rfloor$ be the largest $q\in\mathbb{N}$ with $8^q\le k$, and set $\lfloor\log_8 0\rfloor=0$.
--
--   1. **Blocks and scales.** $m(k)=\lfloor\log_8 k\rfloor+1$ and $N(k)=2^{m(k)}$. Thus $m(k)=q+1$ and $N(k)=2^{q+1}$ when $8^q\le k<8^{q+1}$, while $m(0)=1$ and $N(0)=2$.
--   2. **Residue correction and half-exponent.**
--   $$\delta_t(k)=\begin{cases}0,&k=0,\\100\,\bigl(N(k)-2+t(m(k))\bigr),&k\ge1,\end{cases}\qquad E_t(k)=10(k+1)+\delta_t(k).$$
--   3. **Residue bounds.** $t$ satisfies the residue bounds if $t(m)<2^m$ for every $m\in\mathbb{N}$.
--   4. **Partial sums.** $\Sigma_t(n)=\sum_{k=0}^{n-1}E_t(k)$, so $\Sigma_t(0)=0$ and $\Sigma_t(n+1)=\Sigma_t(n)+E_t(n)$.
--   5. **Bilateral exponent, ratio and weight.** For $j\in\mathbb{Z}$,
--   $$\varepsilon_{t,u}(j)=\begin{cases}E_t(j),&j\ge0,\\E_u(-j-1),&j<0,\end{cases}\qquad\beta_{t,u}(j)=e^{-\varepsilon_{t,u}(j)},\qquad w_{t,u}(j)=\begin{cases}e^{-\Sigma_t(j)},&j\ge0,\\e^{\Sigma_u(-j)},&j<0.\end{cases}$$
--
--   The file records the elementary estimates: $N(k)\ge2$; $\delta_t(k)\ge0$, hence $E_t(k)\ge10(k+1)$, and $E_t(0)=10$; $N(k)^2\le4k$ for $k\ge1$; under the residue bounds $\delta_t(k)\le200\,N(k)$ and $\delta_t(k)\le400\sqrt{k}$; moreover $\varepsilon_{t,u}(j)\ge10$, $w_{t,u}(j)>0$ for all $j$, and $w_{t,u}(-n)=e^{\Sigma_u(n)}$ for all $n\in\mathbb{N}$.
--
--   The weight is normalized by $w_{t,u}(0)=1$ and its consecutive ratios are $w_{t,u}(j+1)/w_{t,u}(j)=\beta_{t,u}(j)$, so $w_{t,u}$ is the weight sequence of the weighted shift $e_j\mapsto\beta_{t,u}(j)\,e_{j+1}$ on $\ell^2(\mathbb{Z})$. When $t$ and $u$ both satisfy the residue bounds, $5n(n+1)\le\Sigma_t(n)\le5n(n+1)+400\,n\sqrt n$ and likewise for $\Sigma_u$, so $\log w_{t,u}(n)/n^2\to-5$ and $\log w_{t,u}(-n)/n^2\to5$, and $w_{t,u}$ is a quadratic weight in the sense needed for the support separation property. The digits enter only through the correction $\delta_t$, of order at most $\sqrt{k}$; this is how the construction couples the fiber weights to the odometer on the 2-adic integers.
--
--   **Formalization Note** The names are `weightBlock`, `residueScale`, `residueCorrection`, `halfExponent`, `ResidueBounds`, `halfSum`, `bilateralExponent`, `bilateralBeta` and `bilateralWeight`. The block uses `Nat.log 8 k`, which is $0$ at $k=0$; the correction is computed in the real numbers, so no truncated subtraction occurs. The bilateral functions are defined by cases on `Int.ofNat n` ($j=n$) and `Int.negSucc n` ($j=-(n+1)$). The listed estimates are the lemmas `residueScale_ge_two`, `residueCorrection_nonneg`, `residueCorrection_le`, `halfExponent_lower`, `halfExponent_zero`, `residueScale_sq_le`, `residueCorrection_sqrt_bound`, `halfSum_zero`, `halfSum_succ`, `bilateralWeight_nat`, `bilateralWeight_neg_nat`, `bilateralExponent_nonneg` and `bilateralWeight_pos`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ExplicitWeights.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ExplicitWeights.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

def weightBlock (k : ℕ) : ℕ := Nat.log 8 k + 1
def residueScale (k : ℕ) : ℕ := 2 ^ weightBlock k

def residueCorrection (t : ℕ → ℕ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else 100 * ((residueScale k : ℝ) - 2 + t (weightBlock k))
def halfExponent (t : ℕ → ℕ) (k : ℕ) : ℝ :=
  10 * ((k : ℝ) + 1) + residueCorrection t k

def ResidueBounds (t : ℕ → ℕ) : Prop := ∀ m, t m < 2 ^ m

lemma residueScale_ge_two (k : ℕ) : 2 ≤ residueScale k := by
  dsimp [residueScale, weightBlock]
  simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ Nat.log 8 k + 1))

lemma residueCorrection_nonneg (t : ℕ → ℕ) (k : ℕ) : 0 ≤ residueCorrection t k := by
  dsimp [residueCorrection]
  split_ifs
  · rfl
  · have hh : (2:ℝ) ≤ residueScale k := by exact_mod_cast residueScale_ge_two k
    positivity

lemma residueCorrection_le {t : ℕ → ℕ} (ht : ResidueBounds t) (k : ℕ) :
    residueCorrection t k ≤ 200 * residueScale k := by
  have hN : (0:ℝ) ≤ residueScale k := Nat.cast_nonneg _
  dsimp [residueCorrection]
  split_ifs
  · positivity
  · have hr : (t (weightBlock k):ℝ) < residueScale k := by exact_mod_cast ht (weightBlock k)
    linarith

lemma halfExponent_lower (t : ℕ → ℕ) (k : ℕ) :
    10*((k:ℝ)+1) ≤ halfExponent t k := by
  have hh := residueCorrection_nonneg t k
  dsimp [halfExponent]
  linarith

@[simp] lemma halfExponent_zero (t : ℕ → ℕ) : halfExponent t 0 = 10 := by
  norm_num [halfExponent, residueCorrection]

lemma residueScale_sq_le {k : ℕ} (hk : k ≠ 0) : (residueScale k)^2 ≤ 4*k := by
  let q := Nat.log 8 k
  have hq : 8 ^ q ≤ k := Nat.pow_log_le_self 8 hk
  have h4 : 4 ^ q ≤ 8 ^ q := Nat.pow_le_pow_left (by norm_num) q
  have he : (residueScale k)^2 = 4 * 4 ^ q := by
    change (2 ^ (q+1))^2 = 4 * 4^q
    rw [pow_succ (2:ℕ) q, mul_pow, ← pow_mul, mul_comm q 2, pow_mul]
    norm_num
    ring
  rw [he]
  omega

lemma residueCorrection_sqrt_bound {t : ℕ → ℕ} (ht : ResidueBounds t) (k : ℕ) :
    residueCorrection t k ≤ 400 * Real.sqrt k := by
  by_cases hk : k = 0
  · simp [hk, residueCorrection]
  have hs : (residueScale k : ℝ)^2 ≤ 4*(k:ℝ) := by exact_mod_cast residueScale_sq_le hk
  have hroot := Real.sq_sqrt (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hroot0 := Real.sqrt_nonneg (k:ℝ)
  have hN0 : (0:ℝ) ≤ residueScale k := Nat.cast_nonneg _
  have hNr : (residueScale k : ℝ) ≤ 2*Real.sqrt k := by nlinarith
  exact (residueCorrection_le ht k).trans (by linarith)

def halfSum (t : ℕ → ℕ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, halfExponent t k

@[simp] lemma halfSum_zero (t : ℕ → ℕ) : halfSum t 0 = 0 := by simp [halfSum]
@[simp] lemma halfSum_succ (t : ℕ → ℕ) (n : ℕ) :
    halfSum t (n+1) = halfSum t n + halfExponent t n := by simp [halfSum, Finset.sum_range_succ]

def bilateralExponent (t u : ℕ → ℕ) : ℤ → ℝ
  | .ofNat n => halfExponent t n
  | .negSucc n => halfExponent u n

def bilateralBeta (t u : ℕ → ℕ) (j : ℤ) : ℝ := Real.exp (-bilateralExponent t u j)

def bilateralWeight (t u : ℕ → ℕ) : ℤ → ℝ
  | .ofNat n => Real.exp (-halfSum t n)
  | .negSucc n => Real.exp (halfSum u (n+1))

@[simp] lemma bilateralWeight_nat (t u : ℕ → ℕ) (n : ℕ) :
    bilateralWeight t u n = Real.exp (-halfSum t n) := rfl
@[simp] lemma bilateralWeight_neg_nat (t u : ℕ → ℕ) (n : ℕ) :
    bilateralWeight t u (-(n:ℤ)) = Real.exp (halfSum u n) := by
  cases n with
  | zero => simp [bilateralWeight]
  | succ n => rfl

lemma bilateralExponent_nonneg (t u : ℕ → ℕ) (j : ℤ) : 10 ≤ bilateralExponent t u j := by
  cases j with
  | ofNat n =>
    have hh := halfExponent_lower t n
    change 10 ≤ halfExponent t n
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  | negSucc n =>
    have hh := halfExponent_lower u n
    change 10 ≤ halfExponent u n
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    linarith

lemma bilateralWeight_pos (t u : ℕ → ℕ) (j : ℤ) : 0 < bilateralWeight t u j := by
  cases j <;> exact Real.exp_pos _

end
end BackwardIntertwiners

end OAI


