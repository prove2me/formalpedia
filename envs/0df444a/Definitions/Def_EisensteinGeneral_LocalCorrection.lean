-- Prove2me | Definitions.Def_EisensteinGeneral_LocalCorrection
-- name    : EisensteinGeneral_LocalCorrection
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/311504e4-28eb-5c16-b4b6-601545f177f4
-- title:
--   Local correction factors for Eisenstein Whittaker coefficients
-- statement:
--   Four explicit complex-analytic functions of a spectral variable $s \in \mathbb{C}$ are defined, all built from powers of a natural number $N$ raised to complex exponents. For $\chi\varpi \in \mathbb{C}$, $N, M \in \mathbb{N}$, `geomSum` is the truncated geometric sum $\sum_{k=0}^{M} (\chi\varpi \cdot N^{-2s})^k$, a sum of $M+1$ terms. For $N, K \in \mathbb{N}$, a constant $c_0 \in \mathbb{C}$ and a sequence $\mathrm{sh} : \mathbb{N} \to \mathbb{C}$, `ramSum` is $c_0 + \sum_{k=1}^{K} (N^{-(2s+1)})^k \, \mathrm{sh}(k)$, the index $k$ running over the integer interval $[1, K]$. Here $N^z$ is the complex power of the natural-number cast.
--
--   The two correction factors are defined by a case split on an integer parameter $e$. For $e \in \mathbb{Z}$, `corrOff` is $\mathrm{geomSum}(\chi\varpi, N, (-e)^{+}, s)$ when $e \le 0$, where $(-e)^{+}$ denotes the truncation of $-e$ to $\mathbb{N}$, and $0$ when $e > 0$. For $n \in \mathbb{Z}$, $c, m \in \mathbb{N}$, $e \in \mathbb{Z}$, a real number $\mu_{\mathcal{O}}$, and data $c_0, \mathrm{sh}$ as above, `corrOn` is $\mu_{\mathcal{O}}^{-1} \cdot \mathrm{ramSum}(N, \max(m-1,\, n+c-e)^{+}, c_0, \mathrm{sh}, s)$ when $e \le n + \max(m,c)$ (the maximum of $m$ and $c$ taken in $\mathbb{N}$ and then cast to $\mathbb{Z}$), and $0$ otherwise; the truncation to $\mathbb{N}$ is again applied to the integer $\max(m-1, n+c-e)$, and $\mu_{\mathcal{O}}$ enters through the cast of its inverse to $\mathbb{C}$.
--
--   Accompanying declarations record the defining equations of the four functions, and the fact that each is entire in $s$ whenever $0 < N$: `geomSum_differentiable`, `ramSum_differentiable`, `corrOff_differentiable` and `corrOn_differentiable`, resting on differentiability of $s \mapsto N^{-2s}$ and $s \mapsto N^{-(2s+1)}$ for $N \neq 0$.
--
--   **Relation to Mathlib.** Mathlib has no notion of these local correction factors; they are the project's own definitions, with differentiability obtained from Mathlib's `Differentiable.const_cpow` for complex powers of a fixed nonzero base.
--
--   **Where it is used.** These are the shapes taken by the local factors in the Euler-product factorisation of torus Whittaker coefficients of a flat $GL_2$ Eisenstein piece: `corrOff`, an unramified geometric correction indexed by the valuation $e$ of the Whittaker argument, at places outside an exceptional finite set, and `corrOn`, a ramified correction assembled from a constant term $c_0$ and shell integrals $\mathrm{sh}$ weighted by $N^{-(2s+1)}$, at the remaining places. Exporting them as definitions lets the factorisation statement and the later bounds on discs and half-planes for these factors be phrased in the same terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_EisensteinGeneral_LocalCorrection.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace EisensteinGeneral.LocalCorrection

def geomSum (χϖ : ℂ) (N : ℕ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (M + 1), (χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))) ^ k

def ramSum (N : ℕ) (K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) : ℂ :=
  c₀ + ∑ k ∈ Finset.Icc 1 K, (((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k

def corrOff (χϖ : ℂ) (N : ℕ) (e : ℤ) (s : ℂ) : ℂ :=
  if e ≤ 0 then geomSum χϖ N (-e).toNat s else 0

def corrOn (N : ℕ) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) : ℂ :=
  if e ≤ n + (max m c : ℕ) then
    (μ𝒪 : ℂ)⁻¹ * ramSum N (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat c₀ sh s
  else 0

theorem geomSum_def (χϖ : ℂ) (N M : ℕ) (s : ℂ) :
    geomSum χϖ N M s = ∑ k ∈ Finset.range (M + 1), (χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))) ^ k := rfl

theorem ramSum_def (N K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) :
    ramSum N K c₀ sh s = c₀ + ∑ k ∈ Finset.Icc 1 K, (((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k := rfl

theorem corrOff_def (χϖ : ℂ) (N : ℕ) (e : ℤ) (s : ℂ) :
    corrOff χϖ N e s = if e ≤ 0 then geomSum χϖ N (-e).toNat s else 0 := rfl

theorem corrOn_def (N : ℕ) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) :
    corrOn N n c m e μ𝒪 c₀ sh s =
      if e ≤ n + (max m c : ℕ) then (μ𝒪 : ℂ)⁻¹ * ramSum N (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat c₀ sh s
      else 0 := rfl

theorem differentiable_cpow_neg_two_mul {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (-(2 * s))) :=
  Differentiable.const_cpow (differentiable_id.const_mul (2 : ℂ)).neg
    (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))

theorem differentiable_cpow_neg_two_mul_add_one {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (-(2 * s + 1))) :=
  Differentiable.const_cpow ((differentiable_id.const_mul (2 : ℂ)).add (differentiable_const 1)).neg
    (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))

theorem geomSum_differentiable (χϖ : ℂ) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    Differentiable ℂ (geomSum χϖ N M) := by
  unfold geomSum
  exact Differentiable.fun_sum fun k _ => ((differentiable_cpow_neg_two_mul hN).const_mul χϖ).pow k

theorem ramSum_differentiable {N : ℕ} (hN : 0 < N) (K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) :
    Differentiable ℂ (ramSum N K c₀ sh) := by
  unfold ramSum
  exact (differentiable_const c₀).add
    (Differentiable.fun_sum fun k _ => ((differentiable_cpow_neg_two_mul_add_one hN).pow k).mul_const (sh k))

theorem corrOff_differentiable (χϖ : ℂ) {N : ℕ} (hN : 0 < N) (e : ℤ) :
    Differentiable ℂ (corrOff χϖ N e) := by
  unfold corrOff
  by_cases he : e ≤ 0
  · simp only [he, ↓reduceIte]
    exact geomSum_differentiable χϖ hN _
  · simp only [he, ↓reduceIte]
    exact differentiable_const 0

theorem corrOn_differentiable {N : ℕ} (hN : 0 < N) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ)
    (sh : ℕ → ℂ) : Differentiable ℂ (corrOn N n c m e μ𝒪 c₀ sh) := by
  unfold corrOn
  by_cases he : e ≤ n + (max m c : ℕ)
  · simp only [he, ↓reduceIte]
    exact (ramSum_differentiable hN _ c₀ sh).const_mul _
  · simp only [he, ↓reduceIte]
    exact differentiable_const 0

end EisensteinGeneral.LocalCorrection

end


