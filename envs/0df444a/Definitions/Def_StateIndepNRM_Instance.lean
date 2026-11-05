-- Prove2me | Definitions.Def_StateIndepNRM_Instance
-- name    : StateIndepNRM_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:16.353326+00:00
-- url     : https://prove2.me/theorems/9b42ebe3-6ecc-4e1d-8e5e-587f9287530d
-- title:
--   Network pricing instance with piecewise-stationary demand, and its $k$-scaling
-- statement:
--   An **instance** of the continuous-price network pricing problem $\mathbb P_C$ has $M$ resources and $N$ products, a consumption matrix $A=[a_{m,n}]$ with $a_{m,n}\ge0$ and a positive entry in every row and column, capacities $b_m\in\mathbb N$, and a horizon $T>0$.
--
--   Demand is piecewise stationary: breakpoints $0=s_0<s_1<\dots<s_J=T$ cut $[0,T]$ into $J$ pieces, and on piece $j$ there are a convex set $\Lambda_j\subseteq\mathbb R^N_{\ge0}$ of feasible Poisson rate vectors with $0\in\Lambda_j$ (Assumption 2) and a concave revenue rate $R_j$ on $\Lambda_j$ with $R_j(0)=0$. Write $\Lambda_t$ and $R_t$ for the set and the function of the piece holding $t$.
--
--   The **$k$-scaled instance** of $\mathbb P_{C,k}$ has capacities $k\,b_m$, rate sets $k\Lambda_j$ and revenue rates $x\mapsto k\,R_j(x/k)$, with $A$, $T$ and the pieces unchanged.
--
--   This is the data of every statement of the mission.
--
--   **Formalization Note** Resources and products are `Fin M`, `Fin N`, counted from $0$. Prices are not modelled: the invertible rate–price map of p.5 lets a policy choose rates. Pieces are half-open and the last one contains $T$. No closedness of $\Lambda_j$, continuity of $R_j$ or boundedness is assumed. `rateSet` is empty and `revRate` is $0$ outside $[0,T]$. `scale` is total in $k$; only $k\ge1$ is used.
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, §3, pp.5–6 (model, Assumption 2) and p.8 (scaling)

import Mathlib

open Set
open scoped Pointwise

namespace StateIndepNRM

/-- An instance of the continuous-price network pricing problem `P_C`
(Manchiraju–Dawande–Janakiraman, SSRN 3831496, §3, pp.5–6): `M` resources, `N` products, a
consumption matrix `a`, capacities `b`, a horizon `T`, and a piecewise-stationary demand model on
the `J` pieces cut out by `0 = s₀ < s₁ < … < s_J = T`. On piece `j`, `Λ j` is the convex set of
feasible Poisson rate vectors and `R j` the concave revenue rate; Assumption 2 (p.6) is
`0 ∈ Λ j`, the null price vector.

**Formalization Note.** Resources and products are `Fin M`, `Fin N` (0-based; the page counts from
1). Prices are not modelled: the invertible rate-price map of p.5 lets a policy choose rates, and
`R j` is the page's `R_t`. `0 ≤ a m n`, with a positive entry in each row and column, is the
reading of p.5 under which "for every n, ∃m such that a_{m,n} > 0" says something. `R j 0 = 0`
records that the null price earns nothing. No closedness of `Λ j`, continuity of `R j` or
boundedness is assumed, and `R j` is only read on `Λ j`. -/
structure Instance (M N : ℕ) where
  a : Matrix (Fin M) (Fin N) ℝ
  a_nonneg : ∀ m n, 0 ≤ a m n
  row_pos : ∀ m, ∃ n, 0 < a m n
  col_pos : ∀ n, ∃ m, 0 < a m n
  b : Fin M → ℕ
  T : ℝ
  T_pos : 0 < T
  J : ℕ
  s : Fin (J + 1) → ℝ
  s_strictMono : StrictMono s
  s_zero : s 0 = 0
  s_last : s (Fin.last J) = T
  Λ : Fin J → Set (Fin N → ℝ)
  R : Fin J → (Fin N → ℝ) → ℝ
  Λ_convex : ∀ j, Convex ℝ (Λ j)
  Λ_nonneg : ∀ j, ∀ x ∈ Λ j, ∀ n, 0 ≤ x n
  zero_mem : ∀ j, (0 : Fin N → ℝ) ∈ Λ j
  R_concave : ∀ j, ConcaveOn ℝ (Λ j) (R j)
  R_zero : ∀ j, R j 0 = 0

namespace Instance

variable {M N : ℕ}

/-- Time `t` lies in piece `j`: pieces are half-open `[s_j, s_{j+1})`, and the last one also
contains `T` (Manchiraju–Dawande–Janakiraman, SSRN 3831496, §3, p.5).

**Formalization Note.** The page does not say which piece owns a breakpoint; the choice changes
nothing on a null set of times, and each `t ∈ [0, T]` lies in exactly one piece. -/
def inPiece (I : Instance M N) (j : Fin I.J) (t : ℝ) : Prop :=
  I.s j.castSucc ≤ t ∧ (t < I.s j.succ ∨ (j.succ = Fin.last I.J ∧ t = I.T))

/-- The set `Λ_t` of feasible rate vectors at time `t` (SSRN 3831496, §3, p.5). It is empty
outside `[0, T]`. -/
def rateSet (I : Instance M N) (t : ℝ) : Set (Fin N → ℝ) :=
  {x | ∃ j, I.inPiece j t ∧ x ∈ I.Λ j}

open Classical in
/-- The revenue rate `R_t(x)` at time `t` (SSRN 3831496, §3, p.6): the value of `R j` for the
piece `j` holding `t`.

**Formalization Note.** Written as a sum over pieces; exactly one term survives for
`t ∈ [0, T]`. It is `0` outside `[0, T]`. -/
noncomputable def revRate (I : Instance M N) (t : ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ j, if I.inPiece j t then I.R j x else 0

/-- The `k`-scaled instance of `P_{C,k}` (SSRN 3831496, §3, p.8): "the demand arrival rates are
scaled by k ... and the capacity of any resource m is k · b_m". The matrix, horizon and pieces are
unchanged, the rate set is `k • Λ j`, and the revenue rate is `x ↦ k R_j(x / k)`.

**Formalization Note.** A price giving rate `λ` in `P_C` gives rate `kλ` in `P_{C,k}`, so the
revenue rate is `kλ·p = k R(λ)`. At `k = 0` this is the degenerate instance with `Λ = {0}`; the
theorems only use `1 ≤ k`. -/
noncomputable def scale (I : Instance M N) (k : ℕ) : Instance M N where
  a := I.a
  a_nonneg := I.a_nonneg
  row_pos := I.row_pos
  col_pos := I.col_pos
  b := fun m => k * I.b m
  T := I.T
  T_pos := I.T_pos
  J := I.J
  s := I.s
  s_strictMono := I.s_strictMono
  s_zero := I.s_zero
  s_last := I.s_last
  Λ := fun j => (k : ℝ) • I.Λ j
  R := fun j x => (k : ℝ) * I.R j ((k : ℝ)⁻¹ • x)
  Λ_convex := fun j => (I.Λ_convex j).smul _
  Λ_nonneg := by
    rintro j _ ⟨y, hy, rfl⟩ n
    exact mul_nonneg (Nat.cast_nonneg k) (I.Λ_nonneg j y hy n)
  zero_mem := fun j => ⟨0, I.zero_mem j, smul_zero _⟩
  R_concave := by
    intro j
    refine ⟨(I.Λ_convex j).smul _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ p q hp hq hpq
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk' : (k : ℝ) ≠ 0 := by positivity
      have hc := (I.R_concave j).2 hx hy hp hq hpq
      have e1 : (k : ℝ)⁻¹ • (k : ℝ) • x = x := inv_smul_smul₀ hk' x
      have e2 : (k : ℝ)⁻¹ • (k : ℝ) • y = y := inv_smul_smul₀ hk' y
      have e3 : (k : ℝ)⁻¹ • (p • (k : ℝ) • x + q • (k : ℝ) • y) = p • x + q • y := by
        rw [smul_comm p, smul_comm q, ← smul_add, inv_smul_smul₀ hk']
      simp only [e1, e2, e3, smul_eq_mul] at hc ⊢
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [mul_le_mul_of_nonneg_left hc hk0]
  R_zero := fun j => by simp [I.R_zero j]

end Instance

end StateIndepNRM


