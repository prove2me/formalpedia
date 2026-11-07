-- Prove2me | Definitions.Def_AdaptiveSparsify_ERMInstance
-- name    : AdaptiveSparsify_ERMInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:52.167684+00:00
-- url     : https://prove2.me/theorems/569f803d-78a6-40dd-8215-0e5c916e6181
-- title:
--   ERM instances, the hypotheses of Theorem 1, the input layout, and the success event
-- statement:
--   An instance of the empirical risk minimization problem
--
--   $$\min_{x\in K_1\times\cdots\times K_m,\ A^\top x=b}\ c^\top x,$$
--
--   with $A\in\mathbb R^{n\times d}$, $b\in\mathbb R^d$, $c\in\mathbb R^n$, $n=\sum_i n_i$, with barriers $\phi_i$, a magnitude bound $\kappa$, and given start points $w_i$.
--
--   The instance is admissible for the constant $C_K$ when:
--
--   1. $d\ge1$ and $1\le n_i\le C_K$; each $K_i$ is compact, convex and contained in $[-\kappa,\kappa]^{n_i}$; each $\phi_i$ is a $C_K$-self-concordant barrier for $K_i$;
--   2. $A,b,c$ have entries at most $\kappa$ in absolute value and $A^\top A\succeq\kappa^{-1}I$;
--   3. there is $z$ with $A^\top z=b$ and $B(z_i,1/\kappa)\subseteq K_i$ for all $i$;
--   4. $B(w_i,1/\kappa)\subseteq K_i$ for all $i$.
--
--   Items 3 and 4 are corrections of Theorem 1. The input occupies memory as follows: integer cells $0,1,2$ hold $m,n,d$ and cell $3+i$ holds $n_i$; real cells from $0$ hold $A$ in row-major order, then $b$, $c$, $w$, $\kappa$ and the accuracy $\varepsilon$; every other cell is $0$. The sets, the barriers and $z$ are not in memory. On `halt` the output $x_j$ is real cell $-1-j$.
--
--   A run succeeds for constants $C,k$ when at some step it has halted without fault, has spent at most $C(nd+d^6\sqrt n)(\log(n+d+\kappa+1/\varepsilon+2))^k$ work, and its output $x$ satisfies $x_i\in K_i$ for all $i$, $A^\top x=b$, and $c^\top x\le\varepsilon+c^\top y$ for every feasible $y$.
--
--   **Formalization Note** The barrier predicate is the published `IsNuSelfConcordantBarrier`, the line form of Definition 3.1, which has no matrix inverse in its second item. The minimum of Theorem 1 is written as a bound against every feasible point, so no junk value of an infimum enters.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), (2), p.4; Theorem 1, pp.6–7; §3.1, p.12

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_AdaptiveSparsify_Machine

namespace AdaptiveSparsify

/-!
# ERM instances and the success event of Theorem 1

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), the
problem (2), p.4, the hypotheses of Theorem 1, pp.6–7, and the access model of §3.1, p.12.

**Formalization Note.**
* `IsAdmissible` carries the printed hypotheses and two corrections. **C1**: a point `z` with
  `A⊤z = b` and `B(z_i, 1/κ) ⊆ K_i`. **C2**: given start points `w_i` with `B(w_i, 1/κ) ⊆ K_i`. As
  printed, Theorem 1 has no conclusion on an infeasible instance, and its barrier oracle returns
  nothing until a query lands in `int K_i`.
* `ν_i ≤ C_K` is reading R6 (§6.4, p.45; Appendix C, p.70; "Theorem 1 is the case … ν = O(n)", p.7).
  The barrier predicate is the published `IsNuSelfConcordantBarrier`, the line form of Definition
  3.1 (reading R9).
* `1 ≤ d` and `1 ≤ n_i`: with `d = 0` the time bound is `0`; nonempty blocks keep `m ≤ n`, so
  reading the input fits the bound (reading R8).
* The minimum of Theorem 1 becomes `∀` feasible `y` (reading R7), so no junk value of `sInf` enters.
* Memory layout. Integer cells `0, 1, 2` hold `m, n, d`, and cell `3 + i` holds `n_i`. Real cells
  from `0` on hold `A` in row-major order, then `b`, `c`, the start points `w`, then `κ`, then the
  accuracy `ε`. Every other cell is `0`. `K_i`, `φ_i` and `z` are not in memory. On `halt` the output
  `x_j` is read from real cell `-1 - j`.
-/

open Matrix

/-- An ERM instance `min { c⊤x : x ∈ K₁ × ⋯ × K_m, A⊤x = b }` of (2), p.4, with the bound `κ`, the
barriers `φ_i` and the start points `w`. -/
structure ERMInstance where
  /-- The block structure. -/
  blocks : Blocks
  /-- The number `d` of equality constraints. -/
  d : ℕ
  /-- The constraint matrix `A ∈ ℝ^{n×d}`. -/
  A : Matrix (Fin blocks.n) (Fin d) ℝ
  /-- The right-hand side `b ∈ ℝ^d`. -/
  b : Fin d → ℝ
  /-- The objective `c ∈ ℝⁿ`. -/
  c : Fin blocks.n → ℝ
  /-- The magnitude bound `κ`. -/
  κ : ℝ
  /-- The convex sets `K_i`. -/
  K : ∀ i, Set (EuclideanSpace ℝ (Fin (blocks.dim i)))
  /-- The barriers `φ_i`. -/
  φ : ∀ i, EuclideanSpace ℝ (Fin (blocks.dim i)) → ℝ
  /-- The start points `w` (correction C2). -/
  w : Fin blocks.n → ℝ

namespace ERMInstance

/-- The barrier environment of an instance. -/
def env (I : ERMInstance) : BarrierEnv := ⟨I.blocks, I.K, I.φ⟩

/-- `x` is feasible: `x_i ∈ K_i` for every block and `A⊤x = b`. -/
def Feasible (I : ERMInstance) (x : Fin I.blocks.n → ℝ) : Prop :=
  (∀ i, WithLp.toLp 2 (I.blocks.restrict x i) ∈ I.K i) ∧ I.Aᵀ *ᵥ x = I.b

/-- The hypotheses of Theorem 1 for the constant `C_K`, with corrections C1 and C2 and reading R6. -/
structure IsAdmissible (I : ERMInstance) (CK : ℕ) : Prop where
  d_pos : 1 ≤ I.d
  κ_pos : 0 < I.κ
  dim_pos : ∀ i, 1 ≤ I.blocks.dim i
  dim_le : ∀ i, I.blocks.dim i ≤ CK
  compact : ∀ i, IsCompact (I.K i)
  convex : ∀ i, Convex ℝ (I.K i)
  bounded : ∀ i, ∀ x ∈ I.K i, ∀ l, |x l| ≤ I.κ
  barrier : ∀ i,
    EntropicBarrier.Universal.IsNuSelfConcordantBarrier (I.K i) (I.φ i) (CK : ℝ)
  A_le : ∀ j k, |I.A j k| ≤ I.κ
  b_le : ∀ k, |I.b k| ≤ I.κ
  c_le : ∀ j, |I.c j| ≤ I.κ
  gram : LoewnerLE (I.κ⁻¹ • (1 : Matrix (Fin I.d) (Fin I.d) ℝ)) (I.Aᵀ * I.A)
  strictly_feasible : ∃ z : Fin I.blocks.n → ℝ, I.Aᵀ *ᵥ z = I.b ∧ ∀ i,
    Metric.closedBall (WithLp.toLp 2 (I.blocks.restrict z i)) I.κ⁻¹ ⊆ I.K i
  start : ∀ i, Metric.closedBall (WithLp.toLp 2 (I.blocks.restrict I.w i)) I.κ⁻¹ ⊆ I.K i

/-- The integer input memory. -/
def intMem (I : ERMInstance) : ℤ → ℤ := fun a =>
  if a = 0 then I.blocks.m
  else if a = 1 then I.blocks.n
  else if a = 2 then I.d
  else if h : 3 ≤ a ∧ (a - 3).toNat < I.blocks.m then I.blocks.dim ⟨(a - 3).toNat, h.2⟩
  else 0

/-- The real input memory for accuracy `ε`, by nonnegative offset. -/
noncomputable def realMemAt (I : ERMInstance) (ε : ℝ) (o : ℕ) : ℝ :=
  let n := I.blocks.n
  let d := I.d
  if h₁ : o < n * d then
    I.A ⟨o / d, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h₁)⟩
      ⟨o % d, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro h; simp [h] at h₁))⟩
  else if h₂ : o - n * d < d then I.b ⟨o - n * d, h₂⟩
  else if h₃ : o - n * d - d < n then I.c ⟨o - n * d - d, h₃⟩
  else if h₄ : o - n * d - d - n < n then I.w ⟨o - n * d - d - n, h₄⟩
  else if o - n * d - d - n - n = 0 then I.κ
  else if o - n * d - d - n - n = 1 then ε
  else 0

/-- The real input memory for accuracy `ε`. Negative cells are `0`. -/
noncomputable def realMem (I : ERMInstance) (ε : ℝ) : ℤ → ℝ := fun a =>
  if 0 ≤ a then I.realMemAt ε a.toNat else 0

/-- The run of `P` on `I` with accuracy `ε` and tape `ω`. -/
noncomputable def runOn (P : Program) (I : ERMInstance) (ε : ℝ) (ω : ℕ → ℝ) (t : ℕ) : State :=
  run P I.env ω (init I.intMem (I.realMem ε)) t

/-- The output read from a state: `x_j` is real cell `-1 - j`. -/
def output (I : ERMInstance) (s : State) : Fin I.blocks.n → ℝ :=
  fun j => s.core.mem (-1 - ((j : ℕ) : ℤ))

/-- The time bound `C (nd + d⁶√n) (log(n + d + κ + 1/ε + 2))^k` of Theorem 1. -/
noncomputable def timeBound (I : ERMInstance) (ε C : ℝ) (k : ℕ) : ℝ :=
  C * ((I.blocks.n : ℝ) * I.d + (I.d : ℝ) ^ 6 * Real.sqrt I.blocks.n) *
    (Real.log ((I.blocks.n : ℝ) + I.d + I.κ + 1 / ε + 2)) ^ k

/-- The success event of Theorem 1 at `(P, I, ε, C, k, ω)`: at some step the run has halted without
fault, within the time bound, and its output is feasible and `ε`-optimal against every feasible
point. -/
def Success (P : Program) (I : ERMInstance) (ε C : ℝ) (k : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℕ,
    (runOn P I ε ω t).halted = true ∧
    (runOn P I ε ω t).faulted = false ∧
    ((runOn P I ε ω t).work : ℝ) ≤ I.timeBound ε C k ∧
    I.Feasible (I.output (runOn P I ε ω t)) ∧
    ∀ y, I.Feasible y → I.c ⬝ᵥ I.output (runOn P I ε ω t) ≤ ε + I.c ⬝ᵥ y

end ERMInstance

end AdaptiveSparsify


