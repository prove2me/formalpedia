-- Prove2me | Definitions.Def_SaddleSplit_Async_Setting
-- name    : SaddleSplit_Async_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:45.6465+00:00
-- url     : https://prove2.me/theorems/adedc794-a940-4085-ba77-cc3be6488683
-- title:
--   Problem 1.1, (1.1)–(1.2), Definitions 2.1, 2.4, (2.13), Assumptions 3.1–3.3, Algorithm 3.4, (2.32), (A.3), pp. 2–31 — data, solution sets, saddle operator, algorithm runs
-- statement:
--   This file fixes the setting of Bùi and Combettes, *Multivariate monotone inclusions in saddle form* (arXiv:2002.06135v3).
--
--   **Spaces and data (Problem 1.1, p. 2).** Let $I$ and $K$ be finite index sets, let $(\mathcal H_i)_{i\in I}$ and $(\mathcal G_k)_{k\in K}$ be real Hilbert spaces, and let $\mathcal H=\bigoplus_{i}\mathcal H_i$ and $\mathcal G=\bigoplus_k\mathcal G_k$ be their Hilbert direct sums. The data consist of operators $A_i:\mathcal H_i\to 2^{\mathcal H_i}$, $C_i,Q_i:\mathcal H_i\to\mathcal H_i$, $R=(R_i)_{i}:\mathcal H\to\mathcal H$, $B^m_k,D^m_k:\mathcal G_k\to 2^{\mathcal G_k}$, $B^c_k,B^\ell_k,D^c_k,D^\ell_k:\mathcal G_k\to\mathcal G_k$, bounded linear $L_{ki}:\mathcal H_i\to\mathcal G_k$, vectors $s^*_i\in\mathcal H_i$, $r_k\in\mathcal G_k$, and constants $\alpha^c_i,\alpha^\ell_i,\beta^c_k,\beta^\ell_k,\delta^c_k,\delta^\ell_k,\chi$. The standing hypotheses [a]–[e] require:
--
--   1. $A_i$, $B^m_k$, $D^m_k$ maximally monotone;
--   2. $C_i$, $B^c_k$, $D^c_k$ cocoercive with constants $\alpha^c_i,\beta^c_k,\delta^c_k\in\left]0,+\infty\right[$;
--   3. $Q_i$, $B^\ell_k$, $D^\ell_k$ and $R$ monotone and Lipschitzian with constants $\alpha^\ell_i,\beta^\ell_k,\delta^\ell_k,\chi\in[0,+\infty[$.
--
--   **Parallel sum and solution sets.** The parallel sum is $B\,\square\,D=(B^{-1}+D^{-1})^{-1}$. With $\mathsf B_k=B^m_k+B^c_k+B^\ell_k$ and $\mathsf D_k=D^m_k+D^c_k+D^\ell_k$, the primal set $\mathscr P$ is the set of $\overline x\in\mathcal H$ with, for every $i$,
--   $$s^*_i\in A_i\overline x_i+C_i\overline x_i+Q_i\overline x_i+R_i\overline x+\sum_{k}L_{ki}^*\big((\mathsf B_k\,\square\,\mathsf D_k)(\textstyle\sum_j L_{kj}\overline x_j-r_k)\big)\qquad(1.1)$$
--   (the Minkowski sum is formed in each equation separately). The dual set $\mathscr D$ (1.2) is the set of $\overline v^*\in\mathcal G$ for which some $x\in\mathcal H$ satisfies $s^*_i-\sum_j L_{ji}^*\overline v^*_j\in A_ix_i+C_ix_i+Q_ix_i+R_ix$ for all $i$ and $\overline v^*_k\in(\mathsf B_k\,\square\,\mathsf D_k)(\sum_jL_{kj}x_j-r_k)$ for all $k$. The Kuhn–Tucker set $\mathsf Z\subset\mathcal H\oplus\mathcal G$ (2.13) consists of the pairs $(\overline x,\overline v^*)$ with the first condition at $\overline x$ and $\sum_jL_{kj}\overline x_j-r_k\in\mathsf B_k^{-1}\overline v^*_k+\mathsf D_k^{-1}\overline v^*_k$.
--
--   **Saddle operator (Definitions 2.1, 2.4).** On $\mathbf X=\mathcal H\oplus\mathcal G\oplus\mathcal G\oplus\mathcal G$ the saddle operator $\boldsymbol{\mathcal S}$ (2.11) sends $(x,y,z,v^*)$ to the product of the sets $-s^*_i+A_ix_i+C_ix_i+Q_ix_i+R_ix+\sum_kL^*_{ki}v^*_k$, $B^m_ky_k+B^c_ky_k+B^\ell_ky_k-v^*_k$, $D^m_kz_k+D^c_kz_k+D^\ell_kz_k-v^*_k$ and $\{r_k+y_k+z_k-\sum_iL_{ki}x_i\}$. The operator $\mathbf M$ (2.28) is the same without $C_i$, $B^c_k$, $D^c_k$, and $\mathbf C(x,y,z,v^*)=((C_ix_i)_i,(B^c_ky_k)_k,(D^c_kz_k)_k,0)$ (2.29).
--
--   **Iterations.** The file also records, as predicates on given sequences, a run of the outer-approximation iteration (2.32) of Proposition 2.6, a run of the half-space iteration (A.3) of Lemma A.4, Assumptions 3.1–3.3 (step-size ranges with (3.1), the activation windows $I_n,K_n$ and the lags $\pi_i(n),\omega_k(n)$), and a run of Algorithm 3.4, (3.3): every assignment of (3.3), the carry-over of inactive blocks, the quantity $\Delta_n$ with $(4\alpha)^{-1}$, and the relaxed update if $\Delta_n>0$, no move otherwise.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Direct sums are `PiLp 2` and nested `WithLp 2` products, so norms and inner products are the ℓ² ones. Set-valued operators are maps `E → Set E`, with the published notions of monotonicity, maximal monotonicity, cocoercivity (`β‖Cx−Cy‖² ≤ ⟪Cx−Cy, x−y⟫`), resolvent, inverse and sum. A run of Algorithm 3.4 takes the resolvents as given maps `JA i γ`, `JB k γ`, `JD k γ`; the theorems constrain them by `IsResolvent` for every `γ > 0`. The carry-over "$a_{i,n}=a_{i,n-1}$ for $i\notin I_n$" is stated at $n+1$ (by Assumption 3.2 every block is active at $n=0$). Assumption 3.3's $n-T\le\pi_i(n)\le n$ is written $\pi_i(n)\le n\le\pi_i(n)+T$ to avoid natural-number subtraction, and (3.1)'s maximum over a finite family is written as one strict inequality per member. α is pinned by `IsLeast`.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, pp. 2–31, Problem 1.1, (1.1), (1.2), p. 4 (parallel sum, cocoercivity), Definitions 2.1, 2.4, (2.11), (2.13), (2.28), (2.29), (2.32), Assumptions 3.1–3.3, Algorithm 3.4 (3.3), Lemma A.4 (A.3)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

namespace SaddleSplit.Async

open InnerProductSpace
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-! # Bùi & Combettes, *Multivariate monotone inclusions in saddle form* (arXiv:2002.06135v3)

Data and standing hypotheses of Problem 1.1 (p. 2), the parallel sum (p. 4), the primal and dual
solution sets (1.1)–(1.2), the Kuhn–Tucker set (2.13), the saddle operator (2.11) and its splitting
(2.28)–(2.29), and the iterations (3.3) (Algorithm 3.4), (2.32) (Proposition 2.6) and (A.3)
(Lemma A.4). Set-valued operators are maps `E → Set E`; monotone, maximally monotone, `zer`,
cocoercive, resolvent and weak convergence are the published `ThreeOpSplitting.Convergence`
notions, and `opInv`, `opAdd` the published `DouglasRachfordPPA.GenDR` ones. -/

/-- Set-valued plus single-valued: `(T + C) x = {u + C x | u ∈ T x}`. -/
def addSV {E : Type*} [Add E] (T : E → Set E) (C : E → E) : E → Set E :=
  fun x => {w | ∃ u ∈ T x, w = u + C x}

/-- The parallel sum `B □ D = (B⁻¹ + D⁻¹)⁻¹` (p. 4). -/
def parSum {E : Type*} [Add E] (B D : E → Set E) : E → Set E :=
  opInv (opAdd (opInv B) (opInv D))

/-- A single-valued `Q` is monotone and Lipschitzian with constant `c ∈ [0, +∞[`. -/
def IsMonoLip {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Q : E → E) (c : ℝ) :
    Prop :=
  (∀ x y, 0 ≤ ⟪x - y, Q x - Q y⟫_ℝ) ∧ 0 ≤ c ∧ ∀ x y, ‖Q x - Q y‖ ≤ c * ‖x - y‖

/-- `T` is `σ`-strongly monotone: `⟪x - y, T x - T y⟫ ≥ σ ‖x - y‖²` (the standard notion of
Bauschke–Combettes [9], used in Lemma A.2). -/
def IsStronglyMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (σ : ℝ)
    (T : E → E) : Prop :=
  ∀ x y, σ * ‖x - y‖ ^ 2 ≤ ⟪x - y, T x - T y⟫_ℝ

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  (H : I → Type*) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, CompleteSpace (H i)]
  (G : K → Type*) [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
  [∀ k, CompleteSpace (G k)]

/-- The data of Problem 1.1 (p. 2): operators `A_i, C_i, Q_i, R_i` on `𝓗_i`, `Bᵐ_k, Bᶜ_k, Bˡ_k`,
`Dᵐ_k, Dᶜ_k, Dˡ_k` on `𝓖_k`, bounded linear `L_{ki} : 𝓗_i → 𝓖_k`, vectors `s*_i`, `r_k`, and the
constants `αᶜ_i, αˡ_i, βᶜ_k, βˡ_k, δᶜ_k, δˡ_k, χ`. `R` is `x ↦ (R_i x)_{i ∈ I}` on `𝓗 = ⨁ 𝓗_i`. -/
structure Problem where
  A : ∀ i, H i → Set (H i)
  C : ∀ i, H i → H i
  Q : ∀ i, H i → H i
  R : PiLp 2 H → PiLp 2 H
  Bm : ∀ k, G k → Set (G k)
  Bc : ∀ k, G k → G k
  Bl : ∀ k, G k → G k
  Dm : ∀ k, G k → Set (G k)
  Dc : ∀ k, G k → G k
  Dl : ∀ k, G k → G k
  L : ∀ k i, H i →L[ℝ] G k
  s : ∀ i, H i
  r : ∀ k, G k
  αc : I → ℝ
  αl : I → ℝ
  βc : K → ℝ
  βl : K → ℝ
  δc : K → ℝ
  δl : K → ℝ
  χ : ℝ

variable {H G}

/-- The standing hypotheses [a]–[e] of Problem 1.1 ([d], `L_{ki}` linear and bounded, is the type
of `L`). -/
def Problem.Hyp (P : Problem H G) : Prop :=
  (∀ i, IsMaximalMonotone (P.A i) ∧ 0 < P.αc i ∧ IsCocoercive (P.αc i) (P.C i) ∧
      IsMonoLip (P.Q i) (P.αl i)) ∧
  (∀ k, IsMaximalMonotone (P.Bm k) ∧ 0 < P.βc k ∧ IsCocoercive (P.βc k) (P.Bc k) ∧
      IsMonoLip (P.Bl k) (P.βl k)) ∧
  (∀ k, IsMaximalMonotone (P.Dm k) ∧ 0 < P.δc k ∧ IsCocoercive (P.δc k) (P.Dc k) ∧
      IsMonoLip (P.Dl k) (P.δl k)) ∧
  IsMonoLip P.R P.χ

/-- `Bᵐ_k + Bᶜ_k + Bˡ_k`. -/
def Problem.Bsum (P : Problem H G) (k : K) : G k → Set (G k) :=
  addSV (addSV (P.Bm k) (P.Bc k)) (P.Bl k)

/-- `Dᵐ_k + Dᶜ_k + Dˡ_k`. -/
def Problem.Dsum (P : Problem H G) (k : K) : G k → Set (G k) :=
  addSV (addSV (P.Dm k) (P.Dc k)) (P.Dl k)

/-- `Σ_{j ∈ I} L_{kj} x_j`. -/
def Problem.Lx (P : Problem H G) (x : PiLp 2 H) (k : K) : G k :=
  ∑ j, P.L k j (x j)

/-- `Σ_{k ∈ K} L*_{ki} v*_k`. -/
noncomputable def Problem.Ladj (P : Problem H G) (v : PiLp 2 G) (i : I) : H i :=
  ∑ k, (ContinuousLinearMap.adjoint (P.L k i)) (v k)

/-- The set `𝒫` of solutions of the primal problem (1.1): for every `i`,
`s*_i ∈ A_i x_i + C_i x_i + Q_i x_i + R_i x + Σ_k L*_{ki}((B_k □ D_k)(Σ_j L_{kj} x_j − r_k))`,
the Minkowski sum being taken in each equation separately. -/
def primalSet (P : Problem H G) : Set (PiLp 2 H) :=
  {x | ∀ i, ∃ w : ∀ k, G k,
      (∀ k, w k ∈ parSum (P.Bsum k) (P.Dsum k) (P.Lx x k - P.r k)) ∧
      ∃ a ∈ P.A i (x i),
        P.s i = a + P.C i (x i) + P.Q i (x i) + P.R x i + ∑ k, (ContinuousLinearMap.adjoint (P.L k i)) (w k)}

/-- The set `𝒟` of solutions of the dual problem (1.2). -/
noncomputable def dualSet (P : Problem H G) : Set (PiLp 2 G) :=
  {v | ∃ x : PiLp 2 H,
      (∀ i, ∃ a ∈ P.A i (x i), P.s i - P.Ladj v i = a + P.C i (x i) + P.Q i (x i) + P.R x i) ∧
      (∀ k, v k ∈ parSum (P.Bsum k) (P.Dsum k) (P.Lx x k - P.r k))}

/-- The Kuhn–Tucker set `Z ⊂ 𝓗 ⊕ 𝓖` of (2.13). -/
noncomputable def ktSet (P : Problem H G) : Set (PiLp 2 H × PiLp 2 G) :=
  {p | (∀ i, ∃ a ∈ P.A i (p.1 i),
          P.s i - P.Ladj p.2 i = a + P.C i (p.1 i) + P.Q i (p.1 i) + P.R p.1 i) ∧
       (∀ k, P.Lx p.1 k - P.r k ∈ opAdd (opInv (P.Bsum k)) (opInv (P.Dsum k)) (p.2 k))}

variable (H G) in
/-- `𝐗 = 𝓗 ⊕ 𝓖 ⊕ 𝓖 ⊕ 𝓖` (Hilbert direct sum, ℓ² norm). -/
abbrev XSpace := WithLp 2 (PiLp 2 H × WithLp 2 (PiLp 2 G × WithLp 2 (PiLp 2 G × PiLp 2 G)))

/-- The `x`-block of `(x, y, z, v*) ∈ 𝐗`. -/
def pX (X : XSpace H G) : PiLp 2 H := (WithLp.ofLp X).1
/-- The `y`-block of `(x, y, z, v*) ∈ 𝐗`. -/
def pY (X : XSpace H G) : PiLp 2 G := (WithLp.ofLp (WithLp.ofLp X).2).1
/-- The `z`-block of `(x, y, z, v*) ∈ 𝐗`. -/
def pZ (X : XSpace H G) : PiLp 2 G := (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp X).2).2).1
/-- The `v*`-block of `(x, y, z, v*) ∈ 𝐗`. -/
def pV (X : XSpace H G) : PiLp 2 G := (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp X).2).2).2

/-- The point `(x, y, z, v*) ∈ 𝐗`. -/
def mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : XSpace H G :=
  WithLp.toLp 2 (x, WithLp.toLp 2 (y, WithLp.toLp 2 (z, v)))

/-- The saddle operator `𝓢 : 𝐗 → 2^𝐗` of Definition 2.1, (2.11). -/
noncomputable def saddleOp (P : Problem H G) : XSpace H G → Set (XSpace H G) :=
  fun X => {W |
    (∀ i, ∃ a ∈ P.A i (pX X i),
      pX W i = -P.s i + a + P.C i (pX X i) + P.Q i (pX X i) + P.R (pX X) i + P.Ladj (pV X) i) ∧
    (∀ k, ∃ b ∈ P.Bm k (pY X k), pY W k = b + P.Bc k (pY X k) + P.Bl k (pY X k) - pV X k) ∧
    (∀ k, ∃ d ∈ P.Dm k (pZ X k), pZ W k = d + P.Dc k (pZ X k) + P.Dl k (pZ X k) - pV X k) ∧
    (∀ k, pV W k = P.r k + pY X k + pZ X k - P.Lx (pX X) k)}

/-- The operator `𝐌 : 𝐗 → 2^𝐗` of Definition 2.4, (2.28). -/
noncomputable def opM (P : Problem H G) : XSpace H G → Set (XSpace H G) :=
  fun X => {W |
    (∀ i, ∃ a ∈ P.A i (pX X i),
      pX W i = -P.s i + a + P.Q i (pX X i) + P.R (pX X) i + P.Ladj (pV X) i) ∧
    (∀ k, ∃ b ∈ P.Bm k (pY X k), pY W k = b + P.Bl k (pY X k) - pV X k) ∧
    (∀ k, ∃ d ∈ P.Dm k (pZ X k), pZ W k = d + P.Dl k (pZ X k) - pV X k) ∧
    (∀ k, pV W k = P.r k + pY X k + pZ X k - P.Lx (pX X) k)}

/-- The operator `𝐂 : 𝐗 → 𝐗 : (x, y, z, v*) ↦ ((C_i x_i)_i, (Bᶜ_k y_k)_k, (Dᶜ_k z_k)_k, 0)` of
Definition 2.4, (2.29). -/
def opC (P : Problem H G) (X : XSpace H G) : XSpace H G :=
  mkX (WithLp.toLp 2 fun i => P.C i (pX X i)) (WithLp.toLp 2 fun k => P.Bc k (pY X k))
    (WithLp.toLp 2 fun k => P.Dc k (pZ X k)) 0

/-- A run of the iteration (2.32) of Proposition 2.6: for every `n`, `(p_n, p*_n) ∈ gra 𝐌`,
`q_n ∈ 𝐗`, `t*_n = p*_n + 𝐂 q_n`, `Δ_n = ⟪x_n − p_n, t*_n⟫ − (4α)⁻¹‖p_n − q_n‖²`, and
`x_{n+1} = x_n − (λ_n Δ_n / ‖t*_n‖²) t*_n` with `λ_n ∈ [ε, 2 − ε]` if `Δ_n > 0`, `x_{n+1} = x_n`
otherwise. -/
def IsOuterApproxRun (P : Problem H G) (α ε : ℝ)
    (x p ps q t : ℕ → XSpace H G) (Δ lam : ℕ → ℝ) : Prop :=
  ∀ n, ps n ∈ opM P (p n) ∧ t n = ps n + opC P (q n) ∧
    Δ n = ⟪x n - p n, t n⟫_ℝ - (4 * α)⁻¹ * ‖p n - q n‖ ^ 2 ∧
    (0 < Δ n → lam n ∈ Set.Icc ε (2 - ε) ∧
        x (n + 1) = x n - (lam n * Δ n / ‖t n‖ ^ 2) • t n) ∧
    (Δ n ≤ 0 → x (n + 1) = x n)

/-- A run of the iteration (A.3) of Lemma A.4 in a real Hilbert space `𝒦`: for every `n`,
`Z ⊂ H_n = {x | ⟪x, t*_n⟫ ≤ η_n}`, `Δ_n = ⟪x_n, t*_n⟫ − η_n`, and
`x_{n+1} = x_n − (λ_n Δ_n / ‖t*_n‖²) t*_n` with `λ_n ∈ [ε, 2 − ε]` if `Δ_n > 0`, `x_{n+1} = x_n`
otherwise. -/
def IsFejerHalfspaceRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (ε : ℝ) (x t : ℕ → E) (η Δ lam : ℕ → ℝ) : Prop :=
  ∀ n, Z ⊆ {y | ⟪y, t n⟫_ℝ ≤ η n} ∧ Δ n = ⟪x n, t n⟫_ℝ - η n ∧
    (0 < Δ n → lam n ∈ Set.Icc ε (2 - ε) ∧
        x (n + 1) = x n - (lam n * Δ n / ‖t n‖ ^ 2) • t n) ∧
    (Δ n ≤ 0 → x (n + 1) = x n)

variable (I K) in
/-- The parameters of Algorithm 3.4: step sizes `γ_{i,n}, µ_{k,n}, ν_{k,n}, σ_{k,n}`, relaxations
`λ_n`, the activated blocks `I_n ⊂ I`, `K_n ⊂ K`, and the lags `π_i(n)`, `ω_k(n)`. -/
structure Alg34Params where
  γ : I → ℕ → ℝ
  μ : K → ℕ → ℝ
  ν : K → ℕ → ℝ
  sig : K → ℕ → ℝ
  lam : ℕ → ℝ
  In : ℕ → Finset I
  Kn : ℕ → Finset K
  π : I → ℕ → ℕ
  ω : K → ℕ → ℕ

variable (H G) in
/-- The sequences generated by Algorithm 3.4 (bold letters are vectors over `I` or `K`). -/
structure Alg34State where
  x : ℕ → PiLp 2 H
  a : ℕ → PiLp 2 H
  astar : ℕ → PiLp 2 H
  pstar : ℕ → PiLp 2 H
  ξ : ℕ → I → ℝ
  y : ℕ → PiLp 2 G
  z : ℕ → PiLp 2 G
  v : ℕ → PiLp 2 G
  b : ℕ → PiLp 2 G
  d : ℕ → PiLp 2 G
  estar : ℕ → PiLp 2 G
  qstar : ℕ → PiLp 2 G
  tstar : ℕ → PiLp 2 G
  e : ℕ → PiLp 2 G
  η : ℕ → K → ℝ
  Δ : ℕ → ℝ
  θ : ℕ → ℝ

/-- Assumption 3.1 (p. 12): `α = min{αᶜ_i, βᶜ_k, δᶜ_k}`, `σ ∈ ]0, +∞[`, `ε ∈ ]0, 1[` with (3.1)
`σ > 1/(4α)` and `1/ε > max{αˡ_i + χ + σ, βˡ_k + σ, δˡ_k + σ}`, and [a]–[b]:
`γ_{i,n} ∈ [ε, 1/(αˡ_i + χ + σ)]`, `µ_{k,n} ∈ [ε, 1/(βˡ_k + σ)]`, `ν_{k,n} ∈ [ε, 1/(δˡ_k + σ)]`,
`σ_{k,n} ∈ [ε, 1/ε]`. ([c], the initial points, is free.) -/
def Assumption31 (P : Problem H G) (α σ ε : ℝ) (prm : Alg34Params I K) : Prop :=
  IsLeast (Set.range P.αc ∪ Set.range P.βc ∪ Set.range P.δc) α ∧
  0 < σ ∧ 0 < ε ∧ ε < 1 ∧ 1 / (4 * α) < σ ∧
  (∀ i, P.αl i + P.χ + σ < 1 / ε) ∧ (∀ k, P.βl k + σ < 1 / ε) ∧ (∀ k, P.δl k + σ < 1 / ε) ∧
  (∀ i n, prm.γ i n ∈ Set.Icc ε (1 / (P.αl i + P.χ + σ))) ∧
  (∀ k n, prm.μ k n ∈ Set.Icc ε (1 / (P.βl k + σ)) ∧ prm.ν k n ∈ Set.Icc ε (1 / (P.δl k + σ)) ∧
      prm.sig k n ∈ Set.Icc ε (1 / ε))

/-- Assumption 3.2 (p. 12) with window `P = Pw`: the `I_n`, `K_n` are nonempty, `I_0 = I`,
`K_0 = K`, and `⋃_{j=n}^{n+P} I_j = I`, `⋃_{j=n}^{n+P} K_j = K` for every `n`. -/
def Assumption32 (Pw : ℕ) (prm : Alg34Params I K) : Prop :=
  (∀ n, (prm.In n).Nonempty) ∧ (∀ n, (prm.Kn n).Nonempty) ∧
  prm.In 0 = Finset.univ ∧ prm.Kn 0 = Finset.univ ∧
  (∀ n, (Finset.range (Pw + 1)).biUnion (fun j => prm.In (n + j)) = Finset.univ) ∧
  (∀ n, (Finset.range (Pw + 1)).biUnion (fun j => prm.Kn (n + j)) = Finset.univ)

/-- Assumption 3.3 (p. 12) with lag bound `T`: `n − T ≤ π_i(n) ≤ n` and `n − T ≤ ω_k(n) ≤ n`. -/
def Assumption33 (T : ℕ) (prm : Alg34Params I K) : Prop :=
  (∀ i n, prm.π i n ≤ n ∧ n ≤ prm.π i n + T) ∧ (∀ k n, prm.ω k n ≤ n ∧ n ≤ prm.ω k n + T)

/-- `st` is a run of Algorithm 3.4, (3.3) (p. 13), for the data `P`, the constant `α`, the
parameters `prm`, and the resolvent maps `JA i γ = J_{γ A_i}`, `JB k γ = J_{γ Bᵐ_k}`,
`JD k γ = J_{γ Dᵐ_k}`. The carry-over `a_{i,n} = a_{i,n−1}` for `i ∉ I_n` is stated at `n + 1`
(at `n = 0` every block is active by Assumption 3.2). -/
noncomputable def IsAlg34Run (P : Problem H G) (α : ℝ) (prm : Alg34Params I K)
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k) (st : Alg34State H G) : Prop :=
  ∀ n,
    -- for every i ∈ I_n
    (∀ i ∈ prm.In n,
      let m := prm.π i n
      let l := P.Q i (st.x m i) + P.R (st.x m) i + P.Ladj (st.v m) i
      st.a n i = JA i (prm.γ i m) (st.x m i + prm.γ i m • (P.s i - l - P.C i (st.x m i))) ∧
      st.astar n i = (prm.γ i m)⁻¹ • (st.x m i - st.a n i) - l + P.Q i (st.a n i) ∧
      st.ξ n i = ‖st.a n i - st.x m i‖ ^ 2) ∧
    -- for every i ∈ I ∖ I_{n+1}
    (∀ i, i ∉ prm.In (n + 1) →
      st.a (n + 1) i = st.a n i ∧ st.astar (n + 1) i = st.astar n i ∧
      st.ξ (n + 1) i = st.ξ n i) ∧
    -- for every k ∈ K_n
    (∀ k ∈ prm.Kn n,
      let m := prm.ω k n
      let us := st.v m k - P.Bl k (st.y m k)
      let ws := st.v m k - P.Dl k (st.z m k)
      st.b n k = JB k (prm.μ k m) (st.y m k + prm.μ k m • (us - P.Bc k (st.y m k))) ∧
      st.d n k = JD k (prm.ν k m) (st.z m k + prm.ν k m • (ws - P.Dc k (st.z m k))) ∧
      st.estar n k = prm.sig k m • (P.Lx (st.x m) k - st.y m k - st.z m k - P.r k) + st.v m k ∧
      st.qstar n k = (prm.μ k m)⁻¹ • (st.y m k - st.b n k) + us + P.Bl k (st.b n k)
        - st.estar n k ∧
      st.tstar n k = (prm.ν k m)⁻¹ • (st.z m k - st.d n k) + ws + P.Dl k (st.d n k)
        - st.estar n k ∧
      st.η n k = ‖st.b n k - st.y m k‖ ^ 2 + ‖st.d n k - st.z m k‖ ^ 2) ∧
    -- for every k ∈ K ∖ K_{n+1}
    (∀ k, k ∉ prm.Kn (n + 1) →
      st.b (n + 1) k = st.b n k ∧ st.d (n + 1) k = st.d n k ∧
      st.estar (n + 1) k = st.estar n k ∧ st.qstar (n + 1) k = st.qstar n k ∧
      st.tstar (n + 1) k = st.tstar n k ∧ st.η (n + 1) k = st.η n k) ∧
    -- e_{k,n} for every k ∈ K
    (∀ k, st.e n k = P.r k + st.b n k + st.d n k - P.Lx (st.a n) k) ∧
    -- for every i ∈ I
    (∀ i, st.pstar n i = st.astar n i + P.R (st.a n) i + P.Ladj (st.estar n) i) ∧
    st.Δ n = -(4 * α)⁻¹ * (∑ i, st.ξ n i + ∑ k, st.η n k)
      + ∑ i, ⟪st.x n i - st.a n i, st.pstar n i⟫_ℝ
      + ∑ k, (⟪st.y n k - st.b n k, st.qstar n k⟫_ℝ + ⟪st.z n k - st.d n k, st.tstar n k⟫_ℝ
          + ⟪st.e n k, st.v n k - st.estar n k⟫_ℝ) ∧
    (0 < st.Δ n →
      st.θ n = prm.lam n * st.Δ n / (∑ i, ‖st.pstar n i‖ ^ 2
        + ∑ k, (‖st.qstar n k‖ ^ 2 + ‖st.tstar n k‖ ^ 2 + ‖st.e n k‖ ^ 2)) ∧
      st.x (n + 1) = st.x n - st.θ n • st.pstar n ∧
      st.y (n + 1) = st.y n - st.θ n • st.qstar n ∧
      st.z (n + 1) = st.z n - st.θ n • st.tstar n ∧
      st.v (n + 1) = st.v n - st.θ n • st.e n) ∧
    (st.Δ n ≤ 0 →
      st.x (n + 1) = st.x n ∧ st.y (n + 1) = st.y n ∧ st.z (n + 1) = st.z n ∧
      st.v (n + 1) = st.v n)

end SaddleSplit.Async


