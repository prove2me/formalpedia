-- Prove2me | Definitions.Def_MirrorBP_JEA_Supplement_Growth
-- name    : MirrorBP_JEA_Supplement_Growth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:46:48.044677+00:00
-- url     : https://prove2.me/theorems/e7fecf4f-e008-4bf2-91aa-a55a691d96cc
-- title:
--   (24), p. 22, and Condition 3, Appendix B.3.1 (PDF 41–42) — finite-buffer congestion function and the growth condition
-- statement:
--   Let $V$, $m=|V|$, $(V_b,\bar d)$, $K$, $\tilde K$ and $\bar q$ be as in the finite-buffer setting (`MirrorBP.JEA.Supplement.Buffer`), and $\bar d_\Sigma=\sum_j\bar d_j$.
--
--   **Congestion function (24).** With $\epsilon=\delta_K/\tilde K$, $h(x)=-x^{-1/2}$, $h_b(x)=(1-x)^{-1/2}-x^{-1/2}$,
--   $$C_b=\frac{h(\epsilon)-h(1/\bar d_\Sigma)}{h_b(\epsilon)-h_b(1/\bar d_\Sigma)},\qquad D_b=h_b(1/\bar d_\Sigma)-C_b^{-1}h(1/\bar d_\Sigma),$$
--   $$f_j(\bar q_j)=\begin{cases}\sqrt m\,C_b\Big(\big(1-\tfrac{\bar q_j}{\bar d_j}\big)^{-1/2}-\big(\tfrac{\bar q_j}{\bar d_j}\big)^{-1/2}-D_b\Big),& j\in V_b,\\[2pt] -\sqrt m\,\bar q_j^{-1/2},& j\notin V_b.\end{cases}$$
--   Since $C_b,D_b$ depend on $K$, (24) is a family indexed by $K$.
--
--   **Condition 3 (growth condition).** A $K$-indexed family $(f_j)_{j\in V}$ satisfies the growth condition with parameters $(\alpha,K_1,M_1,M_2)\in\mathbb R^4_{++}$ if, for every $K>K_1$ at which the finite-buffer model exists, writing $c_j=f_j(\bar d_j/\bar d_\Sigma)$, $\mathcal B(f)=\{\bar q:\max_j|c_j-f_j(\bar q_j)|\le4m\}$ and $W_j=[\bar q_j-1/\tilde K,\bar q_j+1/\tilde K]$, the following hold for all states $q$:
--
--   1. each $f_j$ is strictly increasing and continuously differentiable on $(0,\bar d_j)$; (a) if $q_j=0$ then $f_j(\bar q_j)\le f_k(\bar q_k)$ for all $k$, and if $q_k=d_k$ with $k\in V_b$ then $f_j(\bar q_j)\le f_k(\bar q_k)$ for all $j$; (b) $c_j=c_k$ for all $j,k$;
--   2. each window $W_j$ lies in $(0,\bar d_j)$, and
--      (a) if $\bar q\notin\mathcal B(f)$, then
--   $$\alpha\Big(\max_{j}|c_j-f_j(\bar q_j)|-2m\Big)^+\ \ge\ \frac1{2\tilde K}\max_j\max_{x\in W_j}f_j'(x)+\mathbb 1\{q_j=0\text{ or }d_j,\ \exists j\};\qquad(43)$$
--      (b) for an antiderivative $F(\bar q)=\sum_jF_j(\bar q_j)$, $F_j'=f_j$, one has $F(\bar q)-F(\bar q')\le M_1$ for all states $q,q'$;
--      (c) if $\bar q\in\mathcal B(f)$ then $\max_j\max_{x\in W_j}f_j'(x)\le M_2$;
--      (d) if $q_j=0$ or $q_j=d_j$ for some $j$, then $\bar q\notin\mathcal B(f)$.
--
--   Lemma 9 shows that (24) satisfies Condition 3, and Theorem 4 bounds the loss of MBP for any family satisfying it.
--
--   **Formalization Note** The paper prints the threshold "$K>K_1$" only in 1(a) and 2(a); here every clause is required for every $K>K_1$, since the family depends on $K$ and clauses 2(c), 2(d) fail for (24) at small $K$ (the appendix verifies them for large $K$). The set $\Omega$ of the condition is taken to be the normalized physical states, as in the appendix's verification of 2(b) (sup over $q,q'\in\Omega_K$). The window clause makes the maxima of $f_j'$ in (43) and 2(c) maxima of a continuous function on a compact interval; those maxima are written as bounds for every $j$ and every $x$ in the window. The rpow expressions are only evaluated at points of $(0,\bar d_j)$.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 22, (24) and footnote 6; Appendix B.3.1, appendix pp. 8–9 (PDF 41–42), Condition 3 and (41), (43); Appendix B.3.3, appendix pp. 11–12 (PDF 44–45)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_Supplement_Buffer

namespace MirrorBP.JEA.Supplement

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `h(x) = −x^{−1/2}` (footnote 6, p. 22; Appendix B.3.3, PDF 44). Used at positive arguments. -/
noncomputable def hInv (x : ℝ) : ℝ := -(x ^ (-(1 / 2 : ℝ)))

/-- `h_b(x) = (1 − x)^{−1/2} − x^{−1/2}` (footnote 6, p. 22). Used for `0 < x < 1`. -/
noncomputable def hBuf (x : ℝ) : ℝ := (1 - x) ^ (-(1 / 2 : ℝ)) - x ^ (-(1 / 2 : ℝ))

/-- `ε = δ_K / K̃` with `δ_K = √K` and `K̃` from (23) (footnote 6, p. 22). -/
noncomputable def epsB (dbar : V → ℝ) (K : ℕ) : ℝ := Real.sqrt K / KtB dbar K

/-- `C_b = (h(ε) − h(1/∑_j d̄_j)) / (h_b(ε) − h_b(1/∑_j d̄_j))` (footnote 6, p. 22). -/
noncomputable def Cb (dbar : V → ℝ) (K : ℕ) : ℝ :=
  (hInv (epsB dbar K) - hInv (1 / dSum dbar)) / (hBuf (epsB dbar K) - hBuf (1 / dSum dbar))

/-- `D_b = h_b(1/∑_j d̄_j) − C_b⁻¹ h(1/∑_j d̄_j)` (footnote 6, p. 22). -/
noncomputable def Db (dbar : V → ℝ) (K : ℕ) : ℝ :=
  hBuf (1 / dSum dbar) - (Cb dbar K)⁻¹ * hInv (1 / dSum dbar)

/-- The congestion function vector (24), p. 22, for `K` supply units, `m = |V|` nodes and buffer data
`(Vb, d̄)`:
`f_j(x) = √m · C_b · ((1 − x/d̄_j)^{−1/2} − (x/d̄_j)^{−1/2} − D_b)` for `j ∈ Vb`, and
`f_j(x) = −√m · x^{−1/2}` (the function (8), `fMBP`) for `j ∉ Vb`. The constants `C_b, D_b` depend on
`K` through `ε`, so (24) is a family indexed by `K`. The formulas are used on `0 < x < d̄_j`. -/
noncomputable def congestion24 (Vb : Finset V) (dbar : V → ℝ) (K : ℕ) (j : V) (x : ℝ) : ℝ :=
  if j ∈ Vb then
    Real.sqrt (Fintype.card V) * Cb dbar K * (hBuf (x / dbar j) - Db dbar K)
  else fMBP (Fintype.card V) x

/-- The common centre value `f_j(d̄_j / ∑_ℓ d̄_ℓ)` of node `j` (Condition 3, point 1(b) and point 2,
appendix pp. 8–9, PDF 41–42), for the congestion family `f` at `K` supply units. -/
noncomputable def centre (f : ℕ → V → ℝ → ℝ) (dbar : V → ℝ) (K : ℕ) (j : V) : ℝ :=
  f K j (dbar j / dSum dbar)

/-- `max_{j ∈ V} |f_j(d̄_j/∑_ℓ d̄_ℓ) − f_j(x_j)|` (Condition 3, point 2; the value `0` for empty `V` is
never used). -/
noncomputable def devMax (f : ℕ → V → ℝ → ℝ) (dbar : V → ℝ) (K : ℕ) (x : V → ℝ) : ℝ :=
  if h : (univ : Finset V).Nonempty then
    univ.sup' h (fun j => |centre f dbar K j - f K j (x j)|)
  else 0

/-- Membership in `B(f) = {q̄ ∈ Ω : max_j |f_j(d̄_j/∑_ℓ d̄_ℓ) − f_j(q̄_j)| ≤ 4m}` (Condition 3, point 2,
PDF 42), with `m = |V|`. -/
def InB (f : ℕ → V → ℝ → ℝ) (dbar : V → ℝ) (K : ℕ) (x : V → ℝ) : Prop :=
  ∀ j, |centre f dbar K j - f K j (x j)| ≤ 4 * (Fintype.card V : ℝ)

/-- The boundary event `{q_j = 0 or q_j = d_j, ∃ j ∈ V}` of the indicator in (41) and (43) and of
Condition 3, point 2(d), with `d_j = d̄_j K`. -/
def AtBoundary (dbar : V → ℝ) (K : ℕ) (q : V → ℕ) : Prop :=
  ∃ j, q j = 0 ∨ (q j : ℝ) = dbar j * K

/-- The window `[q̄_j − 1/K̃, q̄_j + 1/K̃]` over which `f_j'` is maximized in (41), (43) and Condition 3,
point 2(c). -/
def window (dbar : V → ℝ) (K : ℕ) (q : V → ℕ) (j : V) : Set ℝ :=
  Set.Icc (qbarB dbar K q j - 1 / KtB dbar K) (qbarB dbar K q j + 1 / KtB dbar K)

open Classical in
/-- **Condition 3** (growth condition for congestion functions, Appendix B.3.1, appendix pp. 8–9,
PDF 41–42) for a congestion family `f K j : ℝ → ℝ` (`K` supply units, node `j`), buffer data `(Vb, d̄)` and
parameters `(α, K₁, M₁, M₂) ∈ ℝ⁴₊₊`. With `m = |V|`, `q̄ = qbarB d̄ K q` the normalization (23) of a physical
state `q ∈ BufStateSpace d̄ K`, and every clause asserted for every `K > K₁` at which the finite-buffer
model exists (`IntegralCapacity d̄ K`):

1. each `f_j` is strictly increasing and continuously differentiable on its domain `(0, d̄_j)`;
   (a) (i) if `q_j = 0` then `f_j(q̄_j) ≤ f_k(q̄_k)` for every `k`; (ii) if `q_k = d_k` with `k ∈ Vb` then
   `f_j(q̄_j) ≤ f_k(q̄_k)` for every `j`;
   (b) `f_j(d̄_j/∑_ℓ d̄_ℓ) = f_k(d̄_k/∑_ℓ d̄_ℓ)` for all `j, k`;
2. the windows `[q̄_j ± 1/K̃]` lie in the domains `(0, d̄_j)` (so that the maxima of `f_j'` below are
   maxima of a continuous function over a compact interval), and
   (a) inequality (43): for `q̄ ∉ B(f)`, every `j` and every `x` in the window of `j`,
   `(1/(2K̃)) f_j'(x) + 1{q_ℓ = 0 or d_ℓ, ∃ ℓ} ≤ α (max_j |f_j(d̄_j/∑d̄) − f_j(q̄_j)| − 2m)⁺`;
   (b) for an antiderivative `F(q̄) = ∑_j F_j(q̄_j)` of `f` (`F_j' = f_j` on `(0, d̄_j)`),
   `F(q̄) − F(q̄') ≤ M₁` for all states `q, q'`;
   (c) for `q̄ ∈ B(f)`, every `j` and every `x` in the window of `j`, `f_j'(x) ≤ M₂`;
   (d) if `q_j = 0` or `q_j = d_j` for some `j`, then `q̄ ∉ B(f)`.

The maxima "max_j max_{x ∈ window} f_j'(x)" of (43) and 2(c) are written as bounds for every `j` and `x`,
which is equivalent because the windows lie in the domains where `f_j'` is continuous. -/
def Condition3 (Vb : Finset V) (dbar : V → ℝ) (f : ℕ → V → ℝ → ℝ) (α K₁ M₁ M₂ : ℝ) : Prop :=
  0 < α ∧ 0 < K₁ ∧ 0 < M₁ ∧ 0 < M₂ ∧
  ∀ K : ℕ, K₁ < (K : ℝ) → IntegralCapacity dbar K →
    -- point 1: monotone and C¹ on the domain
    (∀ j, StrictMonoOn (f K j) (Set.Ioo 0 (dbar j)) ∧ ContDiffOn ℝ 1 (f K j) (Set.Ioo 0 (dbar j))) ∧
    -- point 1(a)
    (∀ q ∈ BufStateSpace dbar K,
      (∀ j, q j = 0 → ∀ k, f K j (qbarB dbar K q j) ≤ f K k (qbarB dbar K q k)) ∧
      (∀ k ∈ Vb, (q k : ℝ) = dbar k * K → ∀ j, f K j (qbarB dbar K q j) ≤ f K k (qbarB dbar K q k))) ∧
    -- point 1(b)
    (∀ j k, centre f dbar K j = centre f dbar K k) ∧
    -- the windows of (41)/(43) lie in the domains
    (∀ q ∈ BufStateSpace dbar K, ∀ j, window dbar K q j ⊆ Set.Ioo 0 (dbar j)) ∧
    -- point 2(a), inequality (43)
    (∀ q ∈ BufStateSpace dbar K, ¬ InB f dbar K (qbarB dbar K q) →
      ∀ j, ∀ x ∈ window dbar K q j,
        1 / (2 * KtB dbar K) * deriv (f K j) x + (if AtBoundary dbar K q then 1 else 0)
          ≤ α * max 0 (devMax f dbar K (qbarB dbar K q) - 2 * (Fintype.card V : ℝ))) ∧
    -- point 2(b)
    (∃ F : V → ℝ → ℝ, (∀ j, ∀ x ∈ Set.Ioo 0 (dbar j), HasDerivAt (F j) (f K j x) x) ∧
      ∀ q ∈ BufStateSpace dbar K, ∀ q' ∈ BufStateSpace dbar K,
        (∑ j, F j (qbarB dbar K q j)) - (∑ j, F j (qbarB dbar K q' j)) ≤ M₁) ∧
    -- point 2(c)
    (∀ q ∈ BufStateSpace dbar K, InB f dbar K (qbarB dbar K q) →
      ∀ j, ∀ x ∈ window dbar K q j, deriv (f K j) x ≤ M₂) ∧
    -- point 2(d)
    (∀ q ∈ BufStateSpace dbar K, AtBoundary dbar K q → ¬ InB f dbar K (qbarB dbar K q))

end MirrorBP.JEA.Supplement


