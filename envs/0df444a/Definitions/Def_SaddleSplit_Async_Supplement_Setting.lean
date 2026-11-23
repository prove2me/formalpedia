-- Prove2me | Definitions.Def_SaddleSplit_Async_Supplement_Setting
-- name    : SaddleSplit_Async_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:18:04.216316+00:00
-- url     : https://prove2.me/theorems/b1a33483-bb0d-498a-af82-b731f2a38645
-- title:
--   (2.33), (2.34), Algorithm 3.6 (3.56), (A.4), Notation p. 4 — the function Ξ, metric projection, runs of the strongly convergent iterations
-- statement:
--   This file adds to the published setting of Bùi and Combettes, *Multivariate monotone inclusions in saddle form* (arXiv:2002.06135v3), the objects needed for the strongly convergent variants of their algorithms. Problem 1.1, the space $\mathbf X=\mathcal H\oplus\mathcal G\oplus\mathcal G\oplus\mathcal G$, the saddle operator $\boldsymbol{\mathcal S}$, its splitting $\mathbf M+\mathbf C$, Assumptions 3.1–3.3 and the parameters and sequences of Algorithm 3.4 are imported from the published `SaddleSplit.Async.Setting`.
--
--   **The function $\Xi$ (2.33).** For $\Delta,\tau,\varsigma,\chi\in\mathbb R$ put $\rho=\tau\varsigma-\chi^2$ and
--   $$\Xi(\Delta,\tau,\varsigma,\chi)=\begin{cases}(1,\ \Delta/\tau),&\rho=0;\\ \big(0,\ (\Delta+\chi)/\tau\big),&\rho\neq0\text{ and }\chi\Delta\geqslant\rho;\\ \big(1-\chi\Delta/\rho,\ \varsigma\Delta/\rho\big),&\rho\neq0\text{ and }\chi\Delta<\rho.\end{cases}$$
--   The paper defines $\Xi$ on $\left]0,+\infty\right[\times\left]0,+\infty\right[\times\mathbb R\times\mathbb R$; the same formula is used on all of $\mathbb R^4$, and every iteration below evaluates it only with $\Delta>0$ and $\tau>0$.
--
--   **Metric projection.** A point $p$ is a nearest point of $C$ to $x$ when $p\in C$ and $\|x-p\|\leqslant\|x-q\|$ for every $q\in C$. The projection $\operatorname{proj}_C x$ is such a nearest point when one exists (for $C$ nonempty, closed and convex in a real Hilbert space it exists and is unique), and $x$ otherwise. The closed half-space $\{y\mid\langle y\mid t^*\rangle\leqslant\eta\}$ is also named.
--
--   **Iteration (A.4) of Lemma A.5.** In a real Hilbert space $\mathcal K$, given $Z\subset\mathcal K$, a run consists of sequences $(x_n)$, $(t^*_n)$, $(\eta_n)$, $(\Delta_n)$, $(\kappa_n)$, $(\lambda_n)$ such that, for every $n$: $Z\subset H_n=\{x\mid\langle x\mid t^*_n\rangle\leqslant\eta_n\}$; $\Delta_n=\langle x_n\mid t^*_n\rangle-\eta_n$; if $\Delta_n>0$ then $(\kappa_n,\lambda_n)=\Xi(\Delta_n,\|t^*_n\|^2,\|x_0-x_n\|^2,\langle x_0-x_n\mid t^*_n\rangle)$ and $x_{n+1}=(1-\kappa_n)x_0+\kappa_nx_n-\lambda_nt^*_n$; otherwise $x_{n+1}=x_n$.
--
--   **Iteration (2.34) of Proposition 2.7.** On $\mathbf X$, a run consists of sequences $(\mathbf x_n)$, $(\mathbf p_n)$, $(\mathbf p^*_n)$, $(\mathbf q_n)$, $(\mathbf t^*_n)$, $(\Delta_n)$, $(\kappa_n)$, $(\lambda_n)$ such that, for every $n$: $(\mathbf p_n,\mathbf p^*_n)\in\operatorname{gra}\mathbf M$; $\mathbf t^*_n=\mathbf p^*_n+\mathbf C\mathbf q_n$; $\Delta_n=\langle\mathbf x_n-\mathbf p_n\mid\mathbf t^*_n\rangle-(4\alpha)^{-1}\|\mathbf p_n-\mathbf q_n\|^2$; if $\Delta_n>0$ then $(\kappa_n,\lambda_n)=\Xi(\Delta_n,\|\mathbf t^*_n\|^2,\|\mathbf x_0-\mathbf x_n\|^2,\langle\mathbf x_0-\mathbf x_n\mid\mathbf t^*_n\rangle)$ and $\mathbf x_{n+1}=(1-\kappa_n)\mathbf x_0+\kappa_n\mathbf x_n-\lambda_n\mathbf t^*_n$; otherwise $\mathbf x_{n+1}=\mathbf x_n$.
--
--   **Algorithm 3.6, (3.56).** A run of Algorithm 3.6 satisfies every line of Algorithm 3.4 up to and including $\Delta_n$ (the activated blocks $i\in I_n$ and $k\in K_n$ evaluated at the delayed iterates $\pi_i(n)$, $\omega_k(n)$, the carry-over of inactive blocks, $e_{k,n}$, $p^*_{i,n}$ and $\Delta_n$), and then, if $\Delta_n>0$, with
--   $$\tau_n=\sum_i\|p^*_{i,n}\|^2+\sum_k\big(\|q^*_{k,n}\|^2+\|t^*_{k,n}\|^2+\|e_{k,n}\|^2\big),$$
--   $$\varsigma_n=\sum_i\|x_{i,0}-x_{i,n}\|^2+\sum_k\big(\|y_{k,0}-y_{k,n}\|^2+\|z_{k,0}-z_{k,n}\|^2+\|v^*_{k,0}-v^*_{k,n}\|^2\big),$$
--   $$\chi_n=\sum_i\langle x_{i,0}-x_{i,n}\mid p^*_{i,n}\rangle+\sum_k\big(\langle y_{k,0}-y_{k,n}\mid q^*_{k,n}\rangle+\langle z_{k,0}-z_{k,n}\mid t^*_{k,n}\rangle+\langle e_{k,n}\mid v^*_{k,0}-v^*_{k,n}\rangle\big),$$
--   it sets $(\kappa_n,\lambda_n)=\Xi(\Delta_n,\tau_n,\varsigma_n,\chi_n)$ and $x_{i,n+1}=(1-\kappa_n)x_{i,0}+\kappa_nx_{i,n}-\lambda_np^*_{i,n}$, $y_{k,n+1}=(1-\kappa_n)y_{k,0}+\kappa_ny_{k,n}-\lambda_nq^*_{k,n}$, $z_{k,n+1}=(1-\kappa_n)z_{k,0}+\kappa_nz_{k,n}-\lambda_nt^*_{k,n}$, $v^*_{k,n+1}=(1-\kappa_n)v^*_{k,0}+\kappa_nv^*_{k,n}-\lambda_ne_{k,n}$; otherwise nothing moves. There is no relaxation sequence: $\kappa_n$ and $\lambda_n$ are computed.
--
--   These objects are used by Lemma A.5, Proposition 2.7 and Theorem 3.7.
--
--   **Formalization Note** The initial point of each iteration is the term of index $0$ of its sequence. $\kappa_n,\lambda_n$ are sequences constrained only when $\Delta_n>0$, where the paper defines them. The run of Algorithm 3.6 reuses the published parameter record `Alg34Params` and state record `Alg34State`; their fields `lam` (relaxation) and `θ` are not used. The lines up to $\Delta_n$ are copied from the published `IsAlg34Run`, including its convention that the carry-over "$a_{i,n}=a_{i,n-1}$ for $i\notin I_n$" is stated at $n+1$. Resolvents enter as given maps, constrained by the theorems. The fourth argument of $\Xi$ is the local quantity $\chi_n$, not the Lipschitz constant $\chi$ of $R$.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 4 (Notation: proj_C), p. 11 (Proposition 2.7: (2.33), (2.34)), pp. 19–20 (Algorithm 3.6, (3.56)), p. 32 (Lemma A.5, (A.4))

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async.Supplement

open InnerProductSpace
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-! # Bùi & Combettes, *Multivariate monotone inclusions in saddle form* (arXiv:2002.06135v3) — supplement

The function `Ξ` of (2.33) (p. 11), the metric projection `proj_C` (Notation, p. 4), and runs of the
strongly convergent iterations (A.4) (Lemma A.5, p. 32), (2.34) (Proposition 2.7, p. 11) and (3.56)
(Algorithm 3.6, pp. 19–20). Everything else (Problem 1.1, `𝐗`, `𝓢`, `𝐌`, `𝐂`, Assumptions 3.1–3.3,
the parameters and sequences of Algorithm 3.4) is the published `SaddleSplit.Async.Setting`. -/

/-- The function `Ξ` of (2.33):
`(Δ, τ, ς, χ) ↦ (1, Δ/τ)` if `ρ = 0`; `(0, (Δ + χ)/τ)` if `ρ ≠ 0` and `χΔ ⩾ ρ`;
`(1 − χΔ/ρ, ςΔ/ρ)` if `ρ ≠ 0` and `χΔ < ρ`, where `ρ = τς − χ²`. The source domain is
`]0, +∞[ × ]0, +∞[ × ℝ × ℝ`; the formula is extended to all of `ℝ⁴` and is only evaluated with
`Δ > 0` and `τ > 0`. The fourth argument `c` is the paper's local `χ`, not the Lipschitz constant
of `R`. -/
noncomputable def Xi (Δ τ ς c : ℝ) : ℝ × ℝ :=
  if τ * ς - c ^ 2 = 0 then (1, Δ / τ)
  else if τ * ς - c ^ 2 ≤ c * Δ then (0, (Δ + c) / τ)
  else (1 - c * Δ / (τ * ς - c ^ 2), ς * Δ / (τ * ς - c ^ 2))

/-- `p` is a nearest point of `C` to `x`: `p ∈ C` and `‖x − p‖ ≤ ‖x − q‖` for every `q ∈ C`. -/
def IsNearest {E : Type*} [NormedAddCommGroup E] (C : Set E) (x p : E) : Prop :=
  p ∈ C ∧ ∀ q ∈ C, ‖x - p‖ ≤ ‖x - q‖

/-- The metric projection `proj_C x` (Notation, p. 4): a nearest point of `C` to `x` when one exists
(for `C` nonempty, closed and convex in a Hilbert space it exists and is unique), and `x` otherwise
(a junk value never reached in this mission's statements). -/
noncomputable def proj {E : Type*} [NormedAddCommGroup E] (C : Set E) (x : E) : E :=
  open Classical in
  if h : ∃ p, IsNearest C x p then h.choose else x

/-- The closed half-space `{y | ⟪y, t⟫ ⩽ η}` (all of the space when `t = 0` and `η ⩾ 0`). -/
def halfSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (t : E) (η : ℝ) : Set E :=
  {y | ⟪y, t⟫_ℝ ≤ η}

/-- A run of the iteration (A.4) of Lemma A.5 in a real Hilbert space `𝒦`, started at `x 0 = x₀`:
for every `n`, `Z ⊂ H_n = {y | ⟪y, t*_n⟫ ⩽ η_n}`, `Δ_n = ⟪x_n, t*_n⟫ − η_n`, and, if `Δ_n > 0`,
`(κ_n, λ_n) = Ξ(Δ_n, ‖t*_n‖², ‖x₀ − x_n‖², ⟪x₀ − x_n, t*_n⟫)` and
`x_{n+1} = (1 − κ_n) x₀ + κ_n x_n − λ_n t*_n`; otherwise `x_{n+1} = x_n`. -/
def IsHaugazeauRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (x t : ℕ → E) (η Δ κ lam : ℕ → ℝ) : Prop :=
  ∀ n, Z ⊆ halfSpace (t n) (η n) ∧ Δ n = ⟪x n, t n⟫_ℝ - η n ∧
    (0 < Δ n →
      (κ n, lam n) = Xi (Δ n) (‖t n‖ ^ 2) (‖x 0 - x n‖ ^ 2) ⟪x 0 - x n, t n⟫_ℝ ∧
      x (n + 1) = (1 - κ n) • x 0 + κ n • x n - lam n • t n) ∧
    (Δ n ≤ 0 → x (n + 1) = x n)

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, CompleteSpace (H i)]
  {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
  [∀ k, CompleteSpace (G k)]

/-- A run of the iteration (2.34) of Proposition 2.7, started at `x 0 = 𝐱₀ ∈ 𝐗`: for every `n`,
`(p_n, p*_n) ∈ gra 𝐌`, `q_n ∈ 𝐗`, `t*_n = p*_n + 𝐂 q_n`,
`Δ_n = ⟪x_n − p_n, t*_n⟫ − (4α)⁻¹‖p_n − q_n‖²`, and, if `Δ_n > 0`,
`(κ_n, λ_n) = Ξ(Δ_n, ‖t*_n‖², ‖x₀ − x_n‖², ⟪x₀ − x_n, t*_n⟫)` and
`x_{n+1} = (1 − κ_n) x₀ + κ_n x_n − λ_n t*_n`; otherwise `x_{n+1} = x_n`. -/
def IsStrongOuterApproxRun (P : Problem H G) (α : ℝ)
    (x p ps q t : ℕ → XSpace H G) (Δ κ lam : ℕ → ℝ) : Prop :=
  ∀ n, ps n ∈ opM P (p n) ∧ t n = ps n + opC P (q n) ∧
    Δ n = ⟪x n - p n, t n⟫_ℝ - (4 * α)⁻¹ * ‖p n - q n‖ ^ 2 ∧
    (0 < Δ n →
      (κ n, lam n) = Xi (Δ n) (‖t n‖ ^ 2) (‖x 0 - x n‖ ^ 2) ⟪x 0 - x n, t n⟫_ℝ ∧
      x (n + 1) = (1 - κ n) • x 0 + κ n • x n - lam n • t n) ∧
    (Δ n ≤ 0 → x (n + 1) = x n)

/-- `st` is a run of Algorithm 3.6, (3.56) (pp. 19–20), for the data `P`, the constant `α`, the
parameters `prm` (its relaxation field `prm.lam` is not used: Algorithm 3.6 has no relaxation
sequence) and the resolvent maps `JA i γ = J_{γ A_i}`, `JB k γ = J_{γ Bᵐ_k}`, `JD k γ = J_{γ Dᵐ_k}`.
Every line up to `Δ_n` is that of Algorithm 3.4 (copied from the published `IsAlg34Run`, carry-over
stated at `n + 1`); then, if `Δ_n > 0`, `(κ_n, λ_n) = Ξ(Δ_n, τ_n, ς_n, χ_n)` with `τ_n, ς_n, χ_n` of
(3.56) and every block moves to `(1 − κ_n)·(initial point) + κ_n·(current point) − λ_n·(direction)`;
otherwise nothing moves. The field `st.θ` is not used. -/
noncomputable def IsAlg36Run (P : Problem H G) (α : ℝ) (prm : Alg34Params I K)
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k) (st : Alg34State H G)
    (κ lam : ℕ → ℝ) : Prop :=
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
      let τ := ∑ i, ‖st.pstar n i‖ ^ 2
        + ∑ k, (‖st.qstar n k‖ ^ 2 + ‖st.tstar n k‖ ^ 2 + ‖st.e n k‖ ^ 2)
      let ς := ∑ i, ‖st.x 0 i - st.x n i‖ ^ 2
        + ∑ k, (‖st.y 0 k - st.y n k‖ ^ 2 + ‖st.z 0 k - st.z n k‖ ^ 2 + ‖st.v 0 k - st.v n k‖ ^ 2)
      let c := ∑ i, ⟪st.x 0 i - st.x n i, st.pstar n i⟫_ℝ
        + ∑ k, (⟪st.y 0 k - st.y n k, st.qstar n k⟫_ℝ + ⟪st.z 0 k - st.z n k, st.tstar n k⟫_ℝ
          + ⟪st.e n k, st.v 0 k - st.v n k⟫_ℝ)
      (κ n, lam n) = Xi (st.Δ n) τ ς c ∧
      (∀ i, st.x (n + 1) i = (1 - κ n) • st.x 0 i + κ n • st.x n i - lam n • st.pstar n i) ∧
      (∀ k, st.y (n + 1) k = (1 - κ n) • st.y 0 k + κ n • st.y n k - lam n • st.qstar n k ∧
        st.z (n + 1) k = (1 - κ n) • st.z 0 k + κ n • st.z n k - lam n • st.tstar n k ∧
        st.v (n + 1) k = (1 - κ n) • st.v 0 k + κ n • st.v n k - lam n • st.e n k)) ∧
    (st.Δ n ≤ 0 →
      st.x (n + 1) = st.x n ∧ st.y (n + 1) = st.y n ∧ st.z (n + 1) = st.z n ∧
      st.v (n + 1) = st.v n)

end SaddleSplit.Async.Supplement


