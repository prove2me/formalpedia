-- Prove2me | Definitions.Def_RegMCBSDE_Simulation_ProjectionScheme
-- name    : RegMCBSDE_Simulation_ProjectionScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:08.805346+00:00
-- url     : https://prove2.me/theorems/b01b1548-9d92-42a6-8910-f6b54f78ffce
-- title:
--   §2.1–2.2, Definition 1, (9), Proposition 2, pp. 5–6, 10–11, 16 — random data, function bases and the projection–Picard scheme
-- statement:
--   This file fixes the random data of one run of the scheme, the function bases, and the projection–Picard scheme of Section 4 of Gobet, Lemor and Warin, which is the comparison object of Theorem 3.
--
--   **Random data.** On a probability space $(\Omega,\mathcal F,\mathbb P)$ we are given $N\ge1$, $S_0\in\mathbb R^d$, increments $(\Delta W_k)_{k<N}$ in $\mathbb R^q$, a chain $(P^N_{t_k})_{k\le N}$ in $\mathbb R^{d'}$ with $d'\ge d$, and a measurable $\Phi^N:\mathbb R^{d'}\to\mathbb R$. They are **admissible** when there is a filtration $(\mathcal F_k)$ such that $\Delta W_k$ is $\mathcal F_{k+1}$-measurable and independent of $\mathcal F_k$, $P^N_{t_k}$ is $\mathcal F_k$-measurable, $\Delta W_k$ has independent $\mathcal N(0,h)$ components, the first $d$ components of $P^N_{t_k}$ are those of the Euler scheme $S^N_{t_k}$, and $\mathbb E[\Phi^N(P^N_{t_N})]^2<\infty$.
--
--   **Bases.** For $0\le l\le q$ and $0\le k\le N-1$, $p_{l,k}:\mathbb R^{d'}\to\mathbb R^{n_{l,k}}$ is measurable, $p_{0,k}$ serves $Y$ and $p_{l,k}$ ($l\ge1$) serves the $l$-th component of $Z$. They are *admissible* when $\mathbb E|p_{l,k}(P^N_{t_k})|^2<\infty$ and $\mathbb E[p_{l,k}p_{l,k}^*]$ is invertible, *orthonormal* when moreover $\mathbb E[p_{l,k}(P^N_{t_k})p_{l,k}(P^N_{t_k})^*]=\mathrm{Id}$.
--
--   **The projection–Picard scheme** (Definition 1, (9)). With $f_k(\alpha)=f(t_k,S^N_{t_k},\alpha_0\cdot p_{0,k},\dots,\alpha_q\cdot p_{q,k})$ and the response $Y^{N,I,I}_{t_{k+1}}=\alpha^{I,I}_{0,k+1}\cdot p_{0,k+1}$ (and $Y^{N,I,I}_{t_N}=\Phi^N(P^N_{t_N})$), the coefficients satisfy $\alpha^{0,I}_k=0$ and, for $i\ge1$, $\alpha^{i,I}_k$ minimizes
--   $$\mathbb E\Big(Y^{N,I,I}_{t_{k+1}}-\alpha_0\cdot p_{0,k}+hf_k(\alpha^{i-1,I}_k)-\sum_{l=1}^q\alpha_l\cdot p_{l,k}\,\Delta W_{l,k}\Big)^2 .$$
--   Then $Y^{N,i,I}_{t_k}=\alpha^{i,I}_{0,k}\cdot p_{0,k}$ and $Z^{N,i,I}_{l,t_k}=\alpha^{i,I}_{l,k}\cdot p_{l,k}$.
--
--   **Truncation levels** (Proposition 2). For $C_0\in\mathbb R$, $\rho^N_{l,k}(x)=\max(1,C_0|p_{l,k}(x)|)$ and $|\rho^N_k(x)|^2=\sum_{l=0}^q\rho^N_{l,k}(x)^2$. The predicate *the bounds of Proposition 2 hold for $C_0$* says that almost surely $|Y^{N,i,I}_{t_k}|\le\rho^N_{0,k}(P^N_{t_k})$ and $\sqrt h|Z^{N,i,I}_{l,t_k}|\le\rho^N_{l,k}(P^N_{t_k})$ for all $i\ge0$, $k\le N-1$, $1\le l\le q$.
--
--   **Formalization Note** The paper's filtration is the augmented Brownian filtration and $\Delta W_k=W_{t_{k+1}}-W_{t_k}$; the formalization quantifies over every filtration and increment family with the three properties above, which are all the statements use and which the Brownian case satisfies. The Markov representation of $P^N$ is not used by Theorems 2–3 or their proofs and is dropped. The minimization is over the expectation in $[0,\infty]$; the rule is imposed for every $i\ge1$ (the Picard iterations simply continue past $I$, as $\sup_{i\ge0}$ in the proofs requires). The basis index $l\in\{0,\dots,q\}$ is `Fin (q+1)`, and $l=j+1$ is paired with component $j$ of $\Delta W$ (0-based).
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, pp. 5–6, §2.2; pp. 10–11, Definition 1 and Eq. (9); p. 16, Proposition 2 (truncation levels)

import Mathlib
import Definitions.Def_RegMCBSDE_Simulation_Setting

namespace RegMCBSDE.Simulation

open MeasureTheory ProbabilityTheory

/-- The random data of one run of the scheme on a sample space `Ω` (§2.1, p. 5): the number of
time steps `N`, the initial point `S₀ ∈ ℝ^d`, the Brownian increments `ΔW_k ∈ ℝ^q`, the chain
`P^N_{t_k} ∈ ℝ^{d'}` and the terminal function `Φ^N : ℝ^{d'} → ℝ`. -/
structure RefData (d q d' : ℕ) (Ω : Type*) where
  N : ℕ
  S0 : E d
  ΔW : ℕ → Ω → E q
  PN : ℕ → Ω → E d'
  ΦN : E d' → ℝ

/-- The same run with its path `(ΔW, P^N)` replaced by another path `(ΔW', P')` (used for the
simulated copies). -/
def RefData.withPath {d q d' : ℕ} {Ω : Type*} (D : RefData d q d' Ω) (ΔW' : ℕ → Ω → E q)
    (P' : ℕ → Ω → E d') : RefData d q d' Ω :=
  { D with ΔW := ΔW', PN := P' }

/-- Standing hypotheses on the random data (§2.1, p. 5), for a model `m` and a probability `P`:
* `N ≥ 1` and `d ≤ d'`;
* there is a filtration `(𝓕_k)` (standing for `𝓕_{t_k}`) such that, for `k < N`, `ΔW_k` is
  `𝓕_{k+1}`-measurable and independent of `𝓕_k`, and `P^N_{t_k}` is `𝓕_k`-measurable for `k ≤ N`;
* for `k < N`, the components of `ΔW_k` are independent with law `𝒩(0, h)` (so `ΔW_k ∼ 𝒩(0, h I_q)`);
* the first `d` components of `P^N_{t_k}` are those of the Euler scheme `S^N_{t_k}`;
* `Φ^N` is measurable and `𝔼[Φ^N(P^N_{t_N})]² < ∞`. -/
def RefData.IsAdmissible {d q d' : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (m : Model d q)
    (D : RefData d q d' Ω) (P : Measure Ω) : Prop :=
  1 ≤ D.N ∧ d ≤ d' ∧
  (∃ 𝓕 : Filtration ℕ mΩ,
    (∀ k < D.N, Measurable[𝓕 (k + 1)] (D.ΔW k) ∧
        Indep (MeasurableSpace.comap (D.ΔW k) inferInstance) (𝓕 k) P) ∧
    (∀ k ≤ D.N, Measurable[𝓕 k] (D.PN k))) ∧
  (∀ k < D.N, iIndepFun (fun (i : Fin q) (ω : Ω) => D.ΔW k ω i) P ∧
      ∀ i : Fin q, P.map (fun ω => D.ΔW k ω i) = gaussianReal 0 (m.h D.N).toNNReal) ∧
  (∀ k ≤ D.N, ∀ ω, ∀ (i : Fin d) (hi : (i : ℕ) < d'),
      D.PN k ω ⟨i, hi⟩ = m.euler D.N D.S0 D.ΔW k ω i) ∧
  Measurable D.ΦN ∧ MemLp (fun ω => D.ΦN (D.PN D.N ω)) 2 P

/-- Function bases (§2.2, pp. 5–6): for `l ∈ {0, …, q}` (index `l : Fin (q+1)`; `l = 0` is the
`Y`-basis, `l = j+1` is the basis for the `j`-th component of `Z`, paired with the component
`j` of `ΔW`) and each time index `k`, a family `p_{l,k} : ℝ^{d'} → ℝ^{n_{l,k}}`. -/
structure Basis (q d' : ℕ) where
  n : Fin (q + 1) → ℕ → ℕ
  p : (l : Fin (q + 1)) → (k : ℕ) → E d' → (Fin (n l k) → ℝ)

/-- Projection coefficients `α_k = (α_{0,k}, …, α_{q,k})`, `α_{l,k} ∈ ℝ^{n_{l,k}}`. -/
abbrev Coeff {q d' : ℕ} (B : Basis q d') (k : ℕ) := (l : Fin (q + 1)) → Fin (B.n l k) → ℝ

section

variable {d q d' : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The Gram matrix `𝔼[p_{l,k}(P^N_{t_k}) p_{l,k}(P^N_{t_k})^*]`. -/
noncomputable def gram (D : RefData d q d' Ω) (B : Basis q d') (P : Measure Ω) (l : Fin (q + 1))
    (k : ℕ) : Matrix (Fin (B.n l k)) (Fin (B.n l k)) ℝ :=
  fun i j => ∫ ω, B.p l k (D.PN k ω) i * B.p l k (D.PN k ω) j ∂P

/-- Bases with `𝔼|p_{l,k}|² < ∞` and invertible Gram matrix `𝔼(p_{l,k} p_{l,k}^*)` (p. 6), for
`k ≤ N-1`. -/
def Basis.IsAdmissible (B : Basis q d') (D : RefData d q d' Ω) (P : Measure Ω) : Prop :=
  ∀ l, ∀ k < D.N, Measurable (B.p l k) ∧
    (∀ j, MemLp (fun ω => B.p l k (D.PN k ω) j) 2 P) ∧ IsUnit (gram D B P l k).det

/-- Orthonormal bases (p. 16): `𝔼|p_{l,k}|² < ∞` and `𝔼[p_{l,k} p_{l,k}^*] = Id` under the law of
`P^N_{t_k}`, for `k ≤ N-1`. -/
def Basis.IsOrthonormal (B : Basis q d') (D : RefData d q d' Ω) (P : Measure Ω) : Prop :=
  ∀ l, ∀ k < D.N, Measurable (B.p l k) ∧
    (∀ j, MemLp (fun ω => B.p l k (D.PN k ω) j) 2 P) ∧ gram D B P l k = 1

/-- Fourth moments `𝔼|p_{l,k}(P^N_{t_k})|⁴ < ∞` for `k ≤ N-1`. -/
def Basis.HasFourthMoments (B : Basis q d') (D : RefData d q d' Ω) (P : Measure Ω) : Prop :=
  ∀ l, ∀ k < D.N, ∀ j, MemLp (fun ω => B.p l k (D.PN k ω) j) 4 P

/-- The multiplier of the `l`-th block in the regression: `1` for `l = 0`, the component
`ΔW_{j,k}` for `l = j+1`. -/
def dWfac (D : RefData d q d' Ω) (k : ℕ) (l : Fin (q + 1)) (ω : Ω) : ℝ :=
  Fin.cases 1 (fun j : Fin q => D.ΔW k ω j) l

/-- The regression function `α_0 · p_{0,k} + ∑_{l=1}^q α_l · p_{l,k} ΔW_{l,k}` on the path of `D`. -/
noncomputable def regr (D : RefData d q d' Ω) (B : Basis q d') (k : ℕ) (a : Coeff B k) (ω : Ω) : ℝ :=
  ∑ l, (a l ⬝ᵥ B.p l k (D.PN k ω)) * dWfac D k l ω

/-- `f_k(α) = f(t_k, S^N_{t_k}, α_0 · p_{0,k}, …, α_q · p_{q,k})` (p. 6) on the path of `D`. -/
noncomputable def drv (m : Model d q) (D : RefData d q d' Ω) (B : Basis q d') (k : ℕ) (a : Coeff B k)
    (ω : Ω) : ℝ :=
  m.f (m.t D.N k) (m.euler D.N D.S0 D.ΔW k ω) (a 0 ⬝ᵥ B.p 0 k (D.PN k ω))
    (WithLp.toLp 2 (fun j : Fin q => a j.succ ⬝ᵥ B.p j.succ k (D.PN k ω)))

/-- The response `Y^{N,I,I}_{t_{k+1}}` of the projection scheme: `α^{I,I}_{0,k+1} · p_{0,k+1}` if
`k+1 < N`, and `Φ^N(P^N_{t_N})` if `k+1 = N`. Here `αI k` stands for `α^{I,I}_k`. -/
noncomputable def projResp (D : RefData d q d' Ω) (B : Basis q d') (αI : (k : ℕ) → Coeff B k) (k : ℕ)
    (ω : Ω) : ℝ :=
  if k + 1 < D.N then αI (k + 1) 0 ⬝ᵥ B.p 0 (k + 1) (D.PN (k + 1) ω) else D.ΦN (D.PN D.N ω)

/-- The projection–Picard scheme (Definition 1 and (9), pp. 10–11) with `I` Picard iterations at
later times: `α i k` stands for `α^{i,I}_k`. For every `k ≤ N-1`, `α^{0,I}_k = 0`, and for every
`i ≥ 1`, `α^{i,I}_k` minimizes over `(α_0, …, α_q)`
`𝔼(Y^{N,I,I}_{t_{k+1}} - α_0·p_{0,k} + h f_k(α^{i-1,I}_k) - ∑_{l≥1} α_l·p_{l,k} ΔW_{l,k})²`. -/
def IsProjectionScheme (m : Model d q) (D : RefData d q d' Ω) (B : Basis q d') (P : Measure Ω) (I : ℕ)
    (α : ℕ → (k : ℕ) → Coeff B k) : Prop :=
  ∀ k < D.N, α 0 k = 0 ∧ ∀ i, 1 ≤ i →
    IsMinOn (fun a : Coeff B k => ∫⁻ ω, ENNReal.ofReal
        ((projResp D B (α I) k ω + m.h D.N * drv m D B k (α (i - 1) k) ω - regr D B k a ω) ^ 2) ∂P)
      Set.univ (α i k)

/-- The truncation level `ρ^N_{l,k}(x) = max(1, C₀ |p_{l,k}(x)|)` of Proposition 2. -/
noncomputable def rho (B : Basis q d') (C0 : ℝ) (l : Fin (q + 1)) (k : ℕ) (x : E d') : ℝ :=
  max 1 (C0 * Real.sqrt (sqn (B.p l k x)))

/-- `|ρ^N_k(x)|² = ∑_{l=0}^q ρ^N_{l,k}(x)²`. -/
noncomputable def rhoSq (B : Basis q d') (C0 : ℝ) (k : ℕ) (x : E d') : ℝ :=
  ∑ l, rho B C0 l k x ^ 2

/-- The conclusion of Proposition 2 for a given `C₀` and a given projection scheme `α`
(`α i k = α^{i,I}_k`): for every `i ≥ 0` and `k ≤ N-1`, almost surely
`|Y^{N,i,I}_{t_k}| ≤ ρ^N_{0,k}(P^N_{t_k})` and `√h |Z^{N,i,I}_{l,t_k}| ≤ ρ^N_{l,k}(P^N_{t_k})`. -/
def Prop2Bounds (m : Model d q) (D : RefData d q d' Ω) (B : Basis q d') (P : Measure Ω) (C0 : ℝ)
    (α : ℕ → (k : ℕ) → Coeff B k) : Prop :=
  ∀ i, ∀ k < D.N,
    (∀ᵐ ω ∂P, |α i k 0 ⬝ᵥ B.p 0 k (D.PN k ω)| ≤ rho B C0 0 k (D.PN k ω)) ∧
    ∀ j : Fin q, ∀ᵐ ω ∂P,
      Real.sqrt (m.h D.N) * |α i k j.succ ⬝ᵥ B.p j.succ k (D.PN k ω)| ≤ rho B C0 j.succ k (D.PN k ω)

end

end RegMCBSDE.Simulation


