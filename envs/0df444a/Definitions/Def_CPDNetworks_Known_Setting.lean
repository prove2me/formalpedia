-- Prove2me | Definitions.Def_CPDNetworks_Known_Setting
-- name    : CPDNetworks_Known_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:00.873449+00:00
-- url     : https://prove2.me/theorems/e03fd3ac-7d6d-4e15-80b5-03ddd6010557
-- title:
--   pp. 5–10 — dynamic networks with missing links: finite law, $\mathcal S_n(\omega_n)$, $\mathcal W^\tau_{n,T}(\omega_n,r)$, type I/II errors, Matrix CUSUM, test (10)–(11)
-- statement:
--   This file sets up the model of Enikeeva and Klopp for change-point detection in a dynamic network observed with missing links.
--
--   **Observations.** There are $n$ vertices and $T$ snapshots. At time $t$ one observes the symmetric zero-diagonal matrix $Y^t\in\{0,1\}^{n\times n}$, $Y^t_{ij}=\Omega^t_{ij}A^t_{ij}$, where $A^t$ is the adjacency matrix of the network and $\Omega^t$ records which pairs were sampled. Only $Y$ is observed: its entries $Y^t_{ij}$, $i<j$, are independent Bernoulli variables with success probability $B^t_{ij}=(\Pi\odot\Theta^t)_{ij}$, independent over $t$, where $\Theta^t$ is the connection-probability matrix, $\Pi$ the sampling-probability matrix and $\odot$ the entrywise (Hadamard) product. The probability of an event $E$ of the observations is
--   $$\mathbb P_B(E)=\sum_{y\in E}\ \prod_{t=1}^T\prod_{i<j}\big(B^t_{ij}\big)^{y^t_{ij}}\big(1-B^t_{ij}\big)^{1-y^t_{ij}}.$$
--
--   **Parameter classes.** $\mathcal C_n$ is the set of symmetric matrices with entries in $[0,1]$, and $\mathcal C^0_n$ those with zero diagonal. A sampling matrix $\Pi$ belongs to $\mathcal C_n$ and satisfies $\Pi_{ii}=1$ and $\Pi_{ij}>0$ for all $i,j$. With the column-wise norm $\|M\|_{1,\infty}=\max_j\sum_i|M_{ij}|$,
--   $$\mathcal S_n(\omega_n)=\{(\Theta,\Pi):\Theta\in\mathcal C^0_n,\ \Pi \text{ a sampling matrix},\ \|\Pi\odot\Theta\|_{1,\infty}\le\omega_n\}.$$
--   With $q(x)=\sqrt{x(1-x)}$ and the spectral norm $\|\cdot\|_{2\to2}$, the alternative class at location $\tau$ and energy $r$ is
--   $$\mathcal W^\tau_{n,T}(\omega_n,r)=\{\{(\Theta^a,\Pi),(\Theta^b,\Pi)\}:(\Theta^a,\Pi),(\Theta^b,\Pi)\in\mathcal S_n(\omega_n),\ q(\tau/T)\,\|\Pi\odot(\Theta^a-\Theta^b)\|_{2\to2}\ge r\}.$$
--   Under the null hypothesis every snapshot has edge probabilities $\Pi\odot\Theta^0$. Under the alternative with change at $\tau$, snapshots $1,\dots,\tau$ have $\Pi\odot\Theta^b$ (with $\Theta^b=\Theta^0$) and snapshots $\tau+1,\dots,T$ have $\Pi\odot\Theta^a$ (with $\Theta^a=\Theta^0+\Delta\Theta^\tau$).
--
--   **Errors (Definition 1).** For a test $\psi$ (a $\{0,1\}$-valued function of the data, $1$ meaning "reject"),
--   $$\alpha(\psi)=\sup_{(\Theta^0,\Pi)\in\mathcal S_n(\omega_n)}\mathbb P_{(\Theta^0,\Pi)}\{\psi=1\},\qquad \beta(\psi,R)=\sup_{\tau\in\mathcal D_T}\ \sup_{\mathcal W^\tau_{n,T}(\omega_n,R)}\mathbb P_{(\Theta^0+\Delta\Theta^\tau,\Pi),(\Theta^0,\Pi)}\{\psi=0\}.$$
--
--   **Matrix CUSUM and noise.** For $1\le t\le T-1$,
--   $$Z_T(t)=\sqrt{\tfrac{t(T-t)}{T}}\Big(\tfrac1t\sum_{s=1}^tY^s-\tfrac1{T-t}\sum_{s=t+1}^TY^s\Big),$$
--   and $\xi(t)$ is the same expression with $Y^s$ replaced by the centred matrices $Y^s-B^s$. The weight function is
--   $$\mu^\tau_T(t)=\sqrt{\tfrac{t(T-t)}{T}}\Big(\tfrac{\tau}{t}\mathbf 1_{\{\tau+1\le t\}}+\tfrac{T-\tau}{T-t}\mathbf 1_{\{t\le\tau\}}\Big).$$
--
--   **Test.** The test at a known location $\tau$ rejects when $\|Z_T(\tau)\|_{2\to2}>H$, with threshold
--   $$H_{\alpha,n}=2\sqrt2(1+\epsilon)\sqrt{\omega_n}+C_\epsilon\log(2n/\alpha).$$
--   The predicate "$C$ is a constant of Lemma 12 for $\epsilon$" states display (38): for all $n,T$, $1\le t\le T-1$, all $B^1,\dots,B^T\in\mathcal C^0_n$ and $\delta\in(0,1)$, with probability larger than $1-\delta$,
--   $$\|\xi(t)\|_{2\to2}\le2\sqrt2(1+\epsilon)\sqrt{\tfrac{t(T-t)}{T}}\Big[\tfrac1{t^2}\sum_{s=1}^t\|B^s\|_{1,\infty}+\tfrac1{(T-t)^2}\sum_{s=t+1}^T\|B^s\|_{1,\infty}\Big]^{1/2}+C\log\tfrac{2n}{\delta}.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** An observation is a function from the $T$ snapshots and the unordered pairs $i<j$ to Booleans; time is 0-based, so snapshot $s$ in Lean is the paper's $s+1$, and "$s<t$" sums the paper's $s=1,\dots,t$. The latent $A^t$ and $\Omega^t$ are integrated out, since the tests and the errors depend only on the law of $Y$. Probabilities are finite sums over the finite observation space (so every test is measurable). The sampling class carries the paper's standing assumptions $\Pi_{ii}=1$, $\Pi_{ij}>0$ (p. 5). The errors are real suprema (`sSup`); the sets are bounded in $[0,1]$, and an empty alternative class gives type II error $0$. Tests are Boolean-valued, `true` meaning rejection. The spectral norm is the published `HighDimProb.RandomMatrices.matrixOpNorm`. The sampling matrix is named `Pm` in Lean because `Π` is reserved syntax.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, pp. 5–10, §2–3 (model (1), (2), (3), (6), (7), (8), Definition 1, (10), (11)); p. 51, display (38)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting

namespace CPDNetworks.Known

open scoped Matrix
open HighDimProb.RandomMatrices

/-- The noise process `ξ(t)`, display (8), p. 8, and p. 50: the CUSUM of the centred matrices
`Y^s − B^s`. -/
noncomputable def noise {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ) (y : CPDNetworks.Lower.Obs n T) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Real.sqrt (t * ((T : ℝ) - t) / T) •
    ((t : ℝ)⁻¹ • ∑ s ∈ Finset.univ.filter (fun s : Fin T => (s : ℕ) < t), (CPDNetworks.Lower.obsMat y s - B s) -
      ((T : ℝ) - t)⁻¹ • ∑ s ∈ Finset.univ.filter (fun s : Fin T => t ≤ (s : ℕ)),
        (CPDNetworks.Lower.obsMat y s - B s))

/-- `μ^τ_T(t)`, display (7), p. 8. -/
noncomputable def mu (T τ t : ℕ) : ℝ :=
  Real.sqrt (t * ((T : ℝ) - t) / T) *
    ((if τ + 1 ≤ t then (τ : ℝ) / t else 0) + (if t ≤ τ then ((T : ℝ) - τ) / ((T : ℝ) - t) else 0))

/-- The conclusion of Lemma 12 (p. 51, display (38)) for the constant `C` and `ϵ = ε`: for all
`n, T`, `1 ≤ t ≤ T − 1`, observed-edge probability matrices `B^s ∈ 𝒞⁰_n` and `δ ∈ (0, 1)`, with
probability larger than `1 − δ`,
`‖ξ(t)‖_{2→2} ≤ 2√2(1+ϵ) √(t(T−t)/T) [t⁻² Σ_{s ≤ t} ‖B^s‖_{1,∞} + (T−t)⁻² Σ_{s > t} ‖B^s‖_{1,∞}]^{1/2}
+ C log(2n/δ)`. -/
def IsNoiseConst (ε C : ℝ) : Prop :=
  ∀ (n T t : ℕ) (B : Fin T → Matrix (Fin n) (Fin n) ℝ) (δ : ℝ),
    (∀ s, CPDNetworks.Lower.IsConnProb0 (B s)) → 1 ≤ t → t < T → 0 < δ → δ < 1 →
      1 - δ < CPDNetworks.Lower.prob B (fun y => matrixOpNorm (noise B y t) ≤
        2 * Real.sqrt 2 * (1 + ε) * Real.sqrt (t * ((T : ℝ) - t) / T) *
          Real.sqrt (((t : ℝ)⁻¹) ^ 2 *
              ∑ s ∈ Finset.univ.filter (fun s : Fin T => (s : ℕ) < t), CPDNetworks.Lower.norm1inf (B s) +
            (((T : ℝ) - t)⁻¹) ^ 2 *
              ∑ s ∈ Finset.univ.filter (fun s : Fin T => t ≤ (s : ℕ)), CPDNetworks.Lower.norm1inf (B s)) +
          C * Real.log (2 * n / δ))

/-- The threshold `H_{α,n} = 2√2(1+ϵ)√ω_n + C_ϵ log(2n/α)`, display (11), p. 10. -/
noncomputable def thrKnown (ε Cε ω α : ℝ) (n : ℕ) : ℝ :=
  2 * Real.sqrt 2 * (1 + ε) * Real.sqrt ω + Cε * Real.log (2 * n / α)

open Classical in
/-- The test `ψ^τ_{n,T}(Y) = 1{‖Z_T(τ)‖_{2→2} > H}`, display (10), p. 10 (`true` = reject H₀). -/
noncomputable def testKnown {n T : ℕ} (τ : ℕ) (H : ℝ) : CPDNetworks.Lower.Obs n T → Bool :=
  fun y => decide (H < matrixOpNorm (CPDNetworks.Lower.cusum y τ))

end CPDNetworks.Known


