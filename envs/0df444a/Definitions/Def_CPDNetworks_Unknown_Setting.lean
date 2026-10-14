-- Prove2me | Definitions.Def_CPDNetworks_Unknown_Setting
-- name    : CPDNetworks_Unknown_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:13.213074+00:00
-- url     : https://prove2.me/theorems/171d75a7-550a-4cd4-ac95-7f1b262c30d4
-- title:
--   pp. 5–12 — network model with missing links, its finite law, 𝒮_n(ω_n), 𝒲^τ_{n,T}(ω_n, r), type I/II errors, Matrix CUSUM, μ^τ_T, dyadic grid (13), test (14)–(15)
-- statement:
--   This file fixes the model and the objects of Enikeeva and Klopp's change-point problem for a dynamic network with missing links.
--
--   **Observations.** There are $n$ vertices and $T$ time points. At time $t$ one observes a symmetric matrix $Y^t\in\{0,1\}^{n\times n}$ with zero diagonal, $Y^t_{ij}=\Omega^t_{ij}A^t_{ij}$, where $A^t$ is the adjacency matrix of the network and $\Omega^t$ indicates which pairs were sampled. The entries $Y^t_{ij}$, $i<j$, are independent over pairs and over time, with
--   $$Y^t_{ij}\sim\mathrm{Bernoulli}\big(B^t_{ij}\big),\qquad B^t=\Pi\odot\Theta^t,$$
--   where $\Theta^t$ is the matrix of connection probabilities, $\Pi$ the matrix of sampling probabilities and $\odot$ the entrywise (Hadamard) product. The law $\mathrm P_B$ of $Y=(Y^1,\dots,Y^T)$ is a finite product of Bernoulli laws.
--
--   **Classes.** $\mathcal C_n$ is the set of symmetric matrices with entries in $[0,1]$, and $\mathcal C_n^0$ those of them with zero diagonal. Sampling matrices are those $\Pi\in\mathcal C_n$ with $\Pi_{ii}=1$ and $\Pi_{ij}>0$ for all $i,j$. With the column norm $\|M\|_{1,\infty}=\max_j\sum_i|M_{ij}|$,
--   $$\mathcal S_n(\omega_n)=\{(\Theta,\Pi):\Theta\in\mathcal C_n^0,\ \Pi\text{ a sampling matrix},\ \|\Pi\odot\Theta\|_{1,\infty}\le\omega_n\},$$
--   and, with $q(x)=\sqrt{x(1-x)}$ and the spectral norm $\|\cdot\|_{2\to2}$,
--   $$\mathcal W^\tau_{n,T}(\omega_n,r)=\{\{(\Theta^a,\Pi),(\Theta^b,\Pi)\}:(\Theta^a,\Pi),(\Theta^b,\Pi)\in\mathcal S_n(\omega_n),\ q(\tau/T)\,\|\Pi\odot(\Theta^a-\Theta^b)\|_{2\to2}\ge r\}.$$
--   Under $H_0$ every $B^t$ equals $\Pi\odot\Theta^0$; under the alternative with change at $\tau$, $B^t=\Pi\odot\Theta^b$ for $1\le t\le\tau$ and $B^t=\Pi\odot\Theta^a$ for $\tau<t\le T$.
--
--   **Errors (Definition 1).** For a test $\psi$ (a $\{0,1\}$-valued function of $Y$) the type I error is $\alpha(\psi)=\sup_{(\Theta^0,\Pi)\in\mathcal S_n(\omega_n)}\mathrm P_{(\Theta^0,\Pi)}\{\psi=1\}$, and for a set $\mathcal D$ of change points the type II error is
--   $$\beta(\psi,R)=\sup_{\tau\in\mathcal D}\ \sup_{\mathcal W^\tau_{n,T}(\omega_n,R)}\mathrm P\{\psi=0\}.$$
--   $\mathcal D_T=\{1,\dots,T-1\}$ is the set of possible change points.
--
--   **Statistics.** The Matrix CUSUM (6), the noise process (8) with $X^s=Y^s-B^s$, and the signal profile (7) are
--   $$Z_T(t)=\sqrt{\tfrac{t(T-t)}{T}}\Big(\tfrac1t\sum_{s=1}^tY^s-\tfrac1{T-t}\sum_{s=t+1}^TY^s\Big),\qquad \xi(t)=\sqrt{\tfrac{t(T-t)}{T}}\Big(\tfrac1t\sum_{s=1}^tX^s-\tfrac1{T-t}\sum_{s=t+1}^TX^s\Big),$$
--   $$\mu^\tau_T(t)=\sqrt{\tfrac{t(T-t)}{T}}\Big(\tfrac\tau t\mathbf 1_{\{\tau+1\le t\le T\}}+\tfrac{T-\tau}{T-t}\mathbf 1_{\{1\le t\le\tau\}}\Big).$$
--   The predicate "$C$ is a constant of Lemma 12 for $\epsilon$" says that for all $n$, $T$, $1\le t\le T-1$, all $B^1,\dots,B^T\in\mathcal C^0_n$ and all $\delta\in(0,1)$, with $\mathrm P_B$-probability larger than $1-\delta$,
--   $$\|\xi(t)\|_{2\to2}\le2\sqrt2(1+\epsilon)\sqrt{\tfrac{t(T-t)}{T}}\Big[\tfrac1{t^2}\sum_{s=1}^t\|B^s\|_{1,\infty}+\tfrac1{(T-t)^2}\sum_{s=t+1}^T\|B^s\|_{1,\infty}\Big]^{1/2}+C\log\tfrac{2n}{\delta}.$$
--
--   **Grid and test (13)–(15).** The dyadic grid is $\mathcal T=\mathcal T^L\cup\mathcal T^R$ with $\mathcal T^L=\{2^k:0\le k\le\lfloor\log_2(T/2)\rfloor\}$ and $\mathcal T^R=\{T-2^k:0\le k\le\lfloor\log_2(T/2)\rfloor\}$. Given $\epsilon$, $C_\epsilon$, $\omega_n$ and a level $\alpha$, the threshold and the test are
--   $$H_{\alpha,n,T}=2\sqrt2(1+\epsilon)\sqrt{\omega_n}+C_\epsilon\log\frac{4n\log_2(T)}{\alpha},\qquad \psi_{n,T}(Y)=\mathbf 1\Big\{\max_{t\in\mathcal T}\|Z_T(t)\|_{2\to2}>H_{\alpha,n,T}\Big\}.$$
--
--   These objects are shared by every statement of the mission: the goal (Theorem 3), Lemmas 5, 6 and 12, the decomposition (7) and the grid facts.
--
--   **Formalization Note.** Only $Y$ is observed and the latent $A^t,\Omega^t$ are integrated out, as in the paper's tests and likelihoods, so the law is the finite product $\mathrm P_B(y)=\prod_t\prod_{i<j}B^t_{ij}{}^{y^t_{ij}}(1-B^t_{ij})^{1-y^t_{ij}}$ and probabilities are finite sums; no measure theory is needed and every test is measurable. Observations are Boolean functions of a 0-based time index and of an unordered pair encoded as $i<j$; Lean's time $s$ is the paper's $s+1$, so "$s<t$" is the paper's $1\le s\le t$. Tests are Boolean-valued ("reject" is `true`). The sampling-matrix class carries the paper's standing assumptions $\Pi_{ii}=1$, $\Pi_{ij}>0$ (§2, p. 5). The errors are real suprema (`sSup`) of sets of probabilities, which lie in $[0,1]$; the supremum of an empty class is $0$. The spectral norm is the published `HighDimProb.RandomMatrices.matrixOpNorm`. $\lfloor\log_2(T/2)\rfloor$ is computed as `Nat.log 2 (T / 2)` with natural division, which agrees for $T\ge2$; "$\max_{t\in\mathcal T}\|Z_T(t)\|>H$" is written "$\exists t\in\mathcal T$, $\|Z_T(t)\|>H$", equivalent for the finite grid. The Lean name `Pi` stands for $\Pi$ (`Π` is a Lean keyword).
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, pp. 5–12 and 51, §2–3.4, (1)–(3), (6)–(8), Definition 1, (13)–(15), (38)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Known_Setting
import Definitions.Def_CPDNetworks_Lower_Setting

namespace CPDNetworks.Unknown

open scoped Matrix
open HighDimProb.RandomMatrices

open Classical in

/-- The set `𝒟_T = {1, …, T − 1}` of possible change points. -/
def DT (T : ℕ) : Finset ℕ := Finset.Icc 1 (T - 1)

/-- The dyadic grid `𝒯 = 𝒯^L ∪ 𝒯^R` of (13), with `⌊log₂(T/2)⌋ = Nat.log 2 (T / 2)`. -/
def dyadicGrid (T : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (T / 2) + 1)).image (fun k => 2 ^ k) ∪
    (Finset.range (Nat.log 2 (T / 2) + 1)).image (fun k => T - 2 ^ k)

/-- The threshold `H_{α,n,T}` of (15). -/
noncomputable def thrGrid (ε Cε ω α : ℝ) (n T : ℕ) : ℝ :=
  2 * Real.sqrt 2 * (1 + ε) * Real.sqrt ω + Cε * Real.log (4 * n * Real.logb 2 T / α)

open Classical in
/-- The test `ψ_{n,T}` of (14): reject iff `max_{t ∈ 𝒯} ‖Z_T(t)‖_{2→2} > H`. -/
noncomputable def testGrid {n T : ℕ} (H : ℝ) : CPDNetworks.Lower.Obs n T → Bool :=
  fun y => decide (∃ t ∈ dyadicGrid T, H < matrixOpNorm (CPDNetworks.Lower.cusum y t))

end CPDNetworks.Unknown


