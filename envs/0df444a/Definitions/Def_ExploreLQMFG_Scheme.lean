-- Prove2me | Definitions.Def_ExploreLQMFG_Scheme
-- name    : ExploreLQMFG_Scheme
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:46.179982+00:00
-- url     : https://prove2.me/theorems/8d5916a4-ea68-48dd-bf78-1fc371d00d4e
-- title:
--   The forward equation of (2.11), its backward equation in the bounded class, and the tilted geometric fictitious play (2.10)
-- statement:
--   Fix $T>0$, $\varepsilon\in(0,1]$, $\varpi\in(1,\sqrt2]$, the Riccati solution $\eta$ of (2.3), maps $Q^\dagger f$, $R^\dagger g$, an initial mean $m_0=\mathbb E(X_0)\in\mathbb R^d$, and a $d$-dimensional Brownian motion $W$ with augmented filtration $\mathbb F^W$.
--
--   1. **Forward limit.** $m$ is adapted with continuous paths and
--   $$m_t=m_0-\int_0^t\eta_s m_s\,ds+\varepsilon W_t,\qquad t\in[0,T].$$
--   2. **Backward limit, bounded class** (the backward part of (2.11)):
--   $$dh^\varpi_t=\Big(-\frac1\varpi Q^\dagger f(m_t)+\eta_th^\varpi_t+\varpi k^\varpi_th^\varpi_t\Big)dt+\varepsilon k^\varpi_t\,dW_t,\qquad h^\varpi_T=\frac1\varpi R^\dagger g(m_T),$$
--   with $h^\varpi$ continuous and bounded, $k^\varpi$ an $\mathbb R^{d\times d}$-valued process bounded $dt\otimes d\mathbb P$-a.e., and $k\,dW=\sum_j k_{\cdot j}\,dW^j$.
--   3. **The scheme (2.10).** Initial processes $\bar m^0$ (adapted, continuous) and $h^0$ (adapted, continuous, bounded) and, for every $n\ge0$,
--   $$d\bar m^{n+1}_t=-\Big(\eta_t\bar m^{n+1}_t+\frac{(1-\varpi^{-1})\varpi^{-n}}{1-\varpi^{-(n+1)}}h^{n+1}_t\Big)dt+\varepsilon\,dW_t,\qquad \bar m^{n+1}_0=m_0,$$
--   $$dh^{n+1}_t=\Big(-\frac1\varpi Q^\dagger f(\bar m^n_t)+\eta_th^{n+1}_t\Big)dt+\varpi k^{n+1}_th^n_t\,dt+\varepsilon k^{n+1}_t\,dW_t,\qquad h^{n+1}_T=\frac1\varpi R^\dagger g(\bar m^n_T),$$
--   with $\bar m^{n+1}$ adapted and continuous and $(h^{n+1},k^{n+1})$ a square-integrable progressive solution with $h^{n+1}$ continuous.
--
--   The scheme is the tilted geometric fictitious play written under the historical probability: by Lemma 2.1 the best response to the proxy $\bar m^n$ under the tilted measure $\mathbb P^{\varpi h^n/\varepsilon}$ is the feedback $-(\eta X+h^{n+1})$, and the geometric averaging (2.6) of the conditional means (2.5) gives the forward equation.
--
--   **Formalization Note** Forward equations have additive noise and are pathwise integral identities, for every $t\in[0,T]$ almost surely. Backward equations are the published `Peng1990.SMP.SolvesBSDE` with martingale integrands $K_j=\varepsilon\,k_{\cdot j}$ and driver $F(s,\omega,p,K)=\frac1\varpi Q^\dagger f(\cdot)-\eta_sp-\frac\varpi\varepsilon\sum_j z_jK_j$ ($z=h^n_s(\omega)$ for the scheme, $z=p$ for the limit), which is the integral form of the equations above.
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), (2.10)–(2.11) p.21, §2.1.1 p.19 (initial processes), Lemma 2.1 and (2.5)–(2.9) p.20, p.22 (bounded class)

import Mathlib
import Definitions.Def_ExploreLQMFG_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

namespace ExploreLQMFG

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `m` solves the forward equation of the limit system (2.11) of arXiv:2107.00839v2 (p.21):
`dm_t = −η_t m_t dt + ε dW_t`, `m_0 = 𝔼(X₀) = m₀`, on `[0, T]`.

The process is `𝔽^W`-adapted with continuous paths, and for every `t ∈ [0, T]`, almost surely,
`m_t = m₀ − ∫₀ᵗ η_s m_s ds + ε W_t`.

**Formalization Note.**
1. The noise is additive, so the equation is a pathwise integral identity and no stochastic
   integral appears.
2. Only `m₀ = 𝔼(X₀) ∈ ℝᵈ` enters (2.10)–(2.13); the initial state `X₀`, the idiosyncratic noise
   `B` and its intensity `σ` do not, so they are not part of the formal data. Every
   `m₀ ∈ ℝᵈ` is `𝔼(X₀)` for the constant `X₀ = m₀`.
3. Time is `ℝ≥0` (as in the published `Peng1990.SMP`); `[0, T]` is cut out by `t ≤ T`, and the
   time integral is over `[0, t] ⊂ ℝ`. -/
def IsForwardLimit {d : ℕ} {P : Measure Ω} {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : Peng1990.SMP.IsStdBrownian P W) (T : ℝ≥0) (η : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (m₀ : Fin d → ℝ) (m : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  StronglyAdapted (augFiltration hW) m ∧ (∀ ω, Continuous fun t => m t ω) ∧
    ∀ t ≤ T, ∀ᵐ ω ∂P,
      m t ω = m₀ - (∫ s in Set.Icc (0 : ℝ) t, η s *ᵥ m s.toNNReal ω) + ε • W t ω

/-- `(h^ϖ, k^ϖ)` solves the backward equation of the limit system (2.11) of
arXiv:2107.00839v2 (Theorem 2.4, p.21) in the class of bounded processes (p.22):

`dh^ϖ_t = (−(1/ϖ) Q†f(m_t) + η_t h^ϖ_t + ϖ k^ϖ_t h^ϖ_t) dt + ε k^ϖ_t dW_t`,
`h^ϖ_T = (1/ϖ) R†g(m_T)`, `t ∈ [0, T]`,

with `Qf = Q†f`, `Rg = R†g`, `h^ϖ` an `ℝᵈ`-valued and `k^ϖ` an `ℝ^{d×d}`-valued process.

The class: `h^ϖ` has continuous paths and is bounded (a deterministic `M` with
`|h^ϖ_t| ≤ M` for all `t ∈ [0, T]`, almost surely), and `k^ϖ` is bounded `dt ⊗ dℙ`-a.e. on
`[0, T] × Ω`; p.22 asserts existence and uniqueness of (2.11) in this class.

**Formalization Note.** The backward equation is the published `Peng1990.SMP.SolvesBSDE`
for the augmented filtration, with index set `Fin d`, terminal value `ξ = (1/ϖ) R†g(m_T)`,
martingale integrands `K_j := ε · (column j of k^ϖ)` (so `Σⱼ K_j dWʲ = ε k^ϖ dW`, with
`k dW = Σⱼ k_{·j} dWʲ`) and driver
`F(s, ω, p, K) = (1/ϖ) Q†f(m_s(ω)) − η_s p − (ϖ/ε) Σⱼ pⱼ K_j`; since
`(ϖ/ε) Σⱼ pⱼ (ε k_{·j}) = ϖ k p`, the identity
`h_t = ξ + ∫ₜᵀ F ds − ∫ₜᵀ ε k dW` is the integral form of (2.11). `SolvesBSDE` also puts `h^ϖ`
and `k^ϖ` in `L²_𝔽` (progressive, square integrable). -/
def IsLimitBdd {d : ℕ} {P : Measure Ω} {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : Peng1990.SMP.IsStdBrownian P W) (T : ℝ≥0) (η : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (Qf Rg : (Fin d → ℝ) → (Fin d → ℝ)) (ε ϖ : ℝ) (m : ℝ≥0 → Ω → Fin d → ℝ)
    (hϖ : ℝ≥0 → Ω → Fin d → ℝ) (kϖ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ ω, Continuous fun t => hϖ t ω) ∧
    (∃ M : ℝ, ∀ᵐ ω ∂P, ∀ t ≤ T, eNorm (hϖ t ω) ≤ M) ∧
    (∃ M : ℝ, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      frob (kϖ s.toNNReal ω) ≤ M) ∧
    Peng1990.SMP.SolvesBSDE (augFiltration hW) P T W (fun ω => ϖ⁻¹ • Rg (m T ω))
      (fun s ω p K => ϖ⁻¹ • Qf (m s ω) - η s *ᵥ p - (ϖ / ε) • ∑ j, p j • K j)
      hϖ (fun j s ω i => ε * kϖ s ω i j)

/-- The tilted geometric fictitious play, written under the historical probability as the
forward–backward scheme (2.10) of arXiv:2107.00839v2 (p.21), with initial processes
`m̄⁰ = mbar 0` and `h⁰ = h 0` (p.19). For every `n ≥ 0`:

`dm̄ⁿ⁺¹_t = −(η_t m̄ⁿ⁺¹_t + ((1−ϖ⁻¹)ϖ⁻ⁿ/(1−ϖ^{−(n+1)})) hⁿ⁺¹_t) dt + ε dW_t`, `m̄ⁿ⁺¹_0 = 𝔼(X₀)`,
`dhⁿ⁺¹_t = (−(1/ϖ) Q†f(m̄ⁿ_t) + η_t hⁿ⁺¹_t) dt + ϖ kⁿ⁺¹_t hⁿ_t dt + ε kⁿ⁺¹_t dW_t`,
`hⁿ⁺¹_T = (1/ϖ) R†g(m̄ⁿ_T)`.

**How this is the fictitious play.** At step `n + 1` the representative player best responds,
in the problem (2.1) (p.19), to the proxy `m̄ⁿ` of the population mean and to the tilted
measure `ℙ^{ϖhⁿ/ε}`. Lemma 2.1 (p.20) shows that the best response is the feedback
`α = −(ηX + hⁿ⁺¹)`, with `η` the Riccati solution (2.3) and `hⁿ⁺¹` the solution of the BSDE
(2.4) under `ℙ^{ϖhⁿ/ε}`. The new mean `mⁿ⁺¹ = 𝔼[Xⁿ⁺¹ | σ(W)]` (2.5) is averaged geometrically
into `m̄ⁿ⁺¹` (2.6), which gives (2.8)–(2.9). Rewriting (2.4) and (2.9) under `ℙ`
(`dW^{ϖhⁿ/ε} = dW + (ϖ/ε) hⁿ dt`) gives the scheme (2.10). Theorem 2.4 is stated on (2.10).
The telescoping sum that turns (2.8) into (2.9) leaves a drift term
`(ϖ(1−ϖ⁻¹)/(1−ϖ^{−(n+1)})) h⁰_t dt`, which vanishes for the typical choice `h⁰ = 0`; for a
general `h⁰` this definition follows (2.10) as printed, the object of Theorem 2.4.

**Class of solutions (the mission's reading of p.19 and Lemma 2.1(ii)).**
1. `m̄⁰` is any `𝔽^W`-adapted process with continuous paths (typically `𝔼(X₀)`).
2. `h⁰` is any `𝔽^W`-adapted process with continuous paths which is bounded (a deterministic
   `M` with `|h⁰_t| ≤ M` for `t ∈ [0, T]`, a.s.), typically `0`. Boundedness makes the tilted
   measure `ℙ^{ϖh⁰/ε}` used by (2.1) a probability measure.
3. For `n ≥ 0`, `m̄ⁿ⁺¹` is adapted with continuous paths and solves the forward equation (a
   pathwise identity, for every `t ∈ [0, T]` almost surely).
4. For `n ≥ 0`, `hⁿ⁺¹` has continuous paths and `(hⁿ⁺¹, kⁿ⁺¹)` solves the backward equation in
   `L²_𝔽`, as the published `Peng1990.SMP.SolvesBSDE` with `K_j = ε · (column j of kⁿ⁺¹)` and
   driver `F(s, ω, p, K) = (1/ϖ) Q†f(m̄ⁿ_s(ω)) − η_s p − (ϖ/ε) Σⱼ hⁿ_{s,j}(ω) K_j`; since
   `(ϖ/ε) Σⱼ hⁿⱼ (ε kⁿ⁺¹_{·j}) = ϖ kⁿ⁺¹ hⁿ`, this is the integral form of (2.10).

`k 0` is not used. -/
structure IsScheme {d : ℕ} {P : Measure Ω} {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : Peng1990.SMP.IsStdBrownian P W) (T : ℝ≥0) (η : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (Qf Rg : (Fin d → ℝ) → (Fin d → ℝ)) (ε ϖ : ℝ) (m₀ : Fin d → ℝ)
    (mbar h : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (k : ℕ → ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) :
    Prop where
  mbar_adapted : ∀ n, StronglyAdapted (augFiltration hW) (mbar n)
  mbar_cont : ∀ n ω, Continuous fun t => mbar n t ω
  init_h_adapted : StronglyAdapted (augFiltration hW) (h 0)
  h_cont : ∀ n ω, Continuous fun t => h n t ω
  init_h_bdd : ∃ M : ℝ, ∀ᵐ ω ∂P, ∀ t ≤ T, eNorm (h 0 t ω) ≤ M
  forward : ∀ n : ℕ, ∀ t ≤ T, ∀ᵐ ω ∂P,
    mbar (n + 1) t ω = m₀
      - (∫ s in Set.Icc (0 : ℝ) t,
          (η s *ᵥ mbar (n + 1) s.toNNReal ω + geomWeight ϖ n • h (n + 1) s.toNNReal ω))
      + ε • W t ω
  backward : ∀ n : ℕ,
    Peng1990.SMP.SolvesBSDE (augFiltration hW) P T W (fun ω => ϖ⁻¹ • Rg (mbar n T ω))
      (fun s ω p K => ϖ⁻¹ • Qf (mbar n s ω) - η s *ᵥ p - (ϖ / ε) • ∑ j, h n s ω j • K j)
      (h (n + 1)) (fun j s ω i => ε * k (n + 1) s ω i j)

end ExploreLQMFG


