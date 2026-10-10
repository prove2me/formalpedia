-- Prove2me | Definitions.Def_PowerOfDUniversality_Diffusion_HalfinWhitt
-- name    : PowerOfDUniversality_Diffusion_HalfinWhitt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:34:46.101598+00:00
-- url     : https://prove2.me/theorems/bcd1c2e9-7ea4-4705-bfbc-24d492ae6821
-- title:
--   §2.3 and Theorem 2.4, pp. 7–8 — Halfin–Whitt sequences of JSQ(d) systems and the statement that they have the diffusion limit (2.4)
-- statement:
--   This file states the hypotheses and the conclusion of Theorem 2.4 as reusable predicates.
--
--   **Halfin–Whitt sequences.** Let $\beta>0$, $b\ge2$, $k\ge2$ and let $\nu$ be a probability measure on $\mathbb R^k$. A sequence of JSQ(d) systems, the $j$-th with $N_j$ servers, $d_j$ samples and arrival rate $\lambda_j$, each on its own probability space, is a *Halfin–Whitt sequence* if
--   1. $N_j\to\infty$;
--   2. for all large $j$ the $j$-th system is a JSQ($d_j$) system with buffer $b$;
--   3. $$\frac{N_j-\lambda_j}{\sqrt{N_j}}\to\beta;$$
--   4. for all large $j$, almost surely $Q_{k+1}(0)=0$;
--   5. the vector $(\bar Q_1(0),\dots,\bar Q_k(0))$ of diffusion-scaled initial values converges in distribution to $\nu$, i.e. $\mathbb E\,g(\bar Q_1(0),\dots,\bar Q_k(0))\to\int g\,d\nu$ for every bounded continuous $g:\mathbb R^k\to\mathbb R$.
--
--   **The conclusion of Theorem 2.4.** Processes $X_j$ *have the diffusion limit (2.4)* if there are a probability space carrying a standard Brownian motion $W$, an initial value $\xi\sim\nu$ independent of $W$ and processes $(\bar Q,U_1)$ that almost surely solve (2.4) driven by $W$ from $\xi$, with $X_j\Rightarrow\bar Q$ in $D_{\ell_1}[0,\infty)$.
--
--   **The JSQ statement.** For fixed $\beta,b,k,\nu$, the ordinary JSQ policy has the diffusion limit if every Halfin–Whitt sequence in which every server is sampled ($d_j=N_j$, the JSQ policy) has the diffusion limit (2.4), for any server counts $N_j\to\infty$. The paper uses this result of Eschenfeldt and Gamarnik [8, Theorem 2] in §5, applied to $\bar N=N-n(N)$ servers.
--
--   **Formalization Note** Theorem 2.4 is the case $N_j=j$. Allowing arbitrary server counts is what the proof of Proposition 5.1 (p. 32) needs. The initial convergence is joint convergence of the $k$-vector. Marginal convergence of each $\bar Q_i(0)$, the literal reading of the page, does not determine the law of the limit. The vector coordinate `i : Fin k` is the level $i+1$. Probability spaces are taken in `Type`.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 7, §2.3 (Halfin–Whitt regime); pp. 7–8, Theorem 2.4 (hypotheses and conclusion); pp. 8, 32 ([8, Theorem 2] for ordinary JSQ)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Diffusion_PathSpace
import Definitions.Def_PowerOfDUniversality_Diffusion_System
import Definitions.Def_PowerOfDUniversality_Diffusion_Limit

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Diffusion

/-!
Mukherjee, Borst, van Leeuwaarden & Whiting, arXiv:1612.00723v2, §2.3 (p. 7), Theorem 2.4
(pp. 7–8) and §5 (p. 32): sequences of JSQ(d) systems in the Halfin–Whitt regime, and the
statement "the diffusion-scaled occupancy processes converge to the solution of (2.4)".

A sequence is indexed by `j : ℕ`; system `j` has `Ns j` servers, `d j` sampled servers and arrival
rate `lam j`, and lives on its own probability space `(Ω j, P j)`. Theorem 2.4 itself is the case
`Ns j = j` (the sequence `N = 1, 2, …`); the proof of Proposition 5.1 (p. 32) applies the JSQ
result to `N̄ = N − n(N)` servers, which is why general server counts are allowed.
-/

/-- **A Halfin–Whitt sequence of JSQ(d) systems with admissible initial states** (§2.3, p. 7, and
the hypotheses of Theorem 2.4): for parameters `β`, buffer `b`, level `k` and a probability
measure `ν` on `ℝ^k`,
1. the number of servers tends to infinity, `Ns j → ∞`;
2. for all large `j`, the primitives `(Q₀ j, E j, M j)` on `(Ω j, P j)` form a JSQ(d) system with
   `Ns j` servers, `d j` samples, arrival rate `lam j` and buffer `b` (`IsJSQdSystem`);
3. the Halfin–Whitt condition `(N − λ(N))/√N → β` holds along the sequence;
4. for all large `j`, almost surely `Q_{k+1}(0) = 0`, i.e. `Q̄^N_{k+1}(0) = 0`;
5. the initial values `(Q̄_1(0), …, Q̄_k(0))` of the diffusion-scaled states converge jointly in
   distribution to `ν`: `E[g(Q̄_1(0), …, Q̄_k(0))] → ∫ g dν` for every bounded continuous
   `g : ℝ^k → ℝ`.
The coordinate `i : Fin k` of the initial vector is the paper's level `i + 1`. -/
structure IsHWSequence (β : ℝ) (b : ℕ∞) (k : ℕ) (ν : Measure (Fin k → ℝ)) (Ns d : ℕ → ℕ)
    (lam : ℕ → ℝ) {Ω : ℕ → Type} [∀ j, MeasurableSpace (Ω j)] (P : ∀ j, Measure (Ω j))
    (Q₀ : ∀ j, Ω j → ℕ → ℕ) (E : ∀ j, Ω j → ℕ → ℝ) (M : ∀ j, Ω j → ℕ → Mark) : Prop where
  servers_tendsto : Tendsto Ns atTop atTop
  system : ∀ᶠ j in atTop, IsJSQdSystem (P j) (Ns j) (d j) (lam j) b (Q₀ j) (E j) (M j)
  halfinWhitt : Tendsto (fun j => ((Ns j : ℝ) - lam j) / Real.sqrt (Ns j)) atTop (𝓝 β)
  init_top : ∀ᶠ j in atTop, ∀ᵐ ω ∂(P j), Q₀ j ω (k + 1) = 0
  init_law : IsProbabilityMeasure ν
  init_conv : ∀ g : BoundedContinuousFunction (Fin k → ℝ) ℝ,
    Tendsto (fun j => ∫ ω, g (fun i : Fin k => diffScaled (Ns j) (Q₀ j ω) ((i : ℕ) + 1)) ∂(P j))
      atTop (𝓝 (∫ x, g x ∂ν))

/-- **The processes `X j` converge weakly in `D_{ℓ¹}[0, ∞)` to the diffusion limit (2.4)**
(Theorem 2.4, pp. 7–8): there are a probability space `(Ω', P')` carrying a standard Brownian
motion `W`, an initial value `ξ ∼ ν` independent of `W`, and processes `Q̄`, `U₁` such that almost
surely `(Q̄, U₁)` solves (2.4) driven by `W` from `ξ` (`IsDiffusionLimit24`), and `X j ⟹ Q̄` in
the `ℓ¹` coupling form (`CouplingConvergesL1`). In particular `Q̄_i ≡ 0` for `i ≥ k + 1`. -/
def HasDiffusionLimit24 (β : ℝ) (k : ℕ) (ν : Measure (Fin k → ℝ)) {Ω : ℕ → Type}
    [∀ j, MeasurableSpace (Ω j)] (P : ∀ j, Measure (Ω j)) (X : ∀ j, Ω j → ℝ → ℕ → ℝ) : Prop :=
  ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : ℝ≥0 → Ω' → ℝ)
    (ξ : Ω' → Fin k → ℝ) (Qlim : Ω' → ℝ → ℕ → ℝ) (U : Ω' → ℝ → ℝ),
    IsDiffusionLimit24 P' β k ν W ξ Qlim U ∧ CouplingConvergesL1 P P' X Qlim

/-- **The diffusion limit of the ordinary JSQ policy** ([8, Theorem 2], as used on pp. 8 and 32),
for fixed `β`, `b`, `k`, `ν`: for every Halfin–Whitt sequence of systems in which every server is
sampled (`d = Ns`, which is JSQ: JSQ(d(N)) with `d(N) = N`, p. 4), with any server counts `Ns j → ∞`,
the diffusion-scaled occupancy processes converge to the diffusion limit (2.4). This is the
statement of Theorem 2.4 in the case `d(N) = N`, along an arbitrary sequence of server counts. -/
def JSQDiffusionLimitStatement (β : ℝ) (b : ℕ∞) (k : ℕ) (ν : Measure (Fin k → ℝ)) : Prop :=
  ∀ (Ns : ℕ → ℕ) (lam : ℕ → ℝ) (Ω : ℕ → Type) [∀ j, MeasurableSpace (Ω j)]
    (P : ∀ j, Measure (Ω j)) (Q₀ : ∀ j, Ω j → ℕ → ℕ) (E : ∀ j, Ω j → ℕ → ℝ)
    (M : ∀ j, Ω j → ℕ → Mark),
    IsHWSequence β b k ν Ns Ns lam P Q₀ E M →
    HasDiffusionLimit24 β k ν P (fun j ω => diffusionProcess b (Ns j) (Q₀ j ω) (E j ω) (M j ω))

end PowerOfDUniversality.Diffusion


