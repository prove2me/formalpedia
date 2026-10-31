-- Prove2me | Definitions.Def_MarkovCLTRate_GeneralChain
-- name    : MarkovCLTRate_GeneralChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:47.62269+00:00
-- url     : https://prove2.me/theorems/d962b96d-ae0e-41da-b15b-58b0c689e9dc
-- title:
--   General state-space Markov chains: $\psi$-irreducibility, aperiodicity, petite sets and the geometric drift condition (8)
-- statement:
--   Let $P$ be a transition kernel on a measurable state space $\mathcal S$ and $P^n$ its $n$-step kernel. The terminology of Theorem 3 is that of Meyn and Tweedie (2012):
--
--   1. A nonzero measure $\varphi$ is an **irreducibility measure** if every measurable $A$ with $\varphi(A)>0$ satisfies: for every $x$ there is $n\ge1$ with $P^n(x,A)>0$. A **maximal** irreducibility measure $\psi$ is one with $\varphi\ll\psi$ for every irreducibility measure $\varphi$; the chain is **$\psi$-irreducible** if one exists.
--   2. A **$d$-cycle** is a family of disjoint measurable sets $D_0,\dots,D_{d-1}$ of positive $\psi$-measure with $P(x,D_{i+1\bmod d})=1$ for $x\in D_i$ and $\psi\big((\cup_iD_i)^c\big)=0$. The chain is **aperiodic** if there is no $d$-cycle with $d\ge2$.
--   3. A measurable set $C$ is **petite** if there are a probability distribution $a$ on $\{0,1,2,\dots\}$ and a nonzero measure $\nu$ with $\sum_n a(n)P^n(x,B)\ge\nu(B)$ for all $x\in C$ and measurable $B$. A function $\mathcal V$ is **unbounded off petite sets** if every sublevel set $\{\mathcal V\le c\}$ is petite.
--
--   The standing assumptions of Theorem 3 are: $X$ is $\psi$-irreducible and aperiodic with invariant distribution $\pi$ and initial distribution $\eta$; $\mathcal V\ge1$ is unbounded off petite sets, $E[\mathcal V(X_0)]<\infty$, and the **geometric drift condition**
--   $$
--   P\mathcal V(x)=E[\mathcal V(X_{k+1})\mid X_k=x]\le\lambda\mathcal V(x)+L\qquad(8)
--   $$
--   holds for some $\lambda\in[0,1)$ and $L<\infty$.
--
--   **Formalization Note** These definitions are not printed in the paper, which borrows them from Meyn and Tweedie (2012, Chapters 4, 5 and 8); they are written here from that book's definitions. Meyn and Tweedie phrase reachability as $P_x(\tau_A<\infty)>0$, equivalent to $P^n(x,A)>0$ for some $n\ge1$. The zero measure is excluded in both places where a measure is asked for: otherwise every chain would be irreducible and every set petite. Aperiodicity is required for every maximal irreducibility measure (they are all equivalent). $\mathcal V$ is real valued and measurable, and $P\mathcal V(x)$ and $E[\mathcal V(X_0)]$ are lower Lebesgue integrals, so (8) cannot hold through an integral defaulting to $0$.
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, Theorem 3 and (8), p.17 (terminology borrowed from Meyn and Tweedie 2012, Markov Chains and Stochastic Stability, Ch. 4–5, 8)

import Mathlib
import Definitions.Def_MarkovIterKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovCLTRate

variable {S : Type*} [MeasurableSpace S]

/-- `φ` is an irreducibility measure for the transition kernel `P` (Meyn and Tweedie 2012, §4.2,
the vocabulary arXiv:2401.15719v5 borrows on p.17): `φ` is a nonzero measure and every measurable
set `A` with `φ(A) > 0` is reached from every starting point, i.e. `Pⁿ(x, A) > 0` for some
`n ≥ 1`.

**Formalization Note.** Meyn–Tweedie phrase the reachability as `L(x, A) = P_x(τ_A < ∞) > 0`, which
is equivalent to `Pⁿ(x, A) > 0` for some `n ≥ 1`. The zero measure is excluded: with it every chain
would be irreducible. -/
def IsIrreducibilityMeasure (P : Kernel S S) (φ : Measure S) : Prop :=
  φ ≠ 0 ∧ ∀ A : Set S, MeasurableSet A → 0 < φ A →
    ∀ x, ∃ n, 1 ≤ n ∧ 0 < MarkovChainCLT.iterKernel P n x A

/-- `ψ` is a maximal irreducibility measure (Meyn and Tweedie 2012, Prop. 4.2.2): it is an
irreducibility measure and every irreducibility measure is absolutely continuous with respect
to it. -/
def IsMaxIrreducibilityMeasure (P : Kernel S S) (ψ : Measure S) : Prop :=
  IsIrreducibilityMeasure P ψ ∧ ∀ φ, IsIrreducibilityMeasure P φ → φ ≪ ψ

/-- The chain with kernel `P` is `ψ`-irreducible: it has a maximal irreducibility measure
(arXiv:2401.15719v5, Theorem 3, p.17; Meyn and Tweedie 2012, §4.2). -/
def PsiIrreducible (P : Kernel S S) : Prop :=
  ∃ ψ, IsMaxIrreducibilityMeasure P ψ

/-- A `d`-cycle for `P` relative to `ψ` (Meyn and Tweedie 2012, Theorem 5.4.4): pairwise disjoint
measurable sets `D_0, …, D_{d−1}` of positive `ψ`-measure such that `P(x, D_{i+1 mod d}) = 1` for
every `x ∈ D_i`, and whose union has `ψ`-null complement. -/
def IsCycle (P : Kernel S S) (ψ : Measure S) (d : ℕ) (D : Fin d → Set S) : Prop :=
  (∀ i, MeasurableSet (D i)) ∧ Pairwise (fun i j => Disjoint (D i) (D j)) ∧
    (∀ i, 0 < ψ (D i)) ∧ (∀ i, ∀ x ∈ D i, P x (D (finRotate d i)) = 1) ∧
    ψ (⋃ i, D i)ᶜ = 0

/-- The chain is aperiodic (Meyn and Tweedie 2012, §5.4; arXiv:2401.15719v5, Theorem 3, p.17): for
a maximal irreducibility measure `ψ` there is no `d`-cycle with `d ≥ 2`, i.e. the period is `1`.

**Formalization Note.** Stated for every maximal irreducibility measure; all of them are
equivalent, so they have the same cycles. Used together with `PsiIrreducible`. -/
def Aperiodic (P : Kernel S S) : Prop :=
  ∀ ψ, IsMaxIrreducibilityMeasure P ψ → ∀ d, 2 ≤ d → ∀ D : Fin d → Set S, ¬ IsCycle P ψ d D

/-- `C` is a petite set (Meyn and Tweedie 2012, §5.5.2): there are a probability distribution
`a` on `{0, 1, 2, …}` and a nonzero measure `ν` with
`Σ_n a(n) Pⁿ(x, B) ≥ ν(B)` for every `x ∈ C` and every measurable `B`.

**Formalization Note.** `ν ≠ 0` is required: with `ν = 0` every set would be petite. -/
def IsPetite (P : Kernel S S) (C : Set S) : Prop :=
  MeasurableSet C ∧ ∃ (a : ℕ → ℝ≥0∞) (ν : Measure S), (∑' n, a n) = 1 ∧ ν ≠ 0 ∧
    ∀ x ∈ C, ∀ B : Set S, MeasurableSet B →
      ν B ≤ ∑' n, a n * MarkovChainCLT.iterKernel P n x B

/-- The function `𝒱` is unbounded off petite sets (Meyn and Tweedie 2012, §8.4.2): every sublevel
set `{x : 𝒱(x) ≤ c}` is petite. -/
def UnboundedOffPetite (P : Kernel S S) (lyap : S → ℝ) : Prop :=
  ∀ c : ℝ, IsPetite P {x | lyap x ≤ c}

/-- The standing assumptions of Theorem 3, arXiv:2401.15719v5, p.17: `X` is a `ψ`-irreducible,
aperiodic Markov chain on `S` with transition kernel `P` and invariant distribution `π`; the initial
distribution is `η`; the Lyapunov function `𝒱 = lyap ≥ 1` is unbounded off petite sets,
`E[𝒱(X_0)] < ∞`, and the drift condition (8)
`P𝒱(x) = E[𝒱(X_{k+1}) | X_k = x] ≤ λ𝒱(x) + L` holds for some `λ ∈ [0, 1)` and `L < ∞`.

**Formalization Note.** `𝒱` is real valued and measurable. `P𝒱(x)` and `E[𝒱(X_0)]` are lower
Lebesgue integrals, so (8) and `E[𝒱(X_0)] < ∞` are not vacuous when `𝒱` fails to be integrable. -/
structure GeoDriftChain (P : Kernel S S) (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ) :
    Prop where
  isProb_pi : IsProbabilityMeasure π
  isProb_eta : IsProbabilityMeasure η
  invariant : P.Invariant π
  psiIrreducible : PsiIrreducible P
  aperiodic : Aperiodic P
  measurable_lyap : Measurable lyap
  one_le_lyap : ∀ x, 1 ≤ lyap x
  unboundedOffPetite : UnboundedOffPetite P lyap
  lam_nonneg : 0 ≤ lam
  lam_lt_one : lam < 1
  drift : ∀ x, ∫⁻ y, ENNReal.ofReal (lyap y) ∂(P x) ≤ ENNReal.ofReal (lam * lyap x + L)
  init : ∫⁻ x, ENNReal.ofReal (lyap x) ∂η < ∞

end MarkovCLTRate


