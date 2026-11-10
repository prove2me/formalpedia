-- Prove2me | Definitions.Def_HiddenHardCoreColoring_Mixing_Chain
-- name    : HiddenHardCoreColoring_Mixing_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:58:37.933195+00:00
-- url     : https://prove2.me/theorems/60a5a7aa-c671-41b0-aaf8-e328d2faae77
-- title:
--   Finite reversible chains: second eigenvalue with multiplicity, total variation, mixing time
-- statement:
--   This file fixes the Markov-chain vocabulary of §3.1 (p.6) for a chain with transition matrix $P$ on a finite state space $\Omega$, acting on functions by $(Pf)(\sigma)=\sum_\tau P(\sigma,\tau)f(\tau)$.
--
--   1. **Second eigenvalue and spectral gap.** For a chain reversible with respect to a full-support law, list the eigenvalues with multiplicity as $1=\lambda_1(P)\ge\lambda_2(P)\ge\cdots$, and set
--   $$\operatorname{gap}(P):=1-\lambda_2(P).$$
--   Thus $\lambda_2(P)=1$ when the eigenvalue $1$ has multiplicity at least two, and otherwise $\lambda_2(P)$ is the largest eigenvalue different from $1$.
--   2. **Total variation and mixing time.** $d_{TV}(\nu,\mu):=\tfrac12\sum_\sigma|\nu(\sigma)-\mu(\sigma)|$, and for $\varepsilon\in(0,1)$
--   $$t_{\mathrm{mix}}(P,\varepsilon):=\min\Big\{t\ge0:\ \max_{\sigma\in\Omega}d_{TV}\big(P^t(\sigma,\cdot),\mu\big)\le\varepsilon\Big\}.$$
--   3. $\mu_{\min}:=\min_\sigma\mu(\sigma)$, and *reversible with full support* means: $P$ is a transition matrix, $\mu(\sigma)>0$, $\sum_\sigma\mu(\sigma)=1$ and $\mu(\sigma)P(\sigma,\tau)=\mu(\tau)P(\tau,\sigma)$.
--
--   These notions are used for the coloring chain in Theorem 1 and Lemma 4, for the hard-core chains in Theorem 5, and for a general chain in Lemma 2.
--
--   **Formalization Note** Eigenvalues are real numbers with a real eigenvector (`MarkovMixing.IsEigenvalue`); the multiplicity of $1$ is the dimension of the kernel of $P-\mathrm{Id}$. On a one-point state space the second eigenvalue does not exist and the definition gives $\operatorname{gap}=1$. `tmix` is the natural-number infimum of the successful times; every statement that bounds it also asserts that a successful time exists.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; §3.1, p.6 (eigenvalues with multiplicity, gap(P), d_TV, t_mix(P, ε)); Lemma 2, p.6 (µ_min)

import Mathlib
import Definitions.Def_mm_spectral

namespace HiddenHardCoreColoring.Mixing

open Finset

noncomputable section

/-!
# Finite reversible chains: second eigenvalue with multiplicity, total variation, mixing time

Xiongxin Yang, *Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via
Hidden Hard-Core Models*, STOC 2027 submission #964 (October 2026), §3.1, p.6.

A chain on a finite state space `S` is a matrix `P : Matrix S S ℝ` acting on functions by
`(P f)(σ) = ∑_τ P(σ,τ) f(τ)` (`P *ᵥ f`); `P ^ t` is the `t`-step kernel.
-/

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The second eigenvalue `λ₂(P)`, counted with multiplicity** (§3.1, p.6: "We list its
eigenvalues with multiplicity as `1 = λ₁(P) ≥ λ₂(P) ≥ ⋯ ≥ λ_{|Ω|}(P) ≥ −1`").

For a chain that is reversible with respect to a full-support law, every eigenvalue is real and at
most `1`, `1` is an eigenvalue (constants), and multiplicities are the dimensions of the eigenspaces.
Hence `λ₂(P) = 1` when the eigenspace of `1` has dimension at least `2`, and otherwise `λ₂(P)` is the
largest eigenvalue different from `1` (the published `MarkovMixing.lambdaTwo`, a supremum over the
finite set of real eigenvalues `≠ 1`).

**Formalization Note** On a one-point state space there is no second eigenvalue; the definition then
returns `MarkovMixing.lambdaTwo P = sSup ∅ = 0`, so `gap P = 1`. -/
def lambdaTwo (P : Matrix S S ℝ) : ℝ :=
  if 2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (P - 1))) then 1
  else MarkovMixing.lambdaTwo P

/-- **The spectral gap** `gap(P) := 1 − λ₂(P)` (§3.1, p.6), with `λ₂` counted with multiplicity. -/
def gap (P : Matrix S S ℝ) : ℝ := 1 - lambdaTwo P

/-- **Total variation distance** `d_TV(ν, μ) := ½ ∑_σ |ν(σ) − μ(σ)|` (§3.1, p.6). -/
def dTV (ν μ : S → ℝ) : ℝ := (1 / 2) * ∑ s, |ν s - μ s|

/-- `MixedAt P μ ε t`: after `t` steps, the chain is within total variation `ε` of `μ` from every
start, i.e. `max_{σ∈Ω} d_TV(P^t(σ,·), μ) ≤ ε`. -/
def MixedAt (P : Matrix S S ℝ) (μ : S → ℝ) (ε : ℝ) (t : ℕ) : Prop :=
  ∀ s : S, dTV (fun s' => (P ^ t) s s') μ ≤ ε

/-- **The mixing time** `t_mix(P, ε) := min {t ≥ 0 : max_σ d_TV(P^t(σ,·), μ) ≤ ε}` (§3.1, p.6).

**Formalization Note** This is the natural-number infimum of the successful times. It is the
minimum only when some time succeeds; every statement of the mission that bounds `tmix` also
asserts that a successful time exists, so the value `sInf ∅ = 0` is never used. -/
def tmix (P : Matrix S S ℝ) (μ : S → ℝ) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | MixedAt P μ ε t}

/-- `μ_min := min_{σ∈Ω} μ(σ)` (Lemma 2, p.6). On a nonempty finite state space this real infimum
is the minimum. -/
def muMin (μ : S → ℝ) : ℝ := ⨅ s : S, μ s

/-- `P` is **reversible** with respect to `μ` and `μ` has full support (§3.1, p.6: "reversible with
respect to a distribution `µ` on a finite state space `Ω` with `µ(σ) > 0` for every `σ ∈ Ω`"):
`P` is a transition matrix, `μ` is a probability vector with positive entries, and detailed balance
`μ(σ)P(σ,τ) = μ(τ)P(τ,σ)` holds. -/
structure IsReversibleFullSupport (P : Matrix S S ℝ) (μ : S → ℝ) : Prop where
  stochastic : MarkovMixing.IsStochastic P
  pos : ∀ s, 0 < μ s
  sum_one : ∑ s, μ s = 1
  balance : MarkovMixing.DetailedBalance P μ

end

end HiddenHardCoreColoring.Mixing


