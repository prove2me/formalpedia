-- Prove2me | Definitions.Def_QMAvsQCIP_CSIncompressible
-- name    : QMAvsQCIP_CSIncompressible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:48:49.036345+00:00
-- url     : https://prove2.me/theorems/24229ef5-5f07-4ad9-a164-0265b2c758f3
-- title:
--   Contractive simultaneous incompressibility
-- statement:
--   Let $F_\lambda\subseteq X_\lambda$ be a family of random sets, $X_\lambda$ finite. The family satisfies **contractive simultaneous incompressibility** if for every polynomially bounded integer-valued $s(\lambda)\ge0$ and all sufficiently large $\lambda$, every oracle-free classical decoder $\mathrm{Dec}$ satisfies
--   $$
--   \Pr_{F_\lambda,R}\Big[\exists m\in\{0,1\}^s:\ \mathrm{Dec}(m,R)\in\binom{F_\lambda}{t_{\mathrm{inc}}(\lambda,s)}\Big]\le\varepsilon_{\mathrm{inc}}(\lambda), \tag{8}
--   $$
--   where the shared random tape $R$ is independent of $F_\lambda$. The decoder may use unrestricted local computation and a description depending on $\lambda$.
--
--   The event covers every message at once, so the bound holds simultaneously for all encoders that see $(F_\lambda,R)$ and send $s$ bits.
--
--   **Formalization Note** The random set is a function of a sample from a finite sample space with given weights (every distribution on finite sets has this form). The tape is a probability space $(\Omega,\mu)$, and each output event of the decoder is measurable in the tape (the standing convention that an algorithm's output is a random variable). "$\mathrm{Dec}(m,R)$ is a $t$-subset of $F$" is $\mathrm{Dec}(m,R)\subseteq F$ with $|\mathrm{Dec}(m,R)|=t$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 7, Eq. (8), p.19

import Definitions.Def_QMAvsQCIP_epsInc
import Definitions.Def_QMAvsQCIP_tInc

set_option autoImplicit false

namespace QMAvsQCIP

open MeasureTheory

/-- **Contractive simultaneous incompressibility** (Definition 7) of a family of random sets
`F_λ ⊆ X_λ` (`X_λ` finite). The random set is given as a function `F λ : S λ → Finset (X λ)` of a
sample `σ` from a finite sample space `S λ` with weights `w λ σ` (any distribution on finite sets
is of this form). The family is incompressible if for every polynomially bounded `s : ℕ → ℕ`
there is `λ₀` such that for every `λ ≥ λ₀`, every probability space `(Ω, μ)` (the shared random
tape `R`, independent of `F_λ`) and every decoder `Dec : {0,1}^s × Ω → Finset X_λ` whose outputs
are measurable in the tape,
`Pr_{F_λ, R}[∃ m ∈ {0,1}^s : Dec(m, R) ∈ (F_λ choose t_inc(λ, s))] ≤ ε_inc(λ)`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 7, p.19 (PDF p.22): "A family of random sets F_λ ⊆ X_λ, with
X_λ finite, satisfies contractive simultaneous incompressibility if, for every polynomially
bounded integer-valued s(λ) ≥ 0 and all sufficiently large λ, every oracle-free classical
decoder Dec satisfies Pr_{F_λ,R}[∃m ∈ {0,1}^s : Dec(m, R) ∈ (F_λ choose t_inc(λ, s))] ≤ ε_inc(λ),
(8) where the shared random tape R is independent of F_λ. The decoder may use unrestricted local
computation and a finite description of arbitrary length depending on λ."

**Formalization Note.** "`Dec(m, R)` is a `t`-element subset of `F_λ`" is
`Dec m ω ⊆ F ∧ (Dec m ω).card = t`. The joint probability is
`∑_σ w(σ) · μ{ω | event(σ, ω)}`, the product of the two laws. Measurability of each output event
`{ω | Dec m ω = T}` is the standing convention that an algorithm's output is a random variable
of its tape; it is needed for the averaging over the tape to be meaningful. -/
def CSIncompressible (X S : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Fintype (S n)] (w : ∀ n, S n → ℝ) (F : ∀ n, S n → Finset (X n)) : Prop :=
  ∀ s : ℕ → ℕ, (∃ p : Polynomial ℕ, ∀ n, s n ≤ p.eval n) →
    ∃ lam₀ : ℕ, ∀ lam, lam₀ ≤ lam →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Dec : (Fin (s lam) → Bool) → Ω → Finset (X lam)),
        (∀ m T, MeasurableSet {ω | Dec m ω = T}) →
        ∑ σ : S lam, w lam σ *
            (μ {ω | ∃ m, Dec m ω ⊆ F lam σ ∧ (Dec m ω).card = tInc lam (s lam)}).toReal
          ≤ epsInc lam

end QMAvsQCIP


