-- Prove2me | Definitions.Def_QFairEx_IsCPInstrument
-- name    : QFairEx_IsCPInstrument
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:03.100811+00:00
-- url     : https://prove2.me/theorems/7f547bff-c5c9-45c6-be86-700f4fe7d96c
-- title:
--   Completely positive maps, cq-instruments and classical Markov kernels
-- statement:
--   Quantum registers are finite-dimensional; a register with basis $Q$ carries density matrices in $\mathbb C^{Q\times Q}$, and a subnormalized matrix represents a branch of an experiment whose trace is the branch probability.
--
--   1. A map $\Phi:\mathbb C^{Q\times Q}\to\mathbb C^{R\times R}$ is **completely positive** if it has a finite Kraus form $\Phi(X)=\sum_{i=1}^n E_iXE_i^\dagger$.
--   2. A **classical–quantum instrument** from a classical alphabet $\mathcal X$ and register $Q$ to an alphabet $\mathcal Y$ and register $R$ is a family of maps $\Phi_{x,y}$, one branch for each classical input $x$ and classical outcome $y$, such that every branch is completely positive and, for each $x$,
--   $$\sum_{y\in\mathcal Y}\operatorname{tr}\Phi_{x,y}(\rho)=\operatorname{tr}\rho\qquad\text{for every }\rho,$$
--   the series converging.
--   3. A **Markov kernel** $w$ from $\mathcal X$ to $\mathcal Y$ has $w(x,y)\ge 0$ and $\sum_y w(x,y)=1$.
--   4. Applying an instrument to a cq-state $\rho=(\rho_x)_{x}$ (the state $\sum_x|x\rangle\langle x|\otimes\rho_x$) gives $(\Phi\rho)_y=\sum_x\Phi_{x,y}(\rho_x)$.
--
--   These are the local operations of the exchange parties (instruments) and of the purely classical trusted party (kernels) in the fair-exchange model, and the notion of a physical adversary in the BB84 guessing game.
--
--   **Formalization Note** The alphabets $\mathcal X,\mathcal Y$ are arbitrary types; there is no finiteness assumption, and sums are `tsum`s whose convergence is part of the definition (`HasSum`). In finite dimension, finite Kraus form is the same as complete positivity.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), §3.1, p.13; §4.1, pp.18–19

import Mathlib

namespace QFairEx

open Matrix

/-- **Completely positive map in finite Kraus form.**
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §3.1, p.13: "Quantum registers are finite-dimensional. We
represent their states by density operators; subnormalized states represent branches of an
experiment, with trace equal to the branch probability."

`IsCPMap Φ` holds when there are finitely many matrices `E i : Matrix R Q ℂ` with
`Φ X = ∑ i, E i * X * (E i)ᴴ` for every matrix `X`.

**Formalization Note.** Between finite-dimensional registers (bases `Q`, `R`), a linear map is
completely positive exactly when it has such a finite Kraus form (Choi), so this is the class of
all completely positive maps; no trace condition is imposed here (instrument branches are
trace-non-increasing). -/
def IsCPMap {Q R : Type} [Fintype Q] [Fintype R] (Φ : Matrix Q Q ℂ → Matrix R R ℂ) : Prop :=
  ∃ (n : ℕ) (E : Fin n → Matrix R Q ℂ), ∀ X : Matrix Q Q ℂ, Φ X = ∑ i, E i * X * (E i)ᴴ

/-- **Classical–quantum instrument** (cq-operation) from classical alphabet `X` and quantum
register `Q` to classical alphabet `Y` and quantum register `R`.
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §3.1, p.13 (CPTP maps; subnormalized branches) and §4.1,
pp.18–19 ("The exchange parties may perform quantum computation").

The data `Φ x y` is the branch taken on classical input `x` with classical output `y`. The
instrument condition: every branch is completely positive, and for each input `x` the branch
traces sum to the input trace, `∑' y, tr (Φ x y ρ) = tr ρ` (as a `HasSum`, so the series
converges).

**Formalization Note.** The classical alphabets `X`, `Y` are arbitrary types (no finiteness);
fresh randomness and measurement outcomes are recorded in `Y`. Trace preservation is asked of
every matrix `ρ`, which for maps of Kraus form is the same as asking it of density matrices. -/
def IsCPInstrument {X Y Q R : Type} [Fintype Q] [Fintype R]
    (Φ : X → Y → Matrix Q Q ℂ → Matrix R R ℂ) : Prop :=
  (∀ x y, IsCPMap (Φ x y)) ∧ ∀ (x : X) (ρ : Matrix Q Q ℂ), HasSum (fun y => (Φ x y ρ).trace) ρ.trace

/-- **Markov kernel between classical alphabets** (a purely classical randomized step).
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §4.1, p.19: "The trusted party has only classical internal state
and sends and receives only classical messages."

`w x y` is the probability of moving from `x` to `y`: nonnegative, and `∑' y, w x y = 1`
(as a `HasSum`).

**Formalization Note.** `X`, `Y` are arbitrary types; a kernel has countable support
automatically because its weights are summable. -/
def IsMarkovKernel {X Y : Type} (w : X → Y → ℝ) : Prop :=
  (∀ x y, 0 ≤ w x y) ∧ ∀ x, HasSum (w x) 1

/-- **Applying a cq-operation to a cq-state.** A (possibly subnormalized) cq-state on classical
alphabet `X` and register `Q` is `ρ : X → Matrix Q Q ℂ` (the state `∑_x |x⟩⟨x| ⊗ ρ x` of the
paper, p.24). `applyCQ Φ ρ y = ∑' x, Φ x y (ρ x)`.

**Formalization Note.** For a cq-state with summable traces and an instrument `Φ`, the series
converges, so the `tsum` is the true sum. -/
noncomputable def applyCQ {X Y Q R : Type} (Φ : X → Y → Matrix Q Q ℂ → Matrix R R ℂ)
    (ρ : X → Matrix Q Q ℂ) : Y → Matrix R R ℂ :=
  fun y => ∑' x, Φ x y (ρ x)

end QFairEx


