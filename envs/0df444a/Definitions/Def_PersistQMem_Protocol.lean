-- Prove2me | Definitions.Def_PersistQMem_Protocol
-- name    : PersistQMem_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:30:52.200196+00:00
-- url     : https://prove2.me/theorems/f26eb64a-3725-4f96-9786-cedf925f8a23
-- title:
--   Persistent-memory receivers with measurable records, branch states $\omega^\rho_h$, decoder events and $\Pr_\rho(E)$
-- statement:
--   A **persistent-memory receiver** (§5.3–5.4, §6.6) with memory bound $K$, source dimension $D$ and records in a measurable space $\mathcal X$ consists of:
--
--   1. a source-independent initial memory state $\sigma_0$ on $\mathbb C^K$;
--   2. for every round $t$ and every classical history $h\in\mathcal X^t$, a complete instrument from $\mathbb C^K\otimes\mathbb C^D$ (memory and the fresh copy) to the retained memory $\mathbb C^K$, given by a reference measure $\mu_t(h,\cdot)$ on the next record, which is a measurable kernel on the product $\sigma$-algebra of histories, and jointly measurable Kraus densities $(\mathrm{Kr}_t(h,a,l))_{l}$ with completeness $\int\sum_l\mathrm{Kr}_t(h,a,l)^*\mathrm{Kr}_t(h,a,l)\,\mu_t(h,da)=I_{KD}$ for every $h$.
--
--   The reference measures on histories are $\nu_0=\delta_\emptyset$ and $\nu_{t+1}=(\nu_t\otimes\mu_t)$ pushed along $(h,a)\mapsto ha$. The **branch states** are the densities
--   $$\omega^\rho_\emptyset=\sigma_0,\qquad\omega^\rho_{ha}=\sum_l\mathrm{Kr}_t(h,a,l)\,(\omega^\rho_h\otimes\rho)\,\mathrm{Kr}_t(h,a,l)^*,$$
--   the density form of $\omega^\rho_{hx}=\Phi_{h,x}(\omega^\rho_h\otimes\rho)$. A **decision event** at depth $N$ is a measurable field of effects $0\preceq Q_h\preceq I$, $h\in\mathcal X^N$, and its probability when every copy is $\rho$ is
--   $$\Pr_\rho(E)=\int\operatorname{Tr}\big(Q_h\,\omega^\rho_h\big)\,\nu_N(dh).$$
--
--   Only $\omega\otimes\rho$ sees the source. This is the model of Theorem 2.2: arbitrary adaptive complete instruments, unlimited classical records, and a coherent memory of dimension at most $K$ kept for the whole run.
--
--   **Formalization Note** Memory is $\mathbb C^K$ on every branch: a register of dimension at most $K$ embeds into it (§6.6, p.28). A protocol is a sequence of rounds, and a run with copy cap $N$ uses rounds $0,\dots,N-1$; early stopping is idling (p.15). One record space serves all rounds (per-round spaces embed in their disjoint union); histories carry the product $\sigma$-algebra; classical seeds are records. Every measurable adaptive instrument has such a Kraus density (milestones `eq_67_68_kraus_density`, `eq_70_74_joint_density`); completeness is required for every history rather than almost every one, which changes the densities on a null set only. Finite records (§5.4) are a finite record space with counting reference measure. The Kraus index is a finite type. Integrals are Bochner integrals of real parts of traces.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §5.3, pp.14–15 (PDF pp.17–18); §5.4, p.15 (PDF p.18); §6.6, (68), (70)–(75), pp.27–28 (PDF pp.30–31)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped Matrix ComplexOrder Kronecker
open MeasureTheory ProbabilityTheory

namespace PersistQMem

/-- **The persistent-memory receiver (§5.3–5.4, pp.14–15; §6.6, pp.27–28).** A receiver with a
retained quantum memory `C^K`, records in a measurable space `X`, and source copies on `C^D`
(Tao, Shen, *Structural Lower Bounds for Quantum Property Estimation with Persistent Memory*,
STOC 2027 submission, manuscript of 2026-11-03, sha256 6d48ad24…, §5.3, pp.14–15; §5.4, p.15;
§6.6, (68), (71)–(74), pp.27–28).

* `sigma0` is the source-independent initial memory state `σ_0`.
* In round `t` (`t = 0, 1, …`), conditioned on the classical history `h ∈ X^t`, the receiver
  applies a complete instrument from `C^K ⊗ C^D` (memory ⊗ fresh copy) to the retained memory
  `C^K`, given by a reference measure `μ_t(h)` on the next record and a Kraus density
  `a ↦ (Kr_t(h, a, l))_{l ∈ L}`: outcome `a ∈ S` occurs with the CP map
  `Z ↦ ∫_S Σ_l Kr_t(h,a,l) Z Kr_t(h,a,l)* dμ_t(h)(a)`.
* `Kr_measurable`: every entry is jointly measurable in `(h, a)` (product σ-algebras).
* `complete_integrable`, `complete`: completeness `∫ Σ_l Kr* Kr dμ_t(h) = I_{KD}` for every history
  `h`, entrywise, with integrable entries.

**Formalization Note.** Memory is `Fin K` on every branch: a register of dimension `≤ K` embeds in
`C^K` (§6.6, p.28, "we embed all memory registers into C^K"). A run with copy cap `N` uses
rounds `0, …, N − 1`; stopping early is idling (p.15). One record space `X` serves all rounds
(per-round spaces embed in their disjoint union); histories `Fin t → X` carry the product
σ-algebra. Classical seeds are part of the records. Finite records (§5.4) are `Fintype X` with
counting measure. `L` is a finite Kraus index (the paper's `l ∈ {1, …, Kd}`, (68), (74)). -/
structure Protocol (X : Type) [MeasurableSpace X] (L : Type) [Fintype L] (K D : ℕ) where
  sigma0 : Matrix (Fin K) (Fin K) ℂ
  sigma0_density : WildeQIT.IsDensityOperator sigma0
  μ : (t : ℕ) → Kernel (Fin t → X) X
  μ_sfinite : ∀ t, IsSFiniteKernel (μ t)
  Kr : (t : ℕ) → (Fin t → X) → X → L → Matrix (Fin K) (Fin K × Fin D) ℂ
  Kr_measurable : ∀ t l o c, Measurable fun q : (Fin t → X) × X => Kr t q.1 q.2 l o c
  complete_integrable : ∀ t (h : Fin t → X) (c c' : Fin K × Fin D),
    Integrable (fun a => (∑ l, (Kr t h a l)ᴴ * Kr t h a l) c c') (μ t h)
  complete : ∀ t (h : Fin t → X) (c c' : Fin K × Fin D),
    ∫ a, (∑ l, (Kr t h a l)ᴴ * Kr t h a l) c c' ∂(μ t h) = (1 : Matrix (Fin K × Fin D) _ ℂ) c c'

variable {X : Type} [MeasurableSpace X] {L : Type} [Fintype L] {K D : ℕ}

/-- The reference measure `ν_t` on histories `X^t` ((74), p.28): `ν_0` is the point mass on the
empty history and `ν_{t+1} = (ν_t ⊗ μ_t)` pushed along `(h, a) ↦ h a` (append the new record). -/
noncomputable def refMeasure (P : Protocol X L K D) : (t : ℕ) → Measure (Fin t → X)
  | 0 => Measure.dirac (fun i => Fin.elim0 i)
  | t + 1 => ((refMeasure P t) ⊗ₘ (P.μ t)).map
      (fun q : (Fin t → X) × X => (Fin.snoc q.1 q.2 : Fin (t + 1) → X))

/-- The branch states `ω^ρ_h` of §5.4, p.15, as densities with respect to `ν_t`:
`ω^ρ_∅ = σ_0`, `ω^ρ_{ha} = Σ_l Kr_t(h,a,l) (ω^ρ_h ⊗ ρ) Kr_t(h,a,l)*` (the density form of
`ω^ρ_{hx} = Φ_{h,x}(ω^ρ_h ⊗ ρ)`, (68), (73)–(74)). The source `ρ` enters only through `ω ⊗ ρ`. -/
noncomputable def branch (P : Protocol X L K D) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    (t : ℕ) → (Fin t → X) → Matrix (Fin K) (Fin K) ℂ
  | 0, _ => P.sigma0
  | t + 1, h => ∑ l, P.Kr t (Fin.init h) (h (Fin.last t)) l *
      (branch P ρ t (Fin.init h) ⊗ₖ ρ) * (P.Kr t (Fin.init h) (h (Fin.last t)) l)ᴴ

/-- **A decision event `E` at depth `N`** (§5.4, p.15): terminal effects `0 ⪯ Q_h ⪯ I` on the
memory for every history `h ∈ X^N`, entrywise measurable in `h`. The final quantum measurement and
classical computation of the receiver produce such a field. -/
structure DecoderEvent (X : Type) [MeasurableSpace X] (K N : ℕ) where
  Q : (Fin N → X) → Matrix (Fin K) (Fin K) ℂ
  measurable : ∀ o o', Measurable fun h => Q h o o'
  effect : ∀ h, (Q h).PosSemidef ∧ (1 - Q h).PosSemidef

/-- The success probability `Pr_ρ(E) = Σ_{|h| = N} Tr(Q_h ω^ρ_h)` of §5.4, p.15, in its measurable
form `∫ Tr(Q(h) ω^ρ_N(h)) dν_N(h)` (§6.6, pp.27–28), when every copy is `ρ`. -/
noncomputable def prob {N : ℕ} (P : Protocol X L K D) (E : DecoderEvent X K N)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  ∫ h, (E.Q h * branch P ρ N h).trace.re ∂(refMeasure P N)

end PersistQMem


