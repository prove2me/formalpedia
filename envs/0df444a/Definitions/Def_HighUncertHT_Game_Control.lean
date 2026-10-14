-- Prove2me | Definitions.Def_HighUncertHT_Game_Control
-- name    : HighUncertHT_Game_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:06.213474+00:00
-- url     : https://prove2.me/theorems/b78d953e-b99b-46e3-9035-f0b23688b47e
-- title:
--   (4)–(8), pp. 6–8 — adversary controls 𝒜ⁿ in feedback form, the cost Cⁿ and the game value Vⁿ
-- statement:
--   At each arrival epoch $k/n$ the adversary first chooses, for each type $\ell$, a distribution $\pi^{\ell n}_k\in\Pi^{\ell n}$, based only on the past job sizes $J^n_1,\dots,J^n_{k-1}$ (5); then the job sizes $J^n_k=(J^{\ell n}_k)_\ell$ are drawn, conditionally on the past, from the product law $\bigotimes_\ell\pi^{\ell n}_k$ (7). An **admissible control** $a^n\in\mathcal A^n$ is encoded by its feedback map
--   $$
--   (J^n_1,\dots,J^n_{k-1})\mapsto(\pi^{\ell n}_k)_\ell
--   $$
--   together with the measurable kernel it induces; its law on job-size sequences is the Ionescu–Tulcea law of these kernels, and $a^n(\omega)=(\pi^n_k,J^n_k)_{k\ge1}$ is its sample path.
--
--   For a strategy $\beta^n$ the effort process is $B^n=\beta^n(a^n)$ (8), and the cost is
--   $$
--   C^n(\beta^n(a^n),a^n)=\mathbb E\Big[\int_0^\infty e^{-t}\,h\cdot\hat Q^n_t\,dt\Big].
--   $$
--   The **value of the $n$-th game** is
--   $$
--   V^n=\inf_{\beta^n\in\mathbb B^n}\ \sup_{a^n\in\mathcal A^n}\ C^n(\beta^n(a^n),a^n).
--   $$
--
--   **Formalization Note** By (5) and the Doob–Dynkin lemma each $\pi^n_k$ is a measurable function of the past job sizes, and by (7) the conditional law of $J^n_k$ is the product of the chosen distributions; hence the law of the control path, and with it the cost, is determined by the feedback maps, and every such family of maps is realized by a control on some probability space. This is why $\mathcal A^n$ is encoded in feedback form. The job-size sequence has a dummy coordinate $0$ (point mass at $0$). Costs and values are in $[0,\infty]$; the expectation is a lower Lebesgue integral.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, pp. 6–8, (4), (5), (6), (7), (8), definition of 𝒜ⁿ (p. 6), Game's value (p. 8)

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy

namespace HighUncertHT.Game

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-!
Atar, Castiel, Shadmi, arXiv:2204.05733v1, §2.1.2, pp. 6–8, (4)–(8): admissible controls of the
adversary `𝒜ⁿ`, the cost `Cⁿ` and the value `Vⁿ = inf_{βⁿ ∈ 𝔹ⁿ} sup_{aⁿ ∈ 𝒜ⁿ} Cⁿ(βⁿ(aⁿ), aⁿ)`.

**Encoding of `𝒜ⁿ`.** By (5) the adversary's choice `πⁿ_k` is `σ(Jⁿ₁, …, Jⁿ_{k-1})`-measurable, so
(Doob–Dynkin; `Πⁿ` is a Borel subset of a standard Borel space) it is a measurable function of the
past job sizes, and by (7) the conditional law of `Jⁿ_k` given the past is the product
`⊗_ℓ π^{ℓn}_k`. The law of the job-size sequence is therefore the Ionescu–Tulcea law of these
kernels, and every quantity of the paper (the cost in particular) depends on `aⁿ` only through
that law. An admissible control is encoded as its feedback map together with the (measurable)
kernel it induces; its law is `ProbabilityTheory.Kernel.trajMeasure` on job-size sequences
`ω : ℕ → (Fin L → ℝ)`, where `ω 0` is a dummy coordinate (the point mass at `0`) and `ω k`,
`k ≥ 1`, is the paper's `Jⁿ_k`.
-/

variable {L : ℕ}

/-- An **admissible control of the adversary** for the `n`-th system, `aⁿ ∈ 𝒜ⁿ` (p. 6), in
feedback form.

* `policy m x ℓ` is the distribution `π^{ℓn}_{m+1} ∈ Π^{ℓn}` chosen for the `(m+1)`-st type-`ℓ`
  job, as a function of the history `x = (ω 0, Jⁿ₁, …, Jⁿ_m)` (coordinate `0` is the dummy);
* `kernel m` is the Markov kernel `x ↦ ⊗_ℓ policy m x ℓ` giving the conditional law (7) of
  `Jⁿ_{m+1}`; being a kernel, it is measurable in the history, which is the measurability (5) of
  the choice. -/
structure AdversaryControl (S : Setting L) (n : ℕ) where
  policy : (m : ℕ) → ((i : Finset.Iic m) → (Fin L → ℝ)) → Fin L → ProbabilityMeasure ℝ
  policy_mem : ∀ m x ℓ, policy m x ℓ ∈ S.cls n ℓ
  kernel : (m : ℕ) → Kernel ((i : Finset.Iic m) → (Fin L → ℝ)) (Fin L → ℝ)
  kernel_eq : ∀ m x, kernel m x = Measure.pi (fun ℓ => (policy m x ℓ : Measure ℝ))

namespace AdversaryControl

variable {S : Setting L} {n : ℕ}

instance isMarkovKernel (f : AdversaryControl S n) (m : ℕ) : IsMarkovKernel (f.kernel m) :=
  ⟨fun x => by rw [f.kernel_eq]; infer_instance⟩

/-- The law of the job-size sequence `ω = (ω 0, Jⁿ₁, Jⁿ₂, …)` under the control `f`
(Ionescu–Tulcea), started from the dummy point mass `ω 0 = 0`. -/
noncomputable def law (f : AdversaryControl S n) : Measure (ℕ → Fin L → ℝ) :=
  Kernel.trajMeasure (X := fun _ => Fin L → ℝ) (Measure.dirac 0) f.kernel

/-- The sample path `aⁿ(ω) = (πⁿ_k, Jⁿ_k)_{k ≥ 1}` of the control, in the 0-based convention of
`ControlPath`: entry `i` is `(π_{i+1}, J_{i+1})` with `π_{i+1} = policy i (ω|_{[0, i]})`. -/
def ctrlPath (f : AdversaryControl S n) (ω : ℕ → Fin L → ℝ) : ControlPath L :=
  fun i => (fun ℓ => f.policy i (Preorder.frestrictLe i ω) ℓ, ω (i + 1))

end AdversaryControl

/-- The cost `Cⁿ(βⁿ(aⁿ), aⁿ) = 𝔼[∫₀^∞ e^{-t} h · Q̂ⁿ_t dt]` ((4), p. 6, and p. 8) of the strategy
`β` against the control `f`, where `Bⁿ = βⁿ(aⁿ)` (8). An expectation of a nonnegative quantity,
computed as a lower Lebesgue integral in `[0, ∞]`. -/
noncomputable def cost (S : Setting L) (n : ℕ) (β : ControlPath L → EffortPath L)
    (f : AdversaryControl S n) : ℝ≥0∞ :=
  ∫⁻ ω, pathCost S n (f.ctrlPath ω) (β (f.ctrlPath ω)) ∂f.law

/-- The value of the `n`-th game, `Vⁿ = inf_{βⁿ ∈ 𝔹ⁿ} sup_{aⁿ ∈ 𝒜ⁿ} Cⁿ(βⁿ(aⁿ), aⁿ)` (p. 8), in
`[0, ∞]`. -/
noncomputable def value (S : Setting L) (n : ℕ) : ℝ≥0∞ :=
  ⨅ β ∈ admissibleStrategies S n, ⨆ f : AdversaryControl S n, cost S n β f

end HighUncertHT.Game


