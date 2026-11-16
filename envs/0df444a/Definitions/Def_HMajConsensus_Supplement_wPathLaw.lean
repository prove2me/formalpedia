-- Prove2me | Definitions.Def_HMajConsensus_Supplement_wPathLaw
-- name    : HMajConsensus_Supplement_wPathLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:44:25.98521+00:00
-- url     : https://prove2.me/theorems/9779de12-e190-4671-ad7d-201eabf3dc52
-- title:
--   $h$-input rules, neutrality, $P_{\mathrm{ignore}}$-ignoring rules, the $\mathcal W$-dynamics and the event $\tau_{\mathrm{consensus}}\ge T$
-- statement:
--   Fix integers $k\ge2$ (opinions) and $h\ge1$ (samples). An **update function** maps a vertex's current opinion $c\in[k]$ and an ordered vector $z=(z_1,\dots,z_h)\in[k]^h$ of sampled opinions to a new opinion in $[k]$. Let $\mathcal L_{\mathcal W}$ be the law of a random update function $\mathcal W$. The module defines:
--
--   1. $\mathcal L_{\mathcal W}$ is an **$h$-input rule** if, for every $c\in[k]$ and $z\in[k]^h$, $\Pr[\mathcal W(c,z)\in\{c,z_1,\dots,z_h\}]=1$.
--   2. The rule is **neutral** if, for every permutation $\sigma$ of $[k]$, every $c,i\in[k]$ and every $z\in[k]^h$,
--   $$\Pr[\mathcal W(c,z)=i]=\Pr[\mathcal W(\sigma(c),\sigma z)=\sigma(i)],\qquad \sigma z=(\sigma(z_1),\dots,\sigma(z_h)).$$
--   3. For $P_{\mathrm{ignore}}\in[0,1]$, the rule is **$P_{\mathrm{ignore}}$-ignoring** if $\Pr[\mathcal W(c,x_1,\dots,x_h)=c]\ge P_{\mathrm{ignore}}$ for every input $(c,x_1,\dots,x_h)\in[k]^{h+1}$ with pairwise distinct entries.
--   4. The **$\mathcal W$-dynamics** on $n$ vertices: from a configuration $C(0)\in[k]^n$, in every round $t$ each vertex $v$ independently draws a fresh copy $\mathcal W_v(t)$ of $\mathcal W$ and, independently, samples $h$ vertices uniformly with replacement from $[n]$ (itself included), recording their opinions in $Z^{(v)}(t)$; all vertices then update simultaneously to $C_v(t+1)=\mathcal W_v(t)(C_v(t),Z^{(v)}(t))$. Given $C(t)$, the sample vector has law $p(t)^{\otimes h}$, where $p(t)$ is the opinion distribution of $C(t)$. The module defines the one-round transition kernel and the law of the whole trajectory $(C(t))_{t\ge0}$.
--   5. The event $\tau_{\mathrm{consensus}}\ge T$: no round $t<T$ is a consensus configuration.
--
--   These objects are the setting of the paper's lower bound (Theorem 8.4), which applies to every neutral $h$-input dynamics, including $h$-Majority, $h$-minority, 2-Choices and DéjàVu.
--
--   **Formalization Note** Opinions and vertices are `Fin k` and `Fin n`. The law $\mathcal L_{\mathcal W}$ is a `PMF` on the finite type `Fin k → (Fin h → Fin k) → Fin k`. "Distinct entries" means `x` injective and `c` not among the `x_j`. The one-vertex law is the image of $\mathcal L_{\mathcal W}\otimes p(C)^{\otimes h}$ under $(f,z)\mapsto f(C_v,z)$, using the published `HMajConsensus.iidSample` and `HMajConsensus.empirical`; the kernel is the product over vertices, and the path law is the published `MarkovChainCLT.chainMeasure` from $\delta_{C(0)}$. The event $\tau\ge T$ quantifies over rounds rather than using an infimum, so a path that never reaches consensus satisfies it for every $T$.
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, §8.1, pp.53-54 (Definitions 8.1, 8.2, 8.3; consensus time, p.54)

import Mathlib
import Definitions.Def_HMajConsensus_majLaw
import Definitions.Def_HMajConsensus_pathLaw
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HMajConsensus.Supplement

/-- A deterministic update function with `h` inputs: it takes a vertex's current opinion `c ∈ [k]`
and an ordered vector `z = (z₁, …, z_h) ∈ [k]^h` of sampled opinions and returns the new opinion
(d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus
Dynamics*, arXiv:2610.40562, §8.1, p.53: "functions from [k] × [k]^h to [k]").

**Formalization Note** Opinions are `Fin k`; the function is curried,
`Fin k → (Fin h → Fin k) → Fin k`. This is a finite type with the product (discrete) σ-algebra. -/
abbrev RuleFun (k h : ℕ) := Fin k → (Fin h → Fin k) → Fin k

/-- `Pr[W(c, z) = i]` for a random update function `W` with law `L`
(arXiv:2610.40562, Definition 8.1, p.54).

**Formalization Note** The law `L_W` of `W` is a `PMF` on the finite type `RuleFun k h`;
`Pr[W(c, z) = i]` is the mass at `i` of the image of `L` under `f ↦ f c z`. -/
noncomputable def selProb {k h : ℕ} (L : PMF (RuleFun k h)) (c : Fin k) (z : Fin h → Fin k)
    (i : Fin k) : ℝ≥0∞ :=
  (L.map (fun f => f c z)) i

/-- `L_W` is an **`h`-input rule** (arXiv:2610.40562, Definition 8.1, p.54): for every
`c ∈ [k]` and `z ∈ [k]^h`, `Pr[W(c, z) ∈ {c, z₁, …, z_h}] = 1`. -/
def IsHInputRule {k h : ℕ} (L : PMF (RuleFun k h)) : Prop :=
  ∀ (c : Fin k) (z : Fin h → Fin k),
    (L.map (fun f => f c z)).toOuterMeasure {x | x = c ∨ x ∈ Set.range z} = 1

/-- The rule is **neutral** (arXiv:2610.40562, Definition 8.1, p.54): for every permutation
`σ` of `[k]`, every `c, i ∈ [k]` and every `z ∈ [k]^h`,
`Pr[W(c, z) = i] = Pr[W(σ(c), σz) = σ(i)]` with `σz = (σ(z₁), …, σ(z_h))`. -/
def IsNeutral {k h : ℕ} (L : PMF (RuleFun k h)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (c i : Fin k) (z : Fin h → Fin k),
    selProb L c z i = selProb L (σ c) (σ ∘ z) (σ i)

/-- The rule is **`P_ignore`-ignoring** (arXiv:2610.40562, Definition 8.2, p.54): for every
input `(c, x₁, …, x_h) ∈ [k]^{h+1}` with distinct entries, `Pr[W(c, x₁, …, x_h) = c] ≥ P_ignore`.

**Formalization Note** "Distinct entries" is: `x` is injective and `c` is not among
`x₁, …, x_h`. The probability is in `ℝ≥0∞`, so the real parameter is compared through
`ENNReal.ofReal`; the theorems using this predicate assume `P_ignore ∈ [0, 1]`, as the
definition does. -/
def IsIgnoring {k h : ℕ} (L : PMF (RuleFun k h)) (Pignore : ℝ) : Prop :=
  ∀ (c : Fin k) (x : Fin h → Fin k), Function.Injective x → c ∉ Set.range x →
    ENNReal.ofReal Pignore ≤ selProb L c x c

/-- The law of the new opinion `C_v(t+1) = W_v(t)(C_v(t), Z^{(v)}(t))` of vertex `v` given the
current configuration `C = C(t)` (arXiv:2610.40562, Definition 8.3, p.54): `W_v(t) ∼ L_W`,
independently `Z^{(v)}(t) ∼ p(t)^{⊗h}` (h vertices sampled uniformly with replacement from
`[n]`, `v` included, and their opinions read).

**Formalization Note** The pair `(W, Z)` has law `L_W ⊗ iidSample h (empirical C)` (the
published `HMajConsensus.iidSample` and `HMajConsensus.empirical`), and the new opinion is its
image under `(f, z) ↦ f (C v) z`. The vertex `v` also witnesses `n ≥ 1`, so `p(C)` is defined. -/
noncomputable def wNodeLaw {n k h : ℕ} (L : PMF (RuleFun k h)) (C : Config n k) (v : Fin n) :
    Measure (Fin k) :=
  haveI : Nonempty (Fin n) := ⟨v⟩
  (L.toMeasure.prod (iidSample h (empirical C))).map (fun q => q.1 (C v) q.2)

instance wNodeLaw_isProbabilityMeasure {n k h : ℕ} (L : PMF (RuleFun k h)) (C : Config n k)
    (v : Fin n) : IsProbabilityMeasure (wNodeLaw L C v) := by
  have : Nonempty (Fin n) := ⟨v⟩
  unfold wNodeLaw iidSample
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- One synchronous round of the **`W`-dynamics** (arXiv:2610.40562, Definition 8.3, p.54):
conditional on `C(t)`, the vertices independently draw `(W_v(t), Z^{(v)}(t))` and all update
simultaneously.

**Formalization Note** The kernel maps `C` to the product over vertices of `wNodeLaw L C v`. -/
noncomputable def wStep {n k h : ℕ} (L : PMF (RuleFun k h)) : Kernel (Config n k) (Config n k) :=
  Kernel.ofFunOfCountable (fun C => Measure.pi (fun v : Fin n => wNodeLaw L C v))

instance wStep_isMarkovKernel {n k h : ℕ} (L : PMF (RuleFun k h)) :
    IsMarkovKernel (wStep (n := n) L) :=
  ⟨fun C => by
    change IsProbabilityMeasure (Measure.pi (fun v : Fin n => wNodeLaw L C v))
    infer_instance⟩

/-- The law of the `W`-dynamics `(C(t))_{t ≥ 0}` started from the fixed configuration
`C(0) = C₀` (arXiv:2610.40562, Definition 8.3, p.54), a measure on paths `ω : ℕ → [k]^n`,
`ω t = C(t)`.

**Formalization Note** It is the published Markov-chain path law `MarkovChainCLT.chainMeasure`
of the kernel `wStep L` from `δ_{C₀}`, exactly as `HMajConsensus.pathLaw` is for `h`-Majority. -/
noncomputable def wPathLaw {n k h : ℕ} (L : PMF (RuleFun k h)) (C₀ : Config n k) :
    Measure (ℕ → Config n k) :=
  MarkovChainCLT.chainMeasure (wStep L) (Measure.dirac C₀)

instance wPathLaw_isProbabilityMeasure {n k h : ℕ} (L : PMF (RuleFun k h)) (C₀ : Config n k) :
    IsProbabilityMeasure (wPathLaw L C₀) := by
  unfold wPathLaw
  infer_instance

/-- The event `τ_consensus ≥ T` on a path `ω`: no round `t` with `t < T` is a consensus
configuration (arXiv:2610.40562, Theorem 8.4, p.54: "the consensus time is at least T").

**Formalization Note** Stated over rounds rather than with `sInf` (which would give a path that
never reaches consensus `τ = 0`). `T` is real; a round `t ∈ ℕ` is compared after casting. -/
def ConsensusNotBefore {n k : ℕ} (T : ℝ) (ω : ℕ → Config n k) : Prop :=
  ∀ t : ℕ, (t : ℝ) < T → ¬ IsConsensus (ω t)

end HMajConsensus.Supplement


