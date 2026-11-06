-- Prove2me | Definitions.Def_HMajConsensus_pathLaw
-- name    : HMajConsensus_pathLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:54.184405+00:00
-- url     : https://prove2.me/theorems/72daac3c-b938-4768-86bc-43a0ac875db9
-- title:
--   Configurations, densities $p_i$, $p_{\max}$, the $h$-Majority kernel, its path law and the event $\tau_{\mathrm{consensus}}\le x$
-- statement:
--   There are $n$ nodes and $k$ opinions. A **configuration** $C\in[k]^n$ assigns an opinion $C_v$ to each node $v$. The **density** of opinion $i$ is
--   $$p_i(C)=\frac{|\{v\in[n]:C_v=i\}|}{n},$$
--   and $p_{\max}(C)=\max_{i\in[k]}p_i(C)$. The **empirical distribution** $p(C)=(p_i(C))_{i\in[k]}$ is the law of the opinion of a node chosen uniformly at random.
--
--   One round of **$h$-Majority** maps $C(t)$ to $C(t+1)$: independently for every node $u$, draw $X^{(u)}\sim\mathrm{Multinomial}(h;p(C(t)))$ and set $C_u(t+1)=\mathrm{Maj}(X^{(u)})$, ties broken uniformly at random; all nodes update simultaneously with fresh randomness. This is a Markov transition kernel on $[k]^n$, and the module defines the law of the process $(C(t))_{t\ge0}$ started from a fixed initial configuration $C(0)=C_0$, a probability measure on paths $\omega:\mathbb N\to[k]^n$ with $\omega(t)=C(t)$. **Voter** is the case $h=1$.
--
--   A configuration is a **consensus** if all nodes hold the same opinion. For a real number $x$, the event $\tau_{\mathrm{consensus}}\le x$ holds on a path when some round $t\le x$ is a consensus configuration.
--
--   These are the objects of every statement of the mission: the consensus time, the densities and the maximum density at a round are read off the path.
--
--   **Formalization Note** Nodes are `Fin n`, opinions `Fin k`; the configuration space carries the discrete σ-algebra. $p_{\max}$ is the real supremum over the finite type `Fin k` (the maximum when $k\ge1$). The path law is the published `MarkovChainCLT.chainMeasure` of the kernel started from $\delta_{C_0}$. The event $\tau_{\mathrm{consensus}}\le x$ is an existential over rounds $t\in\mathbb N$ with $(t:\mathbb R)\le x$, not a `sInf`, so a path that never reaches consensus is never counted as fast. Consensus is absorbing for $h\ge1$ (verified in the mission's sanity checks).
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, §2, p.4 (configurations, p_i(t), the h-Majority rule); §1, p.1 and §1.2, p.2 (consensus, pmax); §5.2, p.25 (Voter is 1-majority); Theorem 7.1, p.40 (τconsensus)

import Mathlib
import Definitions.Def_HMajConsensus_majLaw
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- A configuration `C ∈ [k]^n`: the opinion `C_v` of every node `v ∈ [n]` (d'Amore, Rybicki,
Shimizu, Shiraga, Vacus, arXiv:2610.40562, §2, p.4).

**Formalization Note** Nodes `[n]` are `Fin n` and opinions `[k]` are `Fin k` (0-based labels).
The space is finite and carries the product of discrete σ-algebras, so every set of
configurations is measurable. -/
abbrev Config (n k : ℕ) := Fin n → Fin k

/-- The density `p_i = |{v ∈ [n] : C_v = i}| / n` of opinion `i` in configuration `C`
(arXiv:2610.40562, §2, p.4, rule 1; §1.2, p.2). -/
noncomputable def density {n k : ℕ} (C : Config n k) (i : Fin k) : ℝ :=
  ((Finset.univ.filter (fun v => C v = i)).card : ℝ) / n

/-- The maximum density `pmax = max_{i ∈ [k]} p_i` (arXiv:2610.40562, §1.2, p.2; `pmax(t)`, §7,
p.40).

**Formalization Note** Written as the real supremum over the finite type `Fin k`; for `k ≥ 1` it
is the maximum of finitely many values (attained). Every statement of the mission assumes
`2 ≤ k`. -/
noncomputable def pmax {n k : ℕ} (C : Config n k) : ℝ :=
  ⨆ i : Fin k, density C i

/-- The empirical opinion distribution `p(C)` of a configuration, as a probability vector: the
opinion of a node chosen uniformly at random (arXiv:2610.40562, §2, p.4, rule 1). Its mass at
`i` is `density C i` (verified in `Solutions/verification`).

**Formalization Note** Needs at least one node. -/
noncomputable def empirical {n k : ℕ} [Nonempty (Fin n)] (C : Config n k) : PMF (Fin k) :=
  PMF.map C (PMF.uniformOfFintype (Fin n))

/-- The law of the new opinion of node `v` given the current configuration `C`: `Maj(X^{(v)})`
with `X^{(v)} ∼ Multinomial(h; p(C))` (arXiv:2610.40562, §2, p.4, rule 2).

**Formalization Note** The node `v` only witnesses `n ≥ 1` so that `p(C)` is defined; the law is
the same for every node (`majLaw h (empirical C)`). Sampling `h` nodes uniformly with replacement
(the node itself included) and reading their opinions is sampling `h` times from `p(C)`. -/
noncomputable def nodeLaw {n k : ℕ} (h : ℕ) (C : Config n k) (v : Fin n) : Measure (Fin k) :=
  haveI : Nonempty (Fin n) := ⟨v⟩
  majLaw h (empirical C)

instance nodeLaw_isProbabilityMeasure {n k : ℕ} (h : ℕ) (C : Config n k) (v : Fin n) :
    IsProbabilityMeasure (nodeLaw h C v) := by
  unfold nodeLaw
  infer_instance

/-- One synchronous round of `h`-Majority: given `C(t)`, every node `u ∈ [n]` independently
samples `X^{(u)} ∼ Multinomial(h; p(t))` and sets `C_u(t+1) = Maj(X^{(u)})`, ties broken
uniformly; all nodes update simultaneously with fresh randomness (arXiv:2610.40562, §2, p.4).

**Formalization Note** The kernel maps `C` to the product over nodes of `nodeLaw h C u`.
Voter is `step 1` ("Voter is exactly 1-majority", §5.2, p.25). -/
noncomputable def step {n k : ℕ} (h : ℕ) : Kernel (Config n k) (Config n k) :=
  Kernel.ofFunOfCountable (fun C => Measure.pi (fun u : Fin n => nodeLaw h C u))

instance step_isMarkovKernel {n k : ℕ} (h : ℕ) : IsMarkovKernel (step (n := n) (k := k) h) :=
  ⟨fun C => by
    change IsProbabilityMeasure (Measure.pi (fun u : Fin n => nodeLaw h C u))
    infer_instance⟩

/-- The law of the `h`-Majority process `(C(t))_{t = 0,1,…}` started from the initial
configuration `C(0) = C₀` (arXiv:2610.40562, §2, p.4): a measure on paths `ω : ℕ → [k]^n`,
`ω t = C(t)`.

**Formalization Note** It is the published Markov-chain path law
`MarkovChainCLT.chainMeasure` (Ionescu-Tulcea) of the kernel `step h` from `δ_{C₀}`. -/
noncomputable def pathLaw {n k : ℕ} (h : ℕ) (C₀ : Config n k) : Measure (ℕ → Config n k) :=
  MarkovChainCLT.chainMeasure (step h) (Measure.dirac C₀)

instance pathLaw_isProbabilityMeasure {n k : ℕ} (h : ℕ) (C₀ : Config n k) :
    IsProbabilityMeasure (pathLaw h C₀) := by
  unfold pathLaw
  infer_instance

/-- `C` is a consensus configuration: every node holds the same opinion
(arXiv:2610.40562, §1, p.1). -/
def IsConsensus {n k : ℕ} (C : Config n k) : Prop :=
  ∃ i : Fin k, ∀ v, C v = i

/-- The event `τ_consensus ≤ x` on a path `ω`: some round `t ∈ ℕ` with `t ≤ x` is a consensus
configuration (arXiv:2610.40562, Theorem 7.1, p.40; `τ_consensus` is the first such round).

**Formalization Note** Stated as an existential over rounds rather than with `sInf` (which would
count a path that never reaches consensus as `τ = 0`). The bound `x` is real; a round is a
natural number compared after casting. Consensus is absorbing, so this is the same as consensus
at round `⌊x⌋` when `x ≥ 0`. -/
def ConsensusBy {n k : ℕ} (x : ℝ) (ω : ℕ → Config n k) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ x ∧ IsConsensus (ω t)

end HMajConsensus


