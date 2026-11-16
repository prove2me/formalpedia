-- Prove2me | Definitions.Def_GMRDiversity_Supplement_value
-- name    : GMRDiversity_Supplement_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:08:30.625035+00:00
-- url     : https://prove2.me/theorems/d6bb0d24-f61a-492a-87e9-4e68585ccdbb
-- title:
--   The value $V^\pi_T$, the cost, the budgeted optimum $V^*_n$ and the operator counts
-- statement:
--   Fix a GMR framework $\mathcal G$ with one rule of each arity and full feedback, a policy $\pi$ and a horizon $T\in\mathbb N$, and let $z_1,\dots,z_T$ be the first $T$ candidates of the run of $\pi$.
--
--   1. The **value** is
--   $$
--   V^\pi_T(\mathcal G):=\mathbb E\Big[\max_{t\in[T]}U(z_t)\Big].
--   $$
--   2. The **cost** of the first $T$ rounds is $\mathrm{cost}(\pi,T):=\sum_{1\le t\le T}c(D_t)$, where $D_t$ is the operator used in round $t$.
--   3. The **optimal value under budget $n$** is
--   $$
--   V^*_n(\mathcal G):=\sup_{\substack{\pi\in\Pi^{\mathrm{obs}}_{\mathcal G},\,T\in\mathbb N\\ \mathrm{cost}(\pi,T)\le n\ \text{a.s.}}}V^\pi_T(\mathcal G).
--   $$
--   4. The **operator counts** $G^\pi_T,M^\pi_T,R^\pi_T$ are the numbers of generation, mutation and recombination queries among the first $T$ rounds.
--
--   These are the quantities compared in Theorems 1 and 2: Theorem 1 gives the asymptotics of $V^*_n$ on a Gaussian framework, and Theorem 2 bounds the operator counts of near-optimal policies.
--
--   **Formalization Note** Values live in the extended reals $[-\infty,+\infty]$. The expectation is $\mathbb E[(\max)^+]-\mathbb E[(\max)^-]$, which is the usual expectation whenever it is defined; the maximum over the empty set ($T=0$) is $-\infty$, so $V^\pi_0=-\infty$. $V^*_n$ is the supremum in the extended reals, so an empty or unbounded index set gives $-\infty$ or $+\infty$, never a default $0$. The cost bound is required almost surely under the run law.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), §2 'Policies' and 'Query Complexity', p.4; operator counts §8, p.16

import Mathlib
import Definitions.Def_GMRDiversity_Supplement_Policy

namespace GMRDiversity.Supplement

open MeasureTheory ProbabilityTheory Finset

variable {X : Type} [MeasurableSpace X]

/-- `max_{t ∈ [T]} U(z_t)` along a run (`⊥` for `T = 0`). -/
noncomputable def bestU (F : GMRFramework X) (T : ℕ) (ω : ℕ → Op × X) : EReal :=
  ⨆ t : Fin T, ((F.U (ω t).2 : ℝ) : EReal)

/-- **The value `V^π_T(G) := E[max_{t∈[T]} U(z_t)]`** (Brandenberger, Doron-Arad, Mossel, *Genetic
Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…,
§2 "Query Complexity", p.4).

**Formalization Note.** The expectation is taken in the extended reals as
`E[(max)⁺] − E[(max)⁻]` (two lower Lebesgue integrals), which is the usual expectation whenever it
is well-defined (p.3 assumes all expectations are) and never collapses to a junk `0`. At `T = 0`
the maximum over the empty set is `⊥`, so `V^π_0 = ⊥`. -/
noncomputable def value {F : GMRFramework X} (π : Policy F) (T : ℕ) : EReal :=
  ((∫⁻ ω, (bestU F T ω).toENNReal ∂(runLaw π) : ENNReal) : EReal) -
    ((∫⁻ ω, (-bestU F T ω).toENNReal ∂(runLaw π) : ENNReal) : EReal)

/-- `cost(π, T) = Σ_{1 ≤ t ≤ T} c(D_t)` along a run (p.4). -/
def cost (F : GMRFramework X) (T : ℕ) (ω : ℕ → Op × X) : ℕ :=
  ∑ t : Fin T, (ω t).1.cost F

/-- **The optimal value under budget `n`**
`V*_n(G) := sup_{π ∈ Π^obs_G, T ∈ ℕ, cost(π,T) ≤ n} V^π_T(G)`, with `cost(π, T) ≤ n` required
almost surely (Brandenberger, Doron-Arad, Mossel, STOC 2027 submission, manuscript sha256
f89f4f77…, §2 "Query Complexity", p.4).

**Formalization Note.** The supremum is taken in `EReal`, a complete lattice, so it is never a
junk value: an empty index set gives `⊥` and an unbounded one `⊤`. -/
noncomputable def Vstar (F : GMRFramework X) (n : ℕ) : EReal :=
  ⨆ (π : Policy F) (T : ℕ) (_ : ∀ᵐ ω ∂(runLaw π), cost F T ω ≤ n), value π T

/-- The numbers `G^π_T`, `M^π_T`, `R^π_T` of generation, mutation and recombination queries among
the first `T` rounds of a run (§8, p.16). -/
def numGen (T : ℕ) (ω : ℕ → Op × X) : ℕ := (univ.filter (fun t : Fin T => (ω t).1.isGen)).card

/-- The number `M^π_T` of mutations among the first `T` rounds (§8, p.16). -/
def numMut (T : ℕ) (ω : ℕ → Op × X) : ℕ := (univ.filter (fun t : Fin T => (ω t).1.isMut)).card

/-- The number `R^π_T` of recombinations among the first `T` rounds (§8, p.16). -/
def numRec (T : ℕ) (ω : ℕ → Op × X) : ℕ := (univ.filter (fun t : Fin T => (ω t).1.isRec)).card

end GMRDiversity.Supplement


