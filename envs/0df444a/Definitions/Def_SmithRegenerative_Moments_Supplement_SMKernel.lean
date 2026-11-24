-- Prove2me | Definitions.Def_SmithRegenerative_Moments_Supplement_SMKernel
-- name    : SmithRegenerative_Moments_Supplement_SMKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:42:10.34907+00:00
-- url     : https://prove2.me/theorems/018a8d92-3566-425d-a6d8-f2054145fabd
-- title:
--   Countable S.M. transition kernel, conditional waits, unconditional diagonal and source regularity
-- statement:
--   States are the positive integers, relabelled by $n\mapsto n+1$. A transition matrix $p_{ij}$ has nonnegative entries, row sums one and no self-transitions. Conditional on selecting $j$ from $i$, the next wait has full extended law $G_{ij}$ on $[0,\infty]$, with no used law concentrated at zero. The source's diagonal wait law is the unconditional mixture,
--   $$\Omega_{ii}=\sum_jp_{ij}G_{ij},\qquad m_{ij}=\int u\,d\Omega_{ij}(u),$$
--   where $\Omega_{ij}=G_{ij}$ off the diagonal. Infinite means and defective waits are permitted. Finite-transition masses are $p_{ij}G_{ij}([0,\infty))$.
--
--   Regularity is the exact condition (4·4·1): for each starting state there are positive sequences $\epsilon_n,\eta_n$, independent of the allowable path, with divergent $\sum_n\epsilon_n\eta_n$, and $G_{a_na_{n+1}}([0,\epsilon_n])\le1-\eta_n$ along every allowable path. No nonexplosion consequence is included as an axiom.
--
--   This is the general S.M. kernel, separate from its realization. Unused conditional laws may be filled arbitrarily; zero transition weights remove them from actual probabilities. The source explicitly leaves such laws undefined.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, §4·1, pp. 19–20; §4·4, pp. 21–22

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_ExtendedRenewal

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory Filter Topology

/-- Smith (1955), §4·1, pp. 19–20, (M1)–(M3).
Formalization Note: state n represents the positive integer n+1. `G i j` is the full
extended wait law conditional on the next state j, including infinity. Self-transitions
are excluded: the paper reserves Ω_μμ for the unconditional mixture, not a self-wait.
Unused conditional laws (p_ij=0) are arbitrary probability measures. -/
structure SMKernel where
  p : ℕ → ℕ → ENNReal
  row_sum : ∀ i, ∑' j, p i j = 1
  no_self : ∀ i, p i i = 0
  G : ℕ → ℕ → Measure ENNReal
  probability : ∀ i j, IsProbabilityMeasure (G i j)
  not_zero : ∀ i j, p i j ≠ 0 → G i j {0} < 1

/-- Smith (1955), (4·1·2), p. 20. Formalization Note: Ω_ii is the mixture
Σ_j p_ij Ω_ij; Ω_ij with i≠j is a conditional wait law. -/
noncomputable def SMKernel.waitLaw (S : SMKernel) (i j : ℕ) : Measure ENNReal :=
  if i = j then Measure.sum (fun k => S.p i k • S.G i k) else S.G i j

/-- Smith (1955), (4·1·3), p. 20, all pairwise means including the unconditional
diagonal. Formalization Note: infinity is a genuine value, including defective waits. -/
noncomputable def SMKernel.m (S : SMKernel) (i j : ℕ) : ENNReal :=
  extendedMean (S.waitLaw i j)

/-- Smith (1955), (4·5·1), p. 22: probability of a selected edge completing
in finite time. Formalization Note: conditional G is used also for unused edges;
its value there is annihilated by p=0. -/
noncomputable def SMKernel.finiteMass (S : SMKernel) (i j : ℕ) : ENNReal :=
  S.p i j * S.G i j (Set.Iio ⊤)

/-- Smith (1955), §4·4, p. 21: an allowable state sequence. -/
def SMKernel.Allowable (S : SMKernel) (a : ℕ → ℕ) : Prop :=
  ∀ n, S.p (a n) (a (n + 1)) ≠ 0

/-- Smith (1955), §4·4, pp. 21–22, (4·4·1), source regularity exactly.
Formalization Note: epsilon and eta depend on the starting state, not on the path;
all infinite allowable paths and all their edges are tested. No nonexplosion condition
is substituted for this definition. The erroneous implication discussed on p. 21 is
not built into the definition. -/
def SMKernel.Regular (S : SMKernel) : Prop :=
  ∀ i : ℕ, ∃ ε η : ℕ → ℝ, (∀ n, 0 < ε n ∧ 0 < η n) ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ε n * η n) atTop atTop ∧
    ∀ a : ℕ → ℕ, a 0 = i → S.Allowable a → ∀ n,
      (S.G (a n) (a (n + 1)) (Set.Iic (ENNReal.ofReal (ε n)))).toReal ≤ 1 - η n

end SmithRegenerative.Moments.Supplement


