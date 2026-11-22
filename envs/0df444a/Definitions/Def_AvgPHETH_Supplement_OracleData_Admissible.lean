-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_Admissible
-- name    : AvgPHETH_Supplement_OracleData_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:58:45.982764+00:00
-- url     : https://prove2.me/theorems/ed51842b-0121-49d0-a45a-86a0506260c8
-- title:
--   Admissible data and seeds for the oracle construction
-- statement:
--   The data and seeds of the oracle construction are admissible if:
--
--   1. $\varepsilon(n)>0$, $\varepsilon(n)=o(1)$, $\varepsilon$ is efficiently computable, and $\varepsilon\ge n^{-o(1)}$;
--   2. every deterministic oracle machine occurs in the numbering, up to its acceptance behaviour;
--   3. $(k_s,M_s,m_s)_s$ enumerates all triples $(k,M,m)$ with $k\ge1$, $m\ge2$, each infinitely often;
--   4. the selection rule picks an element of every nonempty set of disagreeing pairs;
--   5. the seeds are independent and uniform on $[0,1]$;
--   6. for every $s$, $(k_s,n_s)$ is active and (a) $n_s>\max_{u<s}t_u(n_u)$, (b) $J_{k_s}(n_s)>\max_{u<s}J_{k_u}(n_u)$, (c) $t_s(n_s)\le2^{a_{k_s}(n_s)}$, (d) $\Pr[E_{k_s,n_s}]\ge1-2^{-s}$.
--
--   These are the standing assumptions of Section 8.1 under which Theorems 8.5 and 8.7 are stated.
--
--   **Formalization Note** $\varepsilon\ge n^{-o(1)}$ is: for every $\delta>0$, $\varepsilon(n)\ge n^{-\delta}$ for all sufficiently large $n$. Indices $s$ start at $0$, where (d) is void.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.38–40 (PDF 40–42)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData
import Definitions.Def_AvgPHETH_Supplement_OracleData_tPar
import Definitions.Def_AvgPHETH_Supplement_EventE
import Definitions.Def_AvgPHETH_Supplement_IsSeedFamily
import Definitions.Def_AvgPHETH_Supplement_IsEfficientlyComputable
import Definitions.Def_AvgPHETH_Supplement_IsActive
import Definitions.Def_AvgPHETH_Supplement_JPar
import Definitions.Def_AvgPHETH_Supplement_aPar
import Definitions.Def_AvgPHETH_acceptsAt

namespace AvgPHETH.Supplement

open KarpLiptonOM AvgPHETH Filter Topology

/-- The data `D` and the seeds `U` are as §8.1 requires
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.38–40 (PDF 40–42)):

1. `ε`: "let `ε(n)` be an arbitrary efficiently-computable function such that `ε(n) = o(1)`. We may
   assume `ε ≥ n^{−o(1)}` without loss of generality" (p.38);
2. the numbering `mach` contains every oracle machine up to its acceptance behaviour;
3. `enum` is "an enumeration of all triples `(k, M, m)` where `k ≥ 1`, `m ≥ 2`, and `M` is an oracle
   machine …, such that each triple appears infinitely often" (p.40);
4. `pick` selects an element of every nonempty set of disagreeing pairs;
5. the seeds are independent and uniform on `[0,1]`;
6. the reserved lengths: "set `n_s` to be large enough so that `(k_s, n_s)` is active and the following
   properties hold: (a) `n_s > max_{u<s} t_u(n_u)`, (b) `J_{k_s}(n_s) > max_{u<s} J_{k_u}(n_u)`,
   (c) `t_s(n_s) ≤ 2^{a_{k_s}(n_s)}`, and (d) `Pr[E_{k_s,n_s}] ≥ 1 − 2^{−s}`" (p.40).

**Formalization Note** `ε(n) > 0` is presupposed by `log(1/ε(n))`; "efficiently computable" is
`IsEfficientlyComputable`; `ε ≥ n^{−o(1)}` is: for every `δ > 0`, `ε(n) ≥ n^{−δ}` for all sufficiently
large `n`. The indices `s` run over `ℕ` from `0`, where (d) is void. The probability in (d) is the
measure of the event `EventE`, which depends on the seeds only. -/
def OracleData.Admissible (D : OracleData) {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U : ℕ × CVar × ℕ → Ω → ℝ) : Prop :=
  ((∀ n, 0 < D.eps n) ∧ Tendsto D.eps atTop (𝓝 0) ∧ IsEfficientlyComputable D.eps ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-δ) ≤ D.eps n) ∧
    (∀ M : OracleTM, ∃ i : ℕ, ∀ (O : Set (List Bool)) (t : ℕ) (w : List (Option Bool)),
      acceptsAt (D.mach i) O t w ↔ acceptsAt M O t w) ∧
    ((∀ s, 1 ≤ (D.enum s).1 ∧ 2 ≤ (D.enum s).2.2) ∧
      ∀ k i m : ℕ, 1 ≤ k → 2 ≤ m → ∀ N : ℕ, ∃ s, N ≤ s ∧ D.enum s = (k, i, m)) ∧
    (∀ S : Set ((CVar → List Bool) × List Bool), S.Nonempty → D.pick S ∈ S) ∧
    IsSeedFamily μ U ∧
    ∀ s : ℕ, IsActive D.eps (D.enum s).1 (D.ns s) ∧
      (∀ r, r < s → D.tPar r (D.ns r) < D.ns s) ∧
      (∀ r, r < s → JPar D.eps (D.enum r).1 (D.ns r) < JPar D.eps (D.enum s).1 (D.ns s)) ∧
      D.tPar s (D.ns s) ≤ 2 ^ aPar D.eps (D.enum s).1 (D.ns s) ∧
      1 - (2 : ENNReal)⁻¹ ^ s ≤
        μ {ω | EventE D.eps (fun i v c => U (i, v, c) ω) (D.enum s).1 (D.ns s)}

end AvgPHETH.Supplement


