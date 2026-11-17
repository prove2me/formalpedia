-- Prove2me | Definitions.Def_OnlineCAP_Supplement_IsNodeCompetitive
-- name    : OnlineCAP_Supplement_IsNodeCompetitive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:20:52.505441+00:00
-- url     : https://prove2.me/theorems/bd28cbdc-58ed-4722-accc-e3f976618db7
-- title:
--   α-competitive online algorithm for connectivity augmentation with node arrivals
-- statement:
--   An online algorithm for connectivity augmentation with **node arrivals** on a base graph $G$, connectivity $k$, links $L$ and costs $c$ receives terminal pairs $(s_1,t_1),(s_2,t_2),\dots$ and irrevocably buys links. It is **$\alpha$-competitive** if
--
--   1. it buys only links of $L$;
--   2. on every valid sequence, for every outcome of its coins, every revealed pair is satisfied by the purchased links;
--   3. on every valid sequence $s$, its expected cost is at most $\alpha\cdot\mathrm{OPT}(s)$.
--
--   For a deterministic algorithm the expected cost is its cost, so this is the deterministic competitive ratio of §2.2.
--
--   **Formalization Note** The request sequence is fixed before the coins are drawn (oblivious adversary), as for cut arrivals.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Problem 2.3, p.9; §2.2, p.10 (PDF p.9–10)

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_Supplement_PairSat

open MeasureTheory

namespace OnlineCAP.Supplement

/-- **α-competitive online algorithm for connectivity augmentation with node arrivals.**
Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity Augmentation via
Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Problem 2.3, p.9, with the
competitive ratios of §2.2, p.10 (PDF p.9–10).

`IsNodeCompetitive ends k L c A α` says:
1. the algorithm only buys links of `L`;
2. on every valid sequence of terminal pairs and for every outcome of the coins, every revealed
   pair is satisfied by the purchased links;
3. on every valid sequence `s`, `E[∑_{ℓ ∈ F(s)} c(ℓ)] ≤ α · OPT_node(s)`.

**Formalization Note.** Same shape as `IsCompetitive` for cut arrivals: the request list is
quantified outside the expectation (oblivious adversary). For a deterministic algorithm the
expectation is the cost. A request is an ordered pair `(s, t)` of distinct vertices. -/
def IsNodeCompetitive {n : ℕ} {E : Type} [Fintype E] (ends : E → Sym2 (Fin n)) (k : ℕ)
    (L : Finset (Sym2 (Fin n))) (c : Sym2 (Fin n) → ℝ)
    (A : RandOnlineAlg (Sym2 (Fin n)) (Fin n × Fin n)) (α : ℝ) : Prop :=
  (∀ ω s, A.buy ω s ⊆ L) ∧
  (∀ s, NodeValid ends k L s → ∀ ω, ∀ p ∈ s, PairSat ends k (A.buy ω s) p) ∧
  (∀ s, NodeValid ends k L s →
    ∫ ω, (∑ ℓ ∈ A.buy ω s, c ℓ) ∂A.μ ≤ α * OPTnode ends k L c s)

end OnlineCAP.Supplement


