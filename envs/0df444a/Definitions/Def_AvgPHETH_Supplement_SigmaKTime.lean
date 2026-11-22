-- Prove2me | Definitions.Def_AvgPHETH_Supplement_SigmaKTime
-- name    : AvgPHETH_Supplement_SigmaKTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:25:52.145803+00:00
-- url     : https://prove2.me/theorems/80b3b564-5cfe-46b7-8b17-3922704d9cf2
-- title:
--   The class $\Sigma_k\mathrm{TIME}^O[t]$ via clocked alternating programs
-- statement:
--   Let $O$ be an oracle, $k\in\mathbb N$ and $t:\mathbb N\to\mathbb R$. For a deterministic oracle machine $M$ and numbers $T,W$, write $\Phi^O_{T,W}(x)=1$ if
--
--   $$\exists w_1\in\{0,1\}^W\;\forall w_2\in\{0,1\}^W\cdots Q_kw_k\in\{0,1\}^W:\ M^O(x,w_1,\dots,w_k)\text{ accepts within }T\text{ steps}.$$
--
--   A language $L$ is in $\Sigma_k\mathrm{TIME}^O[t]$ if there are a constant $c\ge1$ and a machine $M$ such that, for every input $x$ and all $T,W\ge\lceil c\,t(|x|)\rceil+c$, $L(x)=\Phi^O_{T,W}(x)$.
--
--   This is the time-$O(t)$ alternating class against which the oracle barrier of Section 8 is proved.
--
--   **Formalization Note** Definition 4.3 (p.15) states this characterisation, with threshold $ct(|x|)$, for time-constructible $t(n)\ge n$. Here it is the definition for every $t$, because Theorems 1.5 and 8.7 use bounds that need not be time-constructible. The added summand $c$ only enlarges the class. The answer must not depend on the clock or the witness length beyond the threshold, so the machine cannot read information off them.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.3 and the characterisation following it, p.15 (PDF 17)

import Mathlib
import Definitions.Def_KarpLiptonOM_Alt
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_acceptsAt

namespace AvgPHETH.Supplement

open KarpLiptonOM AvgPHETH

/-- The class `Σ_kTIME^O[t]` through clocked alternating programs (Definition 4.3,
Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.2, p.15 (PDF 17)): `L` is in the class if there are a constant `c ≥ 1` and a
deterministic oracle machine `M` such that, for every input `x` and all `T, W ≥ c·t(|x|)`,
`L(x) = Φ^O_{T,W}(x)` with `Φ = (M, k, ∃)`, i.e.
`x ∈ L ⟺ ∃w₁ ∈ {0,1}^W ∀w₂ ∈ {0,1}^W ⋯ Q_k w_k ∈ {0,1}^W : M^O(x, w₁, …, w_k)` accepts within `T` steps.

**Formalization Note** The page characterises the class this way for time-constructible
`t(n) ≥ n` ("Moreover, the verifier `M` can be chosen … `L(x) = Φ^O_{T,W}(x)` whenever `T, W ≥ ct(|x|)`").
Here the characterisation is the definition, for every `t : ℕ → ℝ`, since Theorems 1.5 and 8.7 use
bounds such as `2^{ε(n)n/log^k n}` that need not be time-constructible. The threshold is
`⌈c·t(|x|)⌉₊ + c`; the summand `c` only weakens the requirement (it matters only where `t` is below
`1`), so the class contains the page's. The answer must be the same for every larger clock and
witness length, so the machine cannot read information off the clock or the witness length.
`M` reads the tuple `(x, w₁, …, w_k)` as `tupleEnc`. -/
def SigmaKTime (O : Set (List Bool)) (k : ℕ) (t : ℕ → ℝ) : Set (Set (List Bool)) :=
  {L | ∃ (c : ℕ) (M : OracleTM), 1 ≤ c ∧ ∀ (x : List Bool) (T W : ℕ),
      ⌈(c : ℝ) * t x.length⌉₊ + c ≤ T → ⌈(c : ℝ) * t x.length⌉₊ + c ≤ W →
        (x ∈ L ↔ Alt W k true (fun ws => acceptsAt M O T (tupleEnc (x :: ws))))}

end AvgPHETH.Supplement


