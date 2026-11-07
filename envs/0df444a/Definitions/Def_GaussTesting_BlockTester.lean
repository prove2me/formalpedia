-- Prove2me | Definitions.Def_GaussTesting_BlockTester
-- name    : GaussTesting_BlockTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:45.276254+00:00
-- url     : https://prove2.me/theorems/a30cc3cb-220f-4e5d-875d-21178560cba9
-- title:
--   Testers acting on $k$ copies at a time
-- statement:
--   A **block tester** on $k$ copies consists of
--
--   1. a number of rounds $r\in\mathbb N$;
--   2. an effect $E$ on $\mathcal H^{\otimes k}$, $0\preceq E\preceq I$ (the accepting outcome of one round);
--   3. a decision rule $f:\{\mathrm{acc},\mathrm{rej}\}^r\to\{\mathrm{ACCEPT},\mathrm{REJECT}\}$.
--
--   On input $|\psi\rangle^{\otimes kr}$ it measures $\{E,I-E\}$ on each of the $r$ blocks $|\psi\rangle^{\otimes k}$ and outputs $f$ of the outcomes. The rounds are independent, each accepting with probability $p=\langle\psi^{\otimes k}|E|\psi^{\otimes k}\rangle$, so
--
--   $$
--   \Pr[\mathrm{ACCEPT}]=\sum_{s\in\{0,1\}^r:\,f(s)=\mathrm{ACCEPT}}\ \prod_{i=1}^r p^{s_i}(1-p)^{1-s_i}.
--   $$
--
--   It uses $t=k\cdot r$ copies. This is the shape of every tester in the paper (Algorithm 1 with a base tester on $k$ copies, Theorem 1.4 "acting on $k$ copies of the state at a time", Table 1).
--
--   **Formalization Note** Every block tester is a $t$-copy algorithm in the sense of Definition 1.2 (a product measurement followed by classical post-processing), so the existence of a block tester implies the existence of a tester in the paper's sense.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4; Theorem 1.4 and Table 1, p.5; Algorithm 1, p.28

import Definitions.Def_GaussTesting_tpow

namespace GaussTesting

/-- A tester that acts on `k` copies of the state at a time: in each of `rounds` independent rounds it
performs the two-outcome measurement `{E, I − E}` on a fresh block `|ψ⟩^{⊗k}` (outcome `E` =
"accept this round"), and it outputs ACCEPT iff `accept` holds of the vector of round outcomes. It
consumes `t = k · rounds` copies.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4 (`t`-copy testers), Theorem 1.4, p.5 ("acting on `k`
copies of the state at a time"; "Each of these tests is repeated … times"), Table 1, p.5 ("the number of
copies jointly measured in each round"), Algorithm 1, p.28.

**Formalization Note.** This is the reading of "a `t`-copy tester acting on `k` copies at a time": a
product of `rounds` identical two-outcome measurements on `ℋ^{⊗k}` followed by deterministic classical
post-processing. Every such procedure is a `t`-copy tester in the sense of Definition 1.2, so an
existence statement over `BlockTester` implies the corresponding one over Definition 1.2. `E` is an
effect: `0 ≤ E ≤ I` (`E` and `I − E` positive). -/
structure BlockTester (ι : Type*) (k : ℕ) where
  /-- The number of rounds. -/
  rounds : ℕ
  /-- The accepting effect of one round, on `ℋ^{⊗k}`. -/
  E : Ell2 (Fin k → ι) →L[ℂ] Ell2 (Fin k → ι)
  E_nonneg : E.IsPositive
  E_le_one : (1 - E).IsPositive
  /-- The final decision from the round outcomes (`true` = that round accepted). -/
  accept : (Fin rounds → Bool) → Bool

/-- The acceptance probability of one round on `|ψ⟩^{⊗k}`, `⟨ψ^{⊗k}| E |ψ^{⊗k}⟩`. -/
noncomputable def BlockTester.roundAccept {ι : Type*} {k : ℕ} (T : BlockTester ι k) (ψ : Ell2 ι) :
    ℝ :=
  (inner ℂ (tpow k ψ) (T.E (tpow k ψ))).re

/-- The probability that the tester outputs ACCEPT on `|ψ⟩^{⊗ k·rounds}`: the rounds are independent,
each accepting with probability `p = roundAccept`. -/
noncomputable def BlockTester.acceptProb {ι : Type*} {k : ℕ} (T : BlockTester ι k) (ψ : Ell2 ι) :
    ℝ :=
  ∑ s : Fin T.rounds → Bool,
    if T.accept s then ∏ i, (if s i then T.roundAccept ψ else 1 - T.roundAccept ψ) else 0

end GaussTesting


