-- Prove2me | Definitions.Def_CertRandQROM_accProb
-- name    : CertRandQROM_accProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:33:04.390005+00:00
-- url     : https://prove2.me/theorems/167b3e9d-78bf-42ae-ae9b-6cca4ffa1c36
-- title:
--   Acceptance probability and the conditional output law $\mathcal A^h_\top$
-- statement:
--   Let $\mathcal A$ be a query algorithm whose outputs are $\Sigma^n\cup\{\bot\}$. For the code $C$ and oracle $h$, the **acceptance probability** is
--
--   $$
--   \Pr\big[\mathrm{Verify}^h(\mathcal A^h)\ne\bot\big]=\sum_{x\ \text{correct}}\Pr[X=x\mid H=h],
--   $$
--
--   and the **conditional law** $\mathcal A^h_\top$ (the output of Verify conditioned on not being $\bot$) gives a correct $x$ the probability $\Pr[X=x\mid H=h]/\Pr[\mathrm{Verify}^h(\mathcal A^h)\ne\bot]$ and every other outcome probability $0$.
--
--   These are the two quantities of the bad event in Definition 6.1.
--
--   **Formalization Note** Outputs are `Option (Fin n → Σ)`: `some x` is the proof $\pi=x$, `none` stands for $\bot$ or any string that does not parse as an element of $\Sigma^n$ (Verify rejects both). An adversary with any other finite outcome set reduces to this one by grouping its POVM elements according to Verify's answer. When the acceptance probability is $0$ the quotient is Lean's $0/0=0$; every statement using $\mathcal A^h_\top$ also assumes acceptance probability $\ge\delta>0$.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Definition 6.1, (Q, h∞)-Certifiable Min-Entropy, p.28 (PDF p.30); Construction 6.2, Verify, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_CertRandQROM_outProb
import Definitions.Def_CertRandQROM_IsCorrect

namespace CertRandQROM

open Classical in
/-- **Acceptance probability** (Definition 6.1, p.28; Construction 6.2, Verify, p.29 of
Coladangelo et al., arXiv:2608.31112, sha256 b75095a2…):
`accProb C A h = Pr[Verify^h(A^h) ≠ ⊥] = Σ_{x correct} Pr[X = x | H = h]`.

**Formalization Note** The adversary's outputs are `Option (Fin n → S)`: `some x` is the proof
`π = x`, `none` is `⊥` or any string that does not parse as an element of `Σ^n` (Verify, step 1,
rejects both). Any adversary with another finite outcome set reduces to this one by grouping its
POVM elements by what Verify does with them. -/
noncomputable def accProb {n : ℕ} {S W : Type} [Fintype S] [DecidableEq S] [Fintype W]
    [DecidableEq W] {Q : ℕ} (C : Finset (Fin n → S))
    (A : QueryAlg (Fin n × S) W (Option (Fin n → S)) Q) (h : Fin n × S → Bool) : ℝ :=
  ∑ x : Fin n → S, if IsCorrect C h x then outProb A h (some x) else 0

open Classical in
/-- **The conditional output law `A_⊤^h`** (Definition 6.1, p.28): the distribution of
`Verify^h(A^h)` conditioned on the output not being `⊥`:
`condOut C A h (some x) = Pr[X = x | H = h] / accProb C A h` for a correct `x`, and `0` for an
incorrect `x` and for `⊥` (`none`).

**Formalization Note** When `accProb C A h = 0` the quotient is Lean's `0/0 = 0`; every
statement that uses `condOut` also assumes `accProb C A h ≥ δ > 0`. -/
noncomputable def condOut {n : ℕ} {S W : Type} [Fintype S] [DecidableEq S] [Fintype W]
    [DecidableEq W] {Q : ℕ} (C : Finset (Fin n → S))
    (A : QueryAlg (Fin n × S) W (Option (Fin n → S)) Q) (h : Fin n × S → Bool) :
    Option (Fin n → S) → ℝ
  | none => 0
  | some x => if IsCorrect C h x then outProb A h (some x) / accProb C A h else 0

end CertRandQROM


