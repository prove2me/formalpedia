-- Prove2me | Definitions.Def_CertRandQROM_Event1
-- name    : CertRandQROM_Event1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:34:35.902294+00:00
-- url     : https://prove2.me/theorems/52e04853-94cb-4284-a97e-3f55a65988fd
-- title:
--   Event1: noticeable acceptance and low min-entropy
-- statement:
--   For a code $C$, an algorithm $\mathcal A$, $\delta\in\mathbb R$ and $h_\infty\in\mathbb N$, an oracle $h$ satisfies **Event1** if
--
--   $$
--   \Pr\big[\mathrm{Verify}^h(\mathcal A^h)\ne\bot\big]\ge\delta\quad\text{and}\quad H_\infty\big(\mathcal A^h_\top\big)\le h_\infty ,
--   $$
--
--   where $H_\infty(P)=-\log_2\max_o P(o)$ is the min-entropy in bits. It is the bad event of the $(Q,h_\infty)$-certifiable min-entropy property (Definition 6.1).
--
--   **Formalization Note** $H_\infty$ is the published `CommitOpen.Benign.minEntropy`, taken over all outcomes `Option (Σ^n)` of the conditional law (the outcomes of probability $0$ do not change the maximum).
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §7.3, definition of Event1, p.43 (PDF p.45); Definition 6.1, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model
import Definitions.Def_CertRandQROM_accProb

namespace CertRandQROM

/-- **Event1** (§7.3, p.43 of Coladangelo et al., arXiv:2608.31112, sha256 b75095a2…; the bad
event of Definition 6.1, p.28): the oracle `h` satisfies
`Pr[Verify^h(A^h) ≠ ⊥] ≥ δ ∧ H∞(A_⊤^h) ≤ h∞`, with `H∞(P) = −log₂ max_o P(o)` the published
`CommitOpen.Benign.minEntropy` (bits). -/
noncomputable def Event1 {n : ℕ} {S W : Type} [Fintype S] [DecidableEq S] [Fintype W]
    [DecidableEq W] {Q : ℕ} (C : Finset (Fin n → S))
    (A : QueryAlg (Fin n × S) W (Option (Fin n → S)) Q) (δ : ℝ) (hInf : ℕ)
    (h : Fin n × S → Bool) : Prop :=
  δ ≤ accProb C A h ∧ CommitOpen.Benign.minEntropy (condOut C A h) ≤ (hInf : ℝ)

end CertRandQROM


