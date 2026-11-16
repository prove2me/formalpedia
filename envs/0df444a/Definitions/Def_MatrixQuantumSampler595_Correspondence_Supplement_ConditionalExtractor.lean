-- Prove2me | Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_ConditionalExtractor
-- name    : MatrixQuantumSampler595_Correspondence_Supplement_ConditionalExtractor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:33.384254+00:00
-- url     : https://prove2.me/theorems/ef11dba9-f043-4297-ace5-5b7c1dbbffb2
-- title:
--   Definition 1.4 and §2.2 — conditional-min-entropy quantum-proof extraction
-- statement:
--   Let $F:\{0,1\}^n\times[t]\to\{0,1\}^m$ be a deterministic map. For every finite quantum register $E=\mathbb C^q$, a normalized cq source is a collection of positive semidefinite blocks $\sigma_x$ with $\sum_x\operatorname{Tr}\sigma_x=1$. Its conditional min-entropy is $H_{\min}(X\mid E)=-\log_2 p_{\rm guess}(X\mid E)$, where guessing probability optimizes over all POVMs on $E$.
--
--   The map is a **strong quantum-proof $(k,\eta)$ extractor** when every such source with $H_{\min}(X\mid E)\ge k$ and an independent uniform public seed $I\in[t]$ satisfies
--
--   $$\Delta(\rho_{F(X,I)IE},\tau_m\otimes\tau_{[t]}\otimes\rho_E)\le\eta.$$
--
--   Here $\Delta$ is half the trace norm and $\rho_E=\sum_x\sigma_x$ is the actual marginal. The output and ideal states are the published base definitions. This predicate places no bound on $q$ and allows singular, zero and noncommuting blocks. It supplies the security notion for the construction theorems, whose entropy assumption differs from bounded-storage security.
--
--   **Formalization Note** A $d$-bit seed is indexed by $\operatorname{Fin}(2^d)$ with its uniform distribution, which is just a relabelling of binary strings. The imported entropy is extended-real valued; only normalized sources are tested.
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), Definition 1.4, p.4; §2.2, Eqs.(2.1)–(2.3), pp.12–13

import Mathlib
import Definitions.Def_MatrixQuantumSampler595_Correspondence_QuantumProofExtractor
import Definitions.Def_DIObliviousTransfer_pGuess

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- Definition 1.4 (p.4), §2.2 (pp.12–13): full conditional-min-entropy security.
The seed alphabet `Fin t` is uniform and independent; for a d-bit seed take t=2^d.
No storage dimension bound or restriction to commuting blocks is imposed. -/
def IsStrongConditionalExtractor {n m t : ℕ}
    (F : BitString n → Fin t → BitString m) (k η : ℝ) : Prop :=
  ∀ q : ℕ, ∀ σ : BitString n → Matrix (Fin q) (Fin q) ℂ,
    QAlgorithms.Papers.Independent.Advance50.P02.NormalizedBlocks σ →
    (k : EReal) ≤ DIObliviousTransfer.Hmin σ →
    QAlgorithms.traceDistance (strongOutputState F σ)
      (strongIdealState (m := m) (t := t) σ) ≤ η

end MatrixQuantumSampler595.Correspondence.Supplement


