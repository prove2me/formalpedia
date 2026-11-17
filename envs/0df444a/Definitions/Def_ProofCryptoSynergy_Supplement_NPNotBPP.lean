-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_NPNotBPP
-- name    : ProofCryptoSynergy_Supplement_NPNotBPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:50:07.890428+00:00
-- url     : https://prove2.me/theorems/f9101eb0-03ce-40a4-ae2e-fe3fdc7ef278
-- title:
--   BPP and $\mathsf{NP}\not\subseteq\mathsf{BPP}$
-- statement:
--   A language $L$ is in **BPP** if the promise problem $(L,\overline L)$ is in promise-BPP. The hypothesis $\mathsf{NP}\not\subseteq\mathsf{BPP}$ says some language in NP is not in BPP.
--
--   It is the hypothesis of Theorem 78.
--
--   **Formalization Note** The paper does not define BPP; this is the standard definition on the published `promiseBPP` and `InNP`.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 78, p.57 (PDF 59)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_InUTIME
import Definitions.Def_ProofCryptoSynergy_promiseBPP

open KarpLiptonOM

namespace ProofCryptoSynergy.Supplement

/-- `L ∈ BPP`: the promise problem `(L, Lᶜ)` is in the published `promiseBPP` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 78,
p.57 (PDF 59)).

**Formalization Note** The paper does not define BPP; this is the standard definition. -/
def InBPP (L : Set (List Bool)) : Prop :=
  (⟨L, Lᶜ, disjoint_compl_right⟩ : PromiseProblem) ∈ promiseBPP

/-- **`NP ⊄ BPP`** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 78, p.57 (PDF 59)): some language in NP (published `InNP`) is not in
BPP. -/
def NPNotBPP : Prop := ∃ L : Set (List Bool), InNP L ∧ ¬ InBPP L

end ProofCryptoSynergy.Supplement


