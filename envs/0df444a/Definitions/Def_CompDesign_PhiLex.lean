-- Prove2me | Definitions.Def_CompDesign_PhiLex
-- name    : CompDesign_PhiLex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:52:36.766313+00:00
-- url     : https://prove2.me/theorems/a703822a-1ca1-4dfa-9bfb-8fc8debfd974
-- title:
--   Potentials $\Phi$ and lexicographic $\Phi'$ of the proof of Theorem 4.1
-- statement:
--   For a participating set $S$, the proof of Theorem 4.1 uses the potential
--   $$\Phi(S)=v(S)\prod_{i\in S}\Big(1-\frac{c_i}{B}\Big)$$
--   and, to handle zero-value states, the **lexicographic potential**
--   $$\Phi'(S)=\Big(\Phi(S),\,-\sum_{i\in S}c_i\Big),$$
--   ordered lexicographically: first by $\Phi$, ties broken by $-\sum_{i\in S}c_i$.
--
--   Every strict better response of $\Gamma^{mc}$ strictly increases $\Phi'$, which is how termination is proved.
--
--   **Formalization Note** $\Phi'$ takes values in `ℝ ×ₗ ℝ` (`Lex (ℝ × ℝ)`), whose order is the lexicographic one.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), proof of Theorem 4.1, §4.1, p.17 (PDF 20)

import Mathlib

namespace CompDesign

/-- The potential `Φ(S) = v(S) ∏_{i∈S} (1 − c_i/B)` of the proof of Theorem 4.1, §4.1, p.17 (PDF 20)
of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). -/
noncomputable def Phi {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  v S * ∏ i ∈ S, (1 - c i / B)

/-- The lexicographic potential `Φ′(S) = (Φ(S), −∑_{i∈S} c_i)` of the proof of Theorem 4.1, §4.1,
p.17 (PDF 20) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3,
2026, sha256 3d305d4d…).

**Formalization Note.** The value lives in `ℝ ×ₗ ℝ` (`Lex (ℝ × ℝ)`), whose order compares the first
coordinate and breaks ties by the second, which is the lexicographic order the proof uses. -/
noncomputable def PhiLex {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ ×ₗ ℝ :=
  toLex (Phi v B c S, -∑ i ∈ S, c i)

end CompDesign


