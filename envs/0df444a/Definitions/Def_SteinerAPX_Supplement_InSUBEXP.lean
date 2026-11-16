-- Prove2me | Definitions.Def_SteinerAPX_Supplement_InSUBEXP
-- name    : SteinerAPX_Supplement_InSUBEXP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:10:32.891123+00:00
-- url     : https://prove2.me/theorems/e5d6cb70-d8f9-42c0-bd46-53c2eae4bac7
-- title:
--   The class SUBEXP $=\bigcap_{\varepsilon>0}\mathrm{DTIME}(2^{n^\varepsilon})$ and the inclusion $\mathrm{NP}\subseteq\mathrm{SUBEXP}$
-- statement:
--   A language $L \subseteq \{0,1\}^*$ is in **SUBEXP** when for every $\varepsilon > 0$ there are a Turing machine $M$ (with finite alphabets) and a constant $c$ such that, on every word $x$, $M$ halts within
--   $$\left\lceil c \cdot 2^{|x|^{\varepsilon}} \right\rceil$$
--   steps and outputs the single bit that says whether $x \in L$. **NP ⊆ SUBEXP** means that every language in NP is in SUBEXP.
--
--   The paper uses SUBEXP in Theorem 2 and Lemma 4(iii) without defining it; this is the standard class $\bigcap_{\varepsilon>0}\mathrm{DTIME}(2^{n^\varepsilon})$.
--
--   **Formalization Note** Machines are Mathlib's multi-stack Turing machines `TM2ComputableAux Bool Bool` with finite stack alphabets (`RevRedSAT.FiniteAlphabets`), run with `HMBinPacking.OutputsWithin`; NP is the published verifier class `CookLevin.InNP` used by the base mission's Theorem 1. The constant $c$ is part of the usual meaning of "time $2^{n^\varepsilon}$".
-- source:
--   Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…3fcfa9), Theorem 2, p.2 (PDF p.4); App. A.3, p.38 (PDF p.40), proof of Lemma 4(iii)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets

set_option autoImplicit false

namespace SteinerAPX.Supplement

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **The class SUBEXP of languages decidable in time `2^{n^ε}` for every `ε > 0`.**
S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript
sha256 6f78a9ea…), Theorem 2, p.2 (PDF p.4), "Unless NP ⊆ SUBEXP", and App. A.3, p.38 (PDF p.40),
proof of Lemma 4(iii): "Under NP ⊄ SUBEXP, 3SAT has no 2^{s^{c'}}-time algorithm for some c' > 0".

A bit language `L` is in SUBEXP when for every `ε > 0` there are a machine `M` with finite stack
alphabets and a constant `c` such that on every word `x`, `M` outputs the single bit `[b]`, with
`b = true` exactly when `x ∈ L`, within `⌈c · 2^{|x|^ε}⌉` steps.

**Formalization Note** The paper uses SUBEXP without defining it; this is the standard class
`⋂_{ε>0} DTIME(2^{n^ε})`. The constant `c` is the usual meaning of "time `2^{n^ε}`" (without it no
machine meets the one-step bound on the empty word). Machines are Mathlib's bundled multi-stack
Turing machines `Turing.TM2ComputableAux Bool Bool` with finite stack alphabets
(`RevRedSAT.FiniteAlphabets`), run with `HMBinPacking.OutputsWithin` (Mathlib
`TM2OutputsInTime`); `n^ε` is the real power `Real.rpow`. -/
def InSUBEXP (L : BitLanguage) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ M : Turing.TM2ComputableAux Bool Bool, RevRedSAT.FiniteAlphabets M ∧
      ∃ c : ℕ, ∀ x : List Bool, ∃ b : Bool, (b = true ↔ L x) ∧
        HMBinPacking.OutputsWithin M x [b]
          ⌈(c : ℝ) * (2 : ℝ) ^ ((x.length : ℝ) ^ ε)⌉₊

/-- **NP ⊆ SUBEXP**: every language in NP (the published verifier class `CookLevin.InNP`) is in
SUBEXP. Same source as `InSUBEXP`. -/
def NPSubsetSUBEXP : Prop :=
  ∀ L : BitLanguage, CookLevin.InNP L → InSUBEXP L

end SteinerAPX.Supplement


