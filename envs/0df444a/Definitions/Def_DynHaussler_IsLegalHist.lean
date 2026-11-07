-- Prove2me | Definitions.Def_DynHaussler_IsLegalHist
-- name    : DynHaussler_IsLegalHist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:47.592538+00:00
-- url     : https://prove2.me/theorems/43996804-3735-496b-bde0-a59b8ca6995f
-- title:
--   Legal histories of the input–action game of Lemma 32
-- statement:
--   Consider a game in which, in each round, an adversary first chooses an input $i_s$ and a constructor then chooses an action $a_s$, the legal choices depending on the preceding moves. A history $h=((i_1,a_1),\dots,(i_t,a_t))$ is **legal** if at every round $s$ the input $i_s$ lies in the legal input set at the preceding history $h_{<s}$, and the action $a_s$ lies in the legal action set at $h_{<s}$ and the current input $i_s$.
--
--   **Formalization Note** Inputs and actions are arbitrary types $I$, $A$; the legal sets are `legalI t h ⊆ I` and `legalA t h i ⊆ A` for a history `h : Fin t → I × A` of $t$ completed rounds; the prefix $h_{<s}$ is the published `NondualOpt.histPrefix`.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 32, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_NondualOpt_histPrefix

set_option autoImplicit false

namespace DynHaussler

/-- A history `h = ((i_1, a_1), …, (i_t, a_t))` of the input–action game of Lemma 32 is **legal**
if at every round `s` the adversary's input `i_s` lies in the legal input set at the preceding
history `h_{<s}`, and the constructor's action `a_s` lies in the legal action set at `h_{<s}` and
the current input `i_s`. The legal sets may depend on the preceding moves.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Lemma 32, p.43 (PDF p.45).

**Formalization Note** Inputs and actions are arbitrary types `I`, `A`; the legal sets are given
by `legalI t h ⊆ I` and `legalA t h i ⊆ A` for a history `h : Fin t → I × A` of `t` completed
rounds (0-based), and `h_{<s}` is `NondualOpt.histPrefix h s`. -/
def IsLegalHist {I A : Type*} (legalI : (t : ℕ) → (Fin t → I × A) → Set I)
    (legalA : (t : ℕ) → (Fin t → I × A) → I → Set A) {t : ℕ} (h : Fin t → I × A) : Prop :=
  ∀ s : Fin t, (h s).1 ∈ legalI s (NondualOpt.histPrefix h s) ∧
    (h s).2 ∈ legalA s (NondualOpt.histPrefix h s) (h s).1

end DynHaussler


