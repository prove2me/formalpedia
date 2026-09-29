-- Prove2me | Definitions.Def_Freiman_paddedCopies
-- name    : Freiman_paddedCopies
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:35:45.848056+00:00
-- url     : https://prove2.me/theorems/39294820-ebd8-4a55-a1ca-e94bc6bd8bf7
-- title:
--   Concatenation of padded finite models
-- statement:
--   PaddedCopies describes the concatenation of the model windows [-2j,2j], with constant left extension. Window j starts at j(2j−1); its length is 4j+1. Existence, window classification, and convergence are separate open goals.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_wordRealization

namespace Freiman

def paddedStart (j : ℕ) : ℕ := j * (2 * j - 1)

def PaddedCopies (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+) : Prop :=
  (∀ i : ℤ, i < 0 → b i = d) ∧
  (∀ j k : ℕ, k ≤ 4 * j →
    b ((paddedStart j + k : ℕ) : ℤ) = a j ((k : ℤ) - ((2 * j : ℕ) : ℤ)))

end Freiman


