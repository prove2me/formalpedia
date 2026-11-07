-- Prove2me | Definitions.Def_EffRobustLearn_IsContaminationAdversary
-- name    : EffRobustLearn_IsContaminationAdversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:43.810911+00:00
-- url     : https://prove2.me/theorems/e1725c23-a22a-45f5-9f7e-9333ca0604cc
-- title:
--   Bounded contamination of rate $\eta$ (Definition 1.1)
-- statement:
--   An adversary at rate $\eta$ for the target $c^\star$ receives $n$ clean examples $(x_i,c^\star(x_i))$ and replaces at most $\eta n$ of them by arbitrary labeled examples, giving the corrupted sample $\bar S_{\mathrm{inp}}$.
--
--   Both features and labels may be corrupted, and the adversary sees the whole clean sample.
--
--   **Formalization Note** An adversary is a function from the clean points to the corrupted sample, with the replacement counted index-wise, which keeps the instance identities of §2's sample conventions. It sees neither the reference sample nor the algorithm's randomness, and no measurability is required.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Definition 1.1, p.1 (PDF p.2)

import Mathlib

namespace EffRobustLearn

open Classical in
/-- Bounded contamination of rate `η`, Definition 1.1, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.1:
the adversary receives the clean labeled sample `(x_i, c⋆(x_i))_{i≤n}` and replaces at most `ηn` of its examples by arbitrary labeled examples.

**Formalization Note.** An adversary is a function `adv` from the clean points `s : Fin n → X` (the clean labels are computed from `c⋆`) to the corrupted sample
`S̄inp = adv s`, so it sees only the clean sample, not the reference sample and not the algorithm's randomness. The replacement is index-wise: `S̄inp i` differs from the clean example `i` at no
more than `ηn` indices, keeping the instance identities of §2's sample conventions. No measurability is required of `adv`.
-/
def IsContaminationAdversary {X : Type*} {n : ℕ} (η : ℝ) (cstar : X → Bool)
    (adv : (Fin n → X) → Fin n → X × Bool) : Prop :=
  ∀ s : Fin n → X,
    (((Finset.univ.filter fun i => adv s i ≠ (s i, cstar (s i))).card : ℕ) : ℝ) ≤ η * n

end EffRobustLearn


