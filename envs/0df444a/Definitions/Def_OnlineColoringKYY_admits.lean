-- Prove2me | Definitions.Def_OnlineColoringKYY_admits
-- name    : OnlineColoringKYY_admits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:30.413196+00:00
-- url     : https://prove2.me/theorems/15f6621d-feb3-4797-bdd1-3db6da8375ed
-- title:
--   Admissible base colors $X_v$ of the Section 4.2 adversary
-- statement:
--   Fix $\ell \ge 0$. In the adversary of Section 4.2 every arriving vertex $v$ receives an **admissible set of base colors** $X_v \subseteq \{0, 1, \dots, 2\ell-1\}$ that contains, for each $s \in \{0, \dots, \ell-1\}$, exactly one of the two base colors $2s$ and $2s+1$. Such a set is described by a binary code $x_v \in \{0,1\}^\ell$:
--   $$
--   X_v = \{\, 2s + x_v(s) \;:\; 0 \le s < \ell \,\}.
--   $$
--
--   **Formalization Note** Base colors are 0-indexed: the pair $s$ consists of $2s, 2s+1$, which are the paper's $2s-1, 2s$ for $s \in \{1, \dots, \ell\}$. The codes are given by a function `code : ℕ → Fin ℓ → Bool` on arrival indices.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace OnlineColoringKYY

/-- The **admissible set of base colors** `X_v` of vertex `v` (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary
algorithm", printed p.13 = PDF p.15): `b ∈ X_v` iff `b = 2s + code v s` for some `s < ℓ`. So for
every `s < ℓ`, `X_v` holds exactly one of the two base colors `2s, 2s + 1`.

**Formalization Note** Base colors are 0-indexed: the pair `s ∈ Fin ℓ` has base colors `2s` and
`2s + 1`, the paper's `2s − 1` and `2s` for `s ∈ {1, …, ℓ}`. The choice of `X_v` is encoded by a
code `code : ℕ → Fin ℓ → Bool` indexed by the arrival index `v`: `code v s = false` puts `2s` in
`X_v`, `code v s = true` puts `2s + 1` in it. -/
def admits {ℓ : ℕ} (code : ℕ → Fin ℓ → Bool) (v b : ℕ) : Prop :=
  ∃ s : Fin ℓ, b = 2 * s.val + (code v s).toNat

end OnlineColoringKYY


