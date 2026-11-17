-- Prove2me | Definitions.Def_AvoidPlast_Supplement_altQ
-- name    : AvoidPlast_Supplement_altQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:49:36.260425+00:00
-- url     : https://prove2.me/theorems/e8413c4b-935b-4871-bdd2-e9165318b4bf
-- title:
--   Alternating quantifier prefix
-- statement:
--   For a predicate $P$ on $k$-tuples of strings, $\mathrm{altQ}_k(P)$ is
--   $$\exists w_1\,\forall w_2\,\exists w_3\cdots Q_k w_k\; P(w_1,\dots,w_k),$$
--   each $w_i$ of length at most a bound $b$. It is the acceptance condition of a $\Sigma_k$ machine.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 5.9, 5.11, pp.25–27

import Mathlib

namespace AvoidPlast.Supplement

/-- The alternating quantifier prefix of a `Σ_k` machine (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 5.9, 5.11,
pp.25–27): `altQ k true b P` is `∃ w₁ ∀ w₂ ∃ w₃ … P(w₁, …, w_k)`, every `w_i` of length at most
`b` (`true` = the next quantifier is `∃`). -/
def altQ : (k : ℕ) → Bool → ℕ → ((Fin k → List Bool) → Prop) → Prop
  | 0, _, _, P => P Fin.elim0
  | k + 1, true, b, P =>
      ∃ w : List Bool, w.length ≤ b ∧ altQ k false b (fun ws => P (Fin.cons w ws))
  | k + 1, false, b, P =>
      ∀ w : List Bool, w.length ≤ b → altQ k true b (fun ws => P (Fin.cons w ws))

end AvoidPlast.Supplement


