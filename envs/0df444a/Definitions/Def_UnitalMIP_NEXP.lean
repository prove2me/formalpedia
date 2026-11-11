-- Prove2me | Definitions.Def_UnitalMIP_NEXP
-- name    : UnitalMIP_NEXP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:19.199428+00:00
-- url     : https://prove2.me/theorems/2098ab66-b48e-4c51-a655-e70921d67da9
-- title:
--   The class NEXP (certificate form)
-- statement:
--   A language $L\subseteq\{0,1\}^*$ is in **NEXP** if there are a deterministic program $D$ and polynomials $P,Q$ such that, for every input $z$, $D$ halts within $2^{P(|z|)}$ steps on $(z,w)$ for every certificate $w$ with $|w|\le 2^{Q(|z|)}$, and
--
--   $$
--   z\in L\iff \exists\, w,\ |w|\le 2^{Q(|z|)},\ D \text{ accepts } (z,w).
--   $$
--
--   NEXP is the class of the dichotomy's first branch.
--
--   **Formalization Note** Programs, encodings and running times are those of the published MIPRE cost model; acceptance is halting with output $1$.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 1.1, p.4; Theorem 3.6, p.30

import Mathlib
import Definitions.Def_MIPRE_Foundations_ClassMIPStar

namespace UnitalMIP

open MIPRE MIPRE.Cost

/-- **NEXP** (arXiv:2609.39318, version of 2026-11-03, Theorem 1.1, p.4), in certificate form on the
cost model of the published MIPRE development: a language `L ⊆ {0,1}*` is in NEXP if there are a
closed program `D` and polynomials `P`, `Q` such that, for every input `z`, `D` halts within
`2^{P(|z|)}` steps on `(z, w)` for every certificate `w` of length at most `2^{Q(|z|)}`, and
`z ∈ L` if and only if `D` accepts `(z, w)` for some such `w`.

**Formalization Note** Programs, `encode`, `Prog.Runs` and `HaltsWithin` are those of the published
`MIPRE.Cost` model (programs on binary-tree data, a unit cost per rule). Acceptance is halting
with output `encode true`. This is the usual verifier characterization of nondeterministic
exponential time. -/
def NEXP (L : Set BitStr) : Prop :=
  ∃ (D : Prog) (P Q : Polynomial ℕ), D.WellScoped 1 ∧
    ∀ z : BitStr,
      (∀ w : BitStr, w.length ≤ 2 ^ Q.eval z.length →
        HaltsWithin D (encode (z, w)) (2 ^ P.eval z.length)) ∧
      (z ∈ L ↔ ∃ w : BitStr, w.length ≤ 2 ^ Q.eval z.length ∧
        ∃ t, D.Runs (encode (z, w)) (encode true) t)

end UnitalMIP


