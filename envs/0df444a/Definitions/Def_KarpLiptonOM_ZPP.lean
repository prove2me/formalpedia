-- Prove2me | Definitions.Def_KarpLiptonOM_ZPP
-- name    : KarpLiptonOM_ZPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:02.486934+00:00
-- url     : https://prove2.me/theorems/26a0ec5e-aa9d-461f-bcd6-a273d4c79c57
-- title:
--   $L \in \mathrm{ZPP}^A$ (zero error, output $L(x)$ or ?)
-- statement:
--   A language $L$ is in $\mathrm{ZPP}^A$ if there are a deterministic polynomial-time oracle machine $M$ and a polynomial $q$ such that for every input $x$ and every random string $r \in \{0,1\}^{q(|x|)}$ the output $M^A(x, r)$ is either the correct bit $L(x)$ or the symbol "?", and
--   $$
--   \Pr_{r \in \{0,1\}^{q(|x|)}}\bigl[M^A(x, r) = L(x)\bigr] \ge \tfrac12 .
--   $$
--   For a class $\mathcal C$ of languages, $\mathrm{ZPP}^{\mathcal C} = \bigcup_{A \in \mathcal C}\mathrm{ZPP}^A$.
--
--   **Formalization Note** The paper uses $\mathrm{ZPP}^{\mathrm{ONP}}$ without defining ZPP; this is the standard definition. Output $[1]$ means "$x \in L$", output $[0]$ means "$x \notin L$", any other output is "?".
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem 1, p.5; proof of Theorem A.4.5, p.31 (standard class)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_OracleTM_out
import Definitions.Def_KarpLiptonOM_countStr
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- `L ∈ ZPP^A` (zero-error probabilistic polynomial time with oracle `A`; standard, used without
definition in Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Theorem 1, p.5 and proof of Theorem A.4.5, p.31): a polynomial-time oracle
machine `M` and a polynomial `q` such that, on every `(x, r)` with `|r| = q(|x|)`, the output
`M^A(x, r)` is the bit `L(x)` or "?", and `Pr_r[M^A(x, r) = L(x)] ≥ 1/2`.

**Formalization Note** The bit `b` is the output string `[b]`; every other output string is "?".
The constant `1/2` is the standard one (the paper's proof gives `3/4`). -/
def ZPP (A L : Set (List Bool)) : Prop :=
  ∃ (M : OracleTM) (k : ℕ) (q : Polynomial ℕ), M.IsPolyTime k ∧ ∀ x : List Bool,
    (∀ r : List Bool, r.length = q.eval x.length →
      (M.out A k (tupleEnc [x, r]) = [true] → x ∈ L) ∧
      (M.out A k (tupleEnc [x, r]) = [false] → x ∉ L)) ∧
    2 ^ q.eval x.length ≤ 2 * countStr (q.eval x.length) (fun r =>
      (x ∈ L ∧ M.out A k (tupleEnc [x, r]) = [true]) ∨
      (x ∉ L ∧ M.out A k (tupleEnc [x, r]) = [false]))

end KarpLiptonOM


