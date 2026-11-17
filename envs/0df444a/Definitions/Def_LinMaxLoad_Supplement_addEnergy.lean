-- Prove2me | Definitions.Def_LinMaxLoad_Supplement_addEnergy
-- name    : LinMaxLoad_Supplement_addEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:21:12.757908+00:00
-- url     : https://prove2.me/theorems/1656e0ed-c39a-459f-9ece-200f472c5579
-- title:
--   Additive energy $E(S)$
-- statement:
--   For a finite subset $S$ of an abelian group $G$, the **additive energy** of $S$ is the number of additive quadruples in $S$:
--
--   $$
--   E(S) := \bigl|\{(a,b,c,d) \in S^4 : a + b = c + d\}\bigr|.
--   $$
--
--   It always satisfies $|S|^2 \le E(S) \le |S|^3$ (for nonempty $S$), and cubic energy $E(S) = \Omega(|S|^3)$ is the weakest of the notions of additive structure compared in the paper.
--
--   **Formalization Note** $E(S)$ is a natural number, counted over ordered quadruples, as printed.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Definition 2, item 2, p.3

import Mathlib

namespace LinMaxLoad.Supplement

/-- **Additive energy** `E(S) := |{(a, b, c, d) ∈ S⁴ : a + b = c + d}|` (Definition 2, item 2,
p.3, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)),
the number of additive quadruples of the finite set `S`. -/
def addEnergy {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G) : ℕ :=
  ((S ×ˢ S ×ˢ S ×ˢ S).filter fun x => x.1 + x.2.1 = x.2.2.1 + x.2.2.2).card

end LinMaxLoad.Supplement


