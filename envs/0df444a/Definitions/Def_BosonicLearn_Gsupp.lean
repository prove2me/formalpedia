-- Prove2me | Definitions.Def_BosonicLearn_Gsupp
-- name    : BosonicLearn_Gsupp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:33.3288+00:00
-- url     : https://prove2.me/theorems/aa9440de-fad7-4f5e-9332-0e3a7dc9d875
-- title:
--   $G_{\mathrm{supp}}=\{X\in\mathrm{Herm}_0(n):\|X\|_{\mathrm{op}}\le4\}$
-- statement:
--   $$G_{\mathrm{supp}}=\{X\in\mathrm{Herm}_0(n):\ \|X\|_{\mathrm{op}}\le 4\}.$$
--
--   It is the support of the prior $\mu$ in the lower-bound construction.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30

import Mathlib
import Definitions.Def_BosonicLearn_Herm0
import Definitions.Def_WHMultiplicativity_schattenNorm

namespace BosonicLearn

/-- **`G_supp = {X ∈ Herm₀(n) : ‖X‖_op ≤ 4}`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "Also define G_supp := {X ∈ Herm_0(n) : ‖X‖_op ≤ 4}". It is the support of the prior.

**Formalization Note.** `‖·‖_op` is the published `WHMultiplicativity.schattenNorm ⊤`, the operator norm on `ℂⁿ`. -/
def Gsupp (n : ℕ) : Set (Herm0 n) :=
  {X | WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ 4}

end BosonicLearn


