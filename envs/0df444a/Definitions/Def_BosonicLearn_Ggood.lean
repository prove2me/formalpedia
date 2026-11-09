-- Prove2me | Definitions.Def_BosonicLearn_Ggood
-- name    : BosonicLearn_Ggood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:38.854085+00:00
-- url     : https://prove2.me/theorems/517a950a-f9ea-4298-aae8-8bee3bab70ab
-- title:
--   $G_{\mathrm{good}}=\{X\in\mathrm{Herm}_0(n):\|X\|_{\mathrm{op}}\le3\}$
-- statement:
--   $$G_{\mathrm{good}}=\{X\in\mathrm{Herm}_0(n):\ \|X\|_{\mathrm{op}}\le 3\}.$$
--
--   Ground-truth parameters in $G_{\mathrm{good}}$ stay inside $G_{\mathrm{supp}}$ under the small perturbations used in the posterior argument.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30

import Mathlib
import Definitions.Def_BosonicLearn_Herm0
import Definitions.Def_WHMultiplicativity_schattenNorm

namespace BosonicLearn

/-- **`G_good = {X ∈ Herm₀(n) : ‖X‖_op ≤ 3}`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "G_good := {X ∈ Herm_0(n) : ‖X‖_op ≤ 3}".

**Formalization Note.** `‖·‖_op` is the published `WHMultiplicativity.schattenNorm ⊤`, the operator norm on `ℂⁿ`. -/
def Ggood (n : ℕ) : Set (Herm0 n) :=
  {X | WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ 3}

end BosonicLearn


