-- Prove2me | Definitions.Def_CompNonlocal_Certificate_bobAccEffect
-- name    : CompNonlocal_Certificate_bobAccEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:17.529576+00:00
-- url     : https://prove2.me/theorems/25aee46f-b4af-4737-9262-c226dda79918
-- title:
--   Averaged acceptance effect on Bob's qubit
-- statement:
--   For a question outcome $o=(x,y)$ and Alice's answer $a$, the positive operator on Bob's qubit
--   $$\widetilde W_{o,a}=\sum_b\Pr[o,\ \mathrm{Val}\text{ accepts }(a,b,x,y)]\;B^y_b .$$
--   Summed over the outcomes $o$ with question $x$, it equals $\Pr[X=x]\,W_{x,a}$, where $W_{x,a}=\operatorname{Tr}_S\big(F_{x,a}(I_B\otimes\omega_{S|x})\big)$ is the paper's averaged qubit effect.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 13, Eq. (17), pp.30–31

import Mathlib
import Definitions.Def_CompNonlocal_Certificate
import Definitions.Def_CompNonlocal_ICirc_qubitEffect

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The averaged acceptance effect on Bob's qubit, unnormalized, for one question outcome. Głuch,
Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC
2027 submission, sha256 e245edd7…), Definition 13, pp.30–31: `F_{x,a}` is "the acceptance effect on
Bob's input qubit register B and on S of the test that runs B on Bob's input qubit and the question
y, obtains b, and accepts when Val(a, b, x, y, td) < 0", and `W_{x,a} := Tr_S(F_{x,a}(I_B ⊗ ω_{S|x}))`
(Eq. (17)).

**Formalization Note** For the question outcome `o = x ++ y` and Alice's answer `a`, this is
`Σ_b Pr[o, Val accepts a, b] · B^y_b`, a positive operator on Bob's qubit. Summing it over the
outcomes `o` with `o.take (lx κ) = x` gives `Pr[x] · W_{x,a}` (the conditioning on `X = x` multiplied
out). -/
noncomputable def Certificate.bobAccEffect (c : Certificate) (κ : ℕ) (o a : Str) :
    Matrix Bool Bool ℂ :=
  ∑ b : Bits (c.B κ).outC.length,
    (c.valAccept κ a (List.ofFn b) o : ℂ) •
      (c.B κ).qubitEffect (o.drop (c.lx κ)) (fun t => decide (t = List.ofFn b))

end CompNonlocal


