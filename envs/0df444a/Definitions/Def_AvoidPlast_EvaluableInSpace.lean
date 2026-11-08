-- Prove2me | Definitions.Def_AvoidPlast_EvaluableInSpace
-- name    : AvoidPlast_EvaluableInSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:04.816486+00:00
-- url     : https://prove2.me/theorems/e12eaef9-4e33-4bf6-9653-e3e5d8355cec
-- title:
--   Families evaluable in space $O(S(n))$
-- statement:
--   An indexed family $C=\{C_x\}_{x\in\{0,1\}^*}$ with $C_x:\{0,1\}^{\ell_{in}(|x|)}\to\{0,1\}^{\ell_{out}(|x|)}$ is **evaluable in space $O(S(n))$** if $C_x(y)$ has length $\ell_{out}(|x|)$ whenever $|y|=\ell_{in}(|x|)$, and a machine that gets $(x,y,i)$ with $|y|=\ell_{in}(|x|)$ and $i<\ell_{out}(|x|)$ (in binary) halts and prints the $i$-th output bit of $C_x(y)$ within work space $K(S(|x|)+1)$.
--
--   **Formalization Note** The size $s$ of the paper's circuits is arbitrary in the theorems that use this notion, so a family is a map on strings (reading R8). The lengths are not required to be computable here: the machine sees $y$ and $i$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definitions 3.1 and 3.3, p.14

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Halts
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_workSpace

namespace AvoidPlast

/-- An indexed family `C = {C_x}` with `C_x : {0,1}^{ℓin(|x|)} → {0,1}^{ℓout(|x|)}` that is evaluable in
space `O(S(n))` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definitions 3.1 and 3.3, p.14): `C_x(y)` has length `ℓout(|x|)`, and a machine
that gets `(x, y, i)` with `i < ℓout(n)` in binary prints the `i`-th output bit of `C_x(y)` within
work space `K · (S(n) + 1)`.

**Formalization Note** Reading R8: `s(·)` is arbitrary in the theorems that use this notion, so the
circuits and their sizes add nothing to a map. Reading R2: "space `S(n)`" is `O(S(n))`. -/
def EvaluableInSpace (C : List Bool → List Bool → List Bool) (ℓin ℓout : ℕ → ℕ) (S : ℕ → ℝ) :
    Prop :=
  (∀ x y : List Bool, y.length = ℓin x.length → (C x y).length = ℓout x.length) ∧
    ∃ (M : Machine 3) (K : ℝ), ∀ (x y : List Bool) (i : ℕ),
      y.length = ℓin x.length → i < ℓout x.length →
        Halts M ![x, y, Nat.bits i] ∧
        output M ![x, y, Nat.bits i] = [(C x y).getD i false] ∧
        (workSpace M ![x, y, Nat.bits i] : ℝ) ≤ K * (S x.length + 1)

end AvoidPlast


