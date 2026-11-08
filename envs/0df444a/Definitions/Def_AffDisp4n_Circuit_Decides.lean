-- Prove2me | Definitions.Def_AffDisp4n_Circuit_Decides
-- name    : AffDisp4n_Circuit_Decides
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:39.248565+00:00
-- url     : https://prove2.me/theorems/bdef8e33-1cc9-44a8-b662-abdab4115eeb
-- title:
--   A $B_2$-circuit decides a language on inputs of length $n$
-- statement:
--   A $B_2$-circuit $C$ on $n$ inputs **decides the language $L \subseteq \{0,1\}^*$ on inputs of length $n$** if, for every $x \in \{0,1\}^n$,
--   $$
--   C(x) = 1 \iff x \in L .
--   $$
--   A Boolean function in $\mathbf P$ requires circuits of size $S(n)$ when every circuit deciding its language on length $n$ has at least $S(n)$ gates.
--
--   **Formalization Note** The string $x$ is `List.ofFn x`, and the circuit receives the bits as elements of $\mathbb F_2$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §1.2, p.2

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_ofBool

namespace AffDisp4n

/-- A B₂-circuit `C` on `n` inputs **decides the language `L ⊆ {0,1}*` on inputs of length `n`**
(Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §1.2, p.2: "a Boolean function in P which requires B₂ circuits of size …"): for every
`x ∈ {0,1}ⁿ`, `C(x) = 1` if and only if the string `x` belongs to `L`.

**Formalization Note** A string of length `n` is `List.ofFn x` for `x : Fin n → Bool`. The circuit
runs on `𝔽₂`, and the input bit `xᵢ` is fed as `ofBool xᵢ`. -/
def Circuit.Decides {n : ℕ} (C : Circuit n) (L : Language Bool) : Prop :=
  ∀ x : Fin n → Bool, C.eval (fun i => ofBool (x i)) = 1 ↔ List.ofFn x ∈ L

end AffDisp4n


