-- Prove2me | Definitions.Def_SelectiveDPT_Qfun
-- name    : SelectiveDPT_Qfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:31.617707+00:00
-- url     : https://prove2.me/theorems/b12571b2-15b2-467d-b01d-a54144eb9ce1
-- title:
--   Worst-case quantum query complexity $Q_\varepsilon(f)$ of a function
-- statement:
--   For a function $f : D \to Y$ on a domain $D \subseteq X^\iota$, $Q_\varepsilon(f)$ is the worst-case quantum query complexity of the relation $\{(x, y) : f(x) = y\}$: the least number of phase-oracle queries of an algorithm that outputs $f(x)$ with probability at least $1-\varepsilon$ on every $x \in D$.
--
--   **Formalization Note** $f$ is a total function on $X^\iota$ and only its values on $D$ matter.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, p.10 (Q_ε)

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel

namespace SelectiveDPT

/-- The worst-case quantum query complexity `Q_ε(f)` of a function `f : D → Y` (arXiv:2609.26678,
§2.2, p.10), i.e. `Q_ε` of the relation `{(x, y) : f(x) = y}`.

**Formalization Note.** `f` is a total function on `X^n`, read only on the domain `D`. -/
noncomputable def Qfun {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (f : (ι → ZMod d) → Y) (ε : ℝ) : ℕ∞ :=
  Qrel D (fun x y => f x = y) ε

end SelectiveDPT


