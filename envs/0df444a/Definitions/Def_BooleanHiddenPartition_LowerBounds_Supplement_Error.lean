-- Prove2me | Definitions.Def_BooleanHiddenPartition_LowerBounds_Supplement_Error
-- name    : BooleanHiddenPartition_LowerBounds_Supplement_Error
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:13:57.529127+00:00
-- url     : https://prove2.me/theorems/59881fd5-3077-40f2-bca4-27131b07c580
-- title:
--   Worst-case error for hidden-partition protocols
-- statement:
--   Fix an admissible layout with positive integers $k,n,m$, $\alpha\in(0,1)$ and $km=\alpha n$, and a Boolean function $f$ on $k$ signs. Alice receives $x$, and Bob receives $B=(\sigma,y)$, with the ordered-block promise from the published problem definition. For a private-coin classical protocol or an unassisted quantum strategy, write $a(x,B)$ for its YES probability. Solving with error $\varepsilon$ means
--
--   $$\forall x,B,b\text{ satisfying the promise},\quad
--   1-\varepsilon\le\begin{cases}a(x,B)&b=\mathrm{YES},\\1-a(x,B)&b=\mathrm{NO}.\end{cases}$$
--
--   This is a guarantee on every promised input, with randomness only inside the protocol. The quantum predicate uses the published density-state and effect model directly, with no public seed or entanglement. These predicates allow arbitrary error parameters rather than fixing success at $2/3$. The theorems use them only for $0<\varepsilon<1/2$.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, Characterizing Quantum Advantage for Generalizations of the Boolean Hidden Matching Problem, STOC 2027 submission #1085 (October 2026), pp. 25, 27, success requirements in Theorems 12 and 13; pp. 3, 12, ordered-block promise

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Problem
import Definitions.Def_BooleanHiddenPartition_LowerBounds_Supplement_PrivateCoin

set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds.Supplement

/-- Worst-case success at least 1 - ε, on every promised classical input. -/
def ClassicalSolvesWithError {k n m c : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (P : PrivateCoinProtocol (Cube n) (BobInput n m) c)
    (ε : ℝ) : Prop :=
  ∀ x B b, Promised L f x B b →
    1 - ε ≤ correctProb (privateAccept P x B) b

/-- Worst-case success for one unassisted quantum message: no public seed. -/
def QuantumSolvesWithError {k n m c : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (P : QuantumStrategy (Cube n) (BobInput n m) c)
    (ε : ℝ) : Prop :=
  ∀ x B b, Promised L f x B b →
    1 - ε ≤ correctProb (quantumAccept P x B) b

end BooleanHiddenPartition.LowerBounds.Supplement


