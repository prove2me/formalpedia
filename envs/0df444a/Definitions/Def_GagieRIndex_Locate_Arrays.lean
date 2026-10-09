-- Prove2me | Definitions.Def_GagieRIndex_Locate_Arrays
-- name    : GagieRIndex_Locate_Arrays
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:00.110825+00:00
-- url     : https://prove2.me/theorems/cd0a90db-0c43-487b-ac58-1e0ee5d13b0a
-- title:
--   Definition 2, p. 12; §5.2, p. 20; §5.3, p. 22 — the permutation φ and the differential arrays DSA, DISA
-- statement:
--   The **differential suffix array** and the **differential inverse suffix array** record consecutive differences:
--   $$DSA[p]=\begin{cases}SA[1],&p=1,\\SA[p]-SA[p-1],&p>1,\end{cases}\qquad DISA[i]=\begin{cases}ISA[1],&i=1,\\ISA[i]-ISA[i-1],&i>1.\end{cases}$$
--   The permutation $\phi$ of Definition 2 sends a text position to the text position stored in the preceding suffix-array cell:
--   $$\phi(i)=\begin{cases}SA[ISA[i]-1],&ISA[i]>1,\\SA[n],&\text{otherwise.}\end{cases}$$
--   So if $i=SA[p]$ with $p>1$, then $\phi(i)=SA[p-1]$.
--
--   The runs of the BWT induce repeated blocks in $DSA$ (Lemma 12), and phrases of $ISA$ induce repeated blocks in $DISA$ via $\phi$ (Lemma 14).
--
--   **Formalization Note** $DSA$ and $DISA$ take integer values, since differences of suffix-array cells can be negative. The argument $0$ is treated like $1$.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 12, Definition 2; p. 20, §5.2; p. 22, §5.3

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

namespace GagieRIndex.Locate

/-- The differential suffix array: `DSA[p] = SA[p] − SA[p − 1]` for `p > 1`, `DSA[1] = SA[1]`
(§5.2, p. 20). -/
def DSA (SA : ℕ → ℕ) (p : ℕ) : ℤ :=
  if p ≤ 1 then (SA 1 : ℤ) else (SA p : ℤ) - SA (p - 1)

/-- The differential inverse suffix array: `DISA[i] = ISA[i] − ISA[i − 1]` for `i > 1`,
`DISA[1] = ISA[1]` (§5.3, p. 22). -/
def DISA (n : ℕ) (SA : ℕ → ℕ) (i : ℕ) : ℤ :=
  if i ≤ 1 then (ISA n SA 1 : ℤ) else (ISA n SA i : ℤ) - ISA n SA (i - 1)

/-- The permutation `φ` (Definition 2, p. 12): `φ(i) = SA[ISA[i] − 1]` if `ISA[i] > 1`, and
`φ(i) = SA[n]` otherwise. -/
def phi (n : ℕ) (SA : ℕ → ℕ) (i : ℕ) : ℕ :=
  if 1 < ISA n SA i then SA (ISA n SA i - 1) else SA n

end GagieRIndex.Locate


