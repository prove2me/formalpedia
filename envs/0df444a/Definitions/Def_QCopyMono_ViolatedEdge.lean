-- Prove2me | Definitions.Def_QCopyMono_ViolatedEdge
-- name    : QCopyMono_ViolatedEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:01.294769+00:00
-- url     : https://prove2.me/theorems/a3241d63-3557-40ce-a18d-9cc4f15fa590
-- title:
--   Violated edges $E^-_f$ and the colored count $I^-_{f,\mathrm{col}}(x)$
-- statement:
--   For $f:\{0,1\}^n\to\{0,1\}$, the set of **violated edges** is
--   $$
--   E^-_f=\big\{\{x,y\}: x\preceq y,\ |y|-|x|=1,\ f(x)=1,\ f(y)=0\big\},
--   $$
--   where $|x|=\sum_i x_i$ is the Hamming weight. For a coloring $\mathrm{col}:E^-_f\to\{\text{red},\text{blue}\}$, $I^-_{f,\mathrm{col}}(x)$ counts the red edges incident on $x$ if $f(x)=1$ and the blue edges incident on $x$ if $f(x)=0$, so each violated edge is counted at exactly one endpoint.
--
--   These objects enter the directed isoperimetric inequality (Theorem 4) and the degree-removal lemma (Lemma 5).
--
--   **Formalization Note** An edge is stored as its ordered pair (lower endpoint, upper endpoint). A coloring is any function of such pairs (`true` = red) and is read only on violated edges; every coloring of $E^-_f$ is of this form.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.2.1, p.11, eq. (10) and the definition of I^-_{f,col}

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QCopyMono

open QAlgorithms

/-! # Violated edges and the colored count `I⁻_{f,col}`

P. Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.2.1, p.11, eq. (10).

**Formalization Note.** An edge `{x, y}` of `E⁻_f` is stored as the ordered pair
`(lower endpoint, upper endpoint)`, which determines it. A coloring is a function
`col : Qubits n → Qubits n → Bool` with `true` = red, read only at the pairs `(x, y)` with
`ViolatedEdge f x y`: every coloring of `E⁻_f` arises this way, and values elsewhere are never
read. `|x|` is `QAlgorithms.hammingWeight`. -/

/-- p.11, eq. (10): `{x, y} ∈ E⁻_f` with lower endpoint `x`: `x ⪯ y`, `|y| − |x| = 1`,
`f(x) = 1`, `f(y) = 0`. -/
def ViolatedEdge {n : ℕ} (f : Qubits n → Bool) (x y : Qubits n) : Prop :=
  x ≤ y ∧ hammingWeight y = hammingWeight x + 1 ∧ f x = true ∧ f y = false

open Classical in
/-- p.11: `I⁻_{f,col}(x)`, the number of red edges of `E⁻_f` incident on `x` if `f(x) = 1`
(then `x` is the lower endpoint of each of its violated edges), and the number of blue edges
incident on `x` if `f(x) = 0` (then `x` is the upper endpoint). -/
noncomputable def inflMinus {n : ℕ} (f : Qubits n → Bool) (col : Qubits n → Qubits n → Bool)
    (x : Qubits n) : ℕ :=
  if f x = true then
    (Finset.univ.filter fun y => ViolatedEdge f x y ∧ col x y = true).card
  else
    (Finset.univ.filter fun y => ViolatedEdge f y x ∧ col y x = false).card

end QCopyMono


