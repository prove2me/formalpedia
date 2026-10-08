-- Prove2me | Definitions.Def_TrulySubcubicAPSP_Problems
-- name    : TrulySubcubicAPSP_Problems
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T05:01:21.371039+00:00
-- url     : https://prove2.me/theorems/cc20ddd0-5f5f-4ba9-85d0-87d794a7f1b6
-- title:
--   Exact Triangle, min-plus product, and APSP specifications
-- statement:
--   Three weighted problems share the same word-RAM interface. Exact Triangle takes three $n\times n$ integer matrices and accepts exactly when some $a,b,c$ satisfy $w_{AB}(a,b)+w_{BC}(b,c)+w_{AC}(a,c)=0$. The constant $\varepsilon_T$ is the exact rational $0.0017$. The $(\min,+)$-product takes two integer matrices and outputs $C_{ij}=\min_k(A_{ik}+B_{kj})$, requiring each output to be an attained lower bound of the candidate sums.
--
--   For APSP, the vertex set is $\{0,\ldots,n-1\}$ and each ordered pair has either an integer edge weight or no edge. Paths are finite directed walks, including empty paths of weight zero. Inputs must satisfy
--   $$\forall i\;\forall d,\qquad \text{there is a closed walk at }i\text{ of weight }d\;\Longrightarrow\;0\le d.$$
--   The input stores the edge-presence matrix and weight matrix row by row. Each output pair has a reachability flag followed by a signed distance. A flag of one requires an actual path attaining that distance and no path of smaller weight. A flag of zero requires no path at all, with the distance cell unconstrained. Both function problems always accept, including the empty instance, where there are no output entries. Missing edges and zero-weight edges remain distinct.
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/EndStatement.lean; lines 75–82, 98–103, 109–122; namespace renamed only; Apache-2.0.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TrulySubcubicAPSP

/-- Section 3.2: «S(a, b, c) := w(a, b) + w(b, c) + w(a, c). A zero triangle is a triangle … with S(a, b, c) = 0». -/
def ExactTriangle : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (wAB, wBC, wAC) => rowByRow wAB ++ rowByRow wBC ++ rowByRow wAC
  yes := fun (wAB, wBC, wAC) => ∃ a b c, wAB a b + wBC b c + wAC a c = 0

/-- Theorem 19: «ε_T := 0.0017». -/
def ε_T : Rat := 0.0017


/-- Output, row by row: entry `(i, j)` is the least of the sums `A i k + B k j`. -/
def MinPlusProduct : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (A, B) => rowByRow A ++ rowByRow B
  output := fun {n} (A, B) out => ∀ i j : Fin n,
    (∃ k, out (i.val * n + j.val) = A i k + B k j) ∧ ∀ k, out (i.val * n + j.val) ≤ A i k + B k j


/-- A path and its total weight; it may repeat vertices. -/
inductive Path {n : Nat} (w : Fin n → Fin n → Option Int) : Fin n → Fin n → Int → Prop
  | nil (i : Fin n) : Path w i i 0
  | cons {i j k : Fin n} {d e : Int} : w i j = some d → Path w j k e → Path w i k (d + e)

/-- Input: the 0/1 matrix of the edges, then the weights, with 0 for no edge. Output, two cells for each `(i, j)`: 1 if
there is a path, else 0; then the distance. -/
def APSP : Problem where
  Instance n := {w : Fin n → Fin n → Option Int // ∀ i d, Path w i i d → 0 ≤ d}
  input := fun ⟨w, _⟩ => rowByRow (fun i j => if (w i j).isSome then 1 else 0) ++ rowByRow fun i j => (w i j).getD 0
  output := fun {n} ⟨w, _⟩ out => ∀ i j : Fin n,
    let flag := out (2 * (i.val * n + j.val))
    let dist := out (2 * (i.val * n + j.val) + 1)
    (flag = 1 ∧ Path w i j dist ∧ ∀ e, Path w i j e → dist ≤ e) ∨ (flag = 0 ∧ ∀ e, ¬ Path w i j e)

end TrulySubcubicAPSP


