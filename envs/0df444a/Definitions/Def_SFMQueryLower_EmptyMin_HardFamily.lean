-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_HardFamily
-- name    : SFMQueryLower_EmptyMin_HardFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:55.000793+00:00
-- url     : https://prove2.me/theorems/a35c2c3e-ef22-4b91-b9f6-018efbaf93af
-- title:
--   The explicit layered hard functions and stopping layers
-- statement:
--   For an ordered partition $\Pi$ and a bit $b\in\{0,1\}$, Definition 2.2 fixes $w_1=1$, $w_i=w_{i-1}|V_{i-1}|^2$, and $g_{b,0}(\varnothing)=b-1$. Recursively,
--   $$g_{b,i}(S)=\begin{cases}w_i|V_i||V_i\setminus S|&S\cap R_i\ne\varnothing,\\ w_i|S|&S\cap R_i=\varnothing,\ P_i\nsubseteq S,\\ g_{b,i-1}(S\setminus P_i)&S\cap R_i=\varnothing,\ P_i\subseteq S.\end{cases}$$
--   Set $f_b^\Pi=g_{b,k}$. A layer passes when its bad block is avoided and its good block is included. The stopping layer is the largest failed layer, or zero when all layers pass; equivalently it is the minimum index above which all layers pass.
--
--   **Formalization Note** The recursive values and base subtraction are integers, then embedded in the exact real oracle. The helper uses zero-based weight indices and intersects with $V_i$ outside its intended domain; on $S\subseteq V_i$, $0\le i\le k$, it is the displayed recurrence. The guard beyond layer $k$ is never reached by the top-level construction. No desired hard-family property is an assumed field.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Definition 2.2, printed p. 7 / PDF p. 8; stopping-layer definition, §3.1, printed p. 9 / PDF p. 10

import Definitions.Def_SFMQueryLower_EmptyMin_OrderedPartition

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- `layerWeight π j` is the source's `w_{j+1}`: `w₁ = 1`,
`w_{i+1} = w_i |V_i|²`. It is computed from the partition, not a parameter. -/
def layerWeight {n k : ℕ} (π : OrderedPartition n k) : ℕ → ℕ
  | 0 => 1
  | j + 1 => layerWeight π j * (remainingGround π (j + 1)).card ^ 2

/-- Definition 2.2. Only `0 ≤ i ≤ k` is used; intersection with `V_i` extends
the inner function outside its domain harmlessly. The branch `j ≥ k` is unused.
Integer subtraction is essential in the base case. -/
def hardAux {n k : ℕ} (π : OrderedPartition n k) (b : Bool) :
    ℕ → Finset (Fin n) → ℤ
  | 0, _ => (if b then (1 : ℤ) else 0) - 1
  | j + 1, S =>
    if hj : j < k then
      let J : Fin k := ⟨j, hj⟩
      let V := remainingGround π (j + 1)
      let T := S ∩ V
      if ¬ Disjoint T (badBlock π J) then
        (layerWeight π j : ℤ) * V.card * (V \ T).card
      else if ¬ goodBlock π J ⊆ T then
        (layerWeight π j : ℤ) * T.card
      else hardAux π b j (T \ goodBlock π J)
    else 0

def hardFunction {n k : ℕ} (π : OrderedPartition n k) (b : Bool)
    (S : Finset (Fin n)) : ℝ := (hardAux π b k S : ℝ)

/-- Largest failed source layer, or `0` if all layers pass. This equals §3.1's
minimum index above which all layers pass, and involves no empty-minimum default. -/
def stopLayer {n k : ℕ} (π : OrderedPartition n k) (S : Finset (Fin n)) : ℕ :=
  Finset.univ.sup (fun j : Fin k =>
    if Disjoint S (badBlock π j) ∧ goodBlock π j ⊆ S then 0 else j.val + 1)

end SFMQueryLower.EmptyMin


