-- Prove2me | Definitions.Def_HSElemKernel_decodeHash
-- name    : HSElemKernel_decodeHash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:50.632493+00:00
-- url     : https://prove2.me/theorems/07c4bfe1-5ae8-464e-b8a0-c2d4eb776ebd
-- title:
--   Strict decoder of a sampled hash pair
-- statement:
--   The **hash decoder** on $W = \{0, \dots, w-1\}$ reads the list
--   $$[\,B, q_2, t\,] \mathbin{+\!\!+} [\tilde h(0), \dots, \tilde h(w-1)] \mathbin{+\!\!+} [g_1(0), \dots, g_1(w-1), \dots, g_t(0), \dots, g_t(w-1)]$$
--   as the pair $\mathcal F = (\tilde h, \{g_1, \dots, g_t\})$, and rejects it when its length is not $3 + w + tw$ or a value of $\tilde h$ is at least $B$ or a value of some $g_r$ is at least $q_2$. It is the output format of the sampler of Lemma 4.2.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.2, p.9

import Mathlib
import Definitions.Def_HSElemKernel_TwoLevelHash

namespace HSElemKernel

/-- Read a list of numbers as elements of `Fin B`; `none` if some entry is `≥ B`. (Helper of
`decodeHash`.) -/
def toFinList (B : ℕ) (l : List ℕ) : Option (List (Fin B)) :=
  l.mapM (fun x => if h : x < B then some (⟨x, h⟩ : Fin B) else none)

/-- The strict decoder of a sampled pair `F = (h̃, H₂)` on `W = Fin w` (Sheng–Xiao,
arXiv:2609.06512, held version sha256 aca9c70e…, Lemma 4.2, p.9): the list
`[B, q₂, t] ++ [h̃(0), …, h̃(w−1)] ++ [g₀(0), …, g₀(w−1), …, g_{t−1}(0), …, g_{t−1}(w−1)]`
decodes to `F`, and to `none` when its length is not `3 + w + tw` or a value is out of range. -/
def decodeHash (w : ℕ) : List ℕ → Option (TwoLevelHash (Fin w))
  | B :: q2 :: t :: rest =>
      match toFinList B (rest.take w), toFinList q2 (rest.drop w) with
      | some hl, some gl =>
          if h1 : hl.length = w then
            if h2 : gl.length = t * w then
              some
                { B := B, q2 := q2, t := t
                  h := fun v => hl[v.1]'(by rw [h1]; exact v.2)
                  g := fun r v => gl[r.1 * w + v.1]'(by
                    rw [h2]
                    have hv := v.2
                    have hr := r.2
                    calc r.1 * w + v.1 < r.1 * w + w := by omega
                      _ = (r.1 + 1) * w := by ring
                      _ ≤ t * w := Nat.mul_le_mul_right _ hr) }
            else none
          else none
      | _, _ => none
  | _ => none

end HSElemKernel


