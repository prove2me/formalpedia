-- Prove2me | Definitions.Def_DoublyEffIP_msgs
-- name    : DoublyEffIP_msgs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:50.818567+00:00
-- url     : https://prove2.me/theorems/19a0ffd5-5034-4fa6-906c-23493e8cca0c
-- title:
--   A message sequence as a list of words
-- statement:
--   A sequence of $\ell$ messages $m_0,\dots,m_{\ell-1}$, each a bit string of length exactly $a$, is listed as the words $(m_0,\dots,m_{\ell-1})$. This is how query sequences $q$ and answer sequences $P(x,q)$ are written on the machines' tapes.
--
--   **Formalization Note** Rounds are numbered from $0$: the paper's round $j\in[\ell]$ is index $j-1$. Equal message length is built into the type of messages.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, p.11

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP

/-- **A message sequence as a list of words** — the sequences `q = (q_1, …, q_ℓ)` and
`P(x, q) = (a_1, …, a_ℓ)` of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*,
arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, p.11.

`msgs m` lists the messages `m 0, …, m (ℓ-1)`, each of length `a`, as bit words.

**Formalization Note.** Rounds are indexed from `0`; the paper's round `j ∈ [ℓ]` is index `j - 1`.
"Both parties send messages of equal length" (p.11) is built into the type `List.Vector Bool a`. -/
def msgs {ℓ a : ℕ} (m : Fin ℓ → List.Vector Bool a) : List (List Bool) :=
  List.ofFn fun j => (m j).toList

end DoublyEffIP


