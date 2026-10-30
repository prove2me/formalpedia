-- Prove2me | Definitions.Def_CoffmanMitrani_chain
-- name    : CoffmanMitrani_chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:19:34.685641+00:00
-- url     : https://prove2.me/theorems/247fe9cb-7c53-4b05-947b-d4ea63845249
-- title:
--   Chain of top-priority class sets
-- statement:
--   For an ordering $\sigma$ of the classes and $k = 0, \dots, M-1$, the set $\{\sigma(0), \sigma(1), \dots, \sigma(k)\}$ of the $k+1$ classes of highest priority. These are the sets $g_1 = \{i_1\}$, $g_2 = \{i_1,i_2\}$, …, $g_M = \{1,\dots,M\}$ of the proof of Lemma 2.
--
--   **Formalization Note** The paper's $g_{k+1}$ is the Lean `chain σ k`, with $\sigma(l) = i_{l+1}-1$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818 (proof of Lemma 2)

import Mathlib

namespace CoffmanMitrani

/-- **The chain of top-priority class sets of a priority order.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 818, proof of Lemma 2: "g1 = {i1}, g2 = {i1, i2}, ···, gM−1 = {i1, i2, ···, iM−1},
gM = {i1, i2, ···, iM} = {1, 2, ···, M}".

`chain σ k = {σ 0, σ 1, …, σ k}`, the `k + 1` classes of highest priority under `σ`.

**Formalization Note.** 0-based: the paper's `g_{k+1}` is `chain σ k`, with `σ l = i_{l+1} − 1`. -/
def chain {M : ℕ} (σ : Equiv.Perm (Fin M)) (k : Fin M) : Finset (Fin M) :=
  (Finset.univ.filter (· ≤ k)).image σ

end CoffmanMitrani


