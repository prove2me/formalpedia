-- Prove2me | Definitions.Def_BlockSSM_wordProd
-- name    : BlockSSM_wordProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:26.932062+00:00
-- url     : https://prove2.me/theorems/07d17d6d-8488-4d96-be34-181a7eb38eca
-- title:
--   Running product $\pi(s)=g_T\cdots g_1$ of a word
-- statement:
--   For a word $s=g_1\cdots g_T$ over a group $G$, the **running product** is
--   $$
--   \pi(s)=g_T\cdots g_1,
--   $$
--   the later letter multiplying on the left. The empty word has product $1$. This is the quantity a tracker has to report after every prefix.
--
--   **Formalization Note** A word is a list with $g_1$ at the head, so $\pi(s)$ is the product of the reversed list.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3)

import Mathlib

universe u

namespace BlockSSM

/-- **The running product of a word.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 1, p.2 (PDF p.3): "π(s) = g_T ⋯ g₁ for a
word s = g₁ ⋯ g_T".

**Formalization Note.** A word is a `List G` with `g₁` at the head, so `π(s)` is the product of the
reversed list: the later letter multiplies on the left. The empty word has product `1`. -/
def wordProd {G : Type u} [Group G] (s : List G) : G := s.reverse.prod

end BlockSSM


