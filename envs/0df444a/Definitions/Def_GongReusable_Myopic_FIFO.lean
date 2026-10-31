-- Prove2me | Definitions.Def_GongReusable_Myopic_FIFO
-- name    : GongReusable_Myopic_FIFO
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:22:51.086064+00:00
-- url     : https://prove2.me/theorems/b712d903-38c3-4d5e-bd08-954751ab92e5
-- title:
--   FIFO insertion and extraction with an empty-queue fallback
-- statement:
--   A FIFO queue is represented by a list in arrival order. Insertion appends an element at the rear. Extraction returns the head and removes it. If the list is empty, extraction returns a supplied fresh value and leaves the queue empty. This general list operation contains no probabilistic independence or distributional correctness assertion.
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), printed p. 12 / PDF p. 12

import Mathlib

namespace GongReusable.Myopic

/-- Append at the rear and remove at the front. An empty queue uses a fresh value. -/
def fifoPush {A : Type} (q : List A) (a : A) : List A := q ++ [a]

def fifoTake {A : Type} (q : List A) (fresh : A) : A × List A :=
  (q.headD fresh, q.tail)

end GongReusable.Myopic


