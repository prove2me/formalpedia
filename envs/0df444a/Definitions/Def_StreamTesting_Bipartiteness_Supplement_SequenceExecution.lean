-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceExecution
-- name    : StreamTesting_Bipartiteness_Supplement_SequenceExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:58:25.661239+00:00
-- url     : https://prove2.me/theorems/5db688ab-6efd-4cf2-8fbe-07429d660ab7
-- title:
--   Actual sequence execution and query count
-- statement:
--   Execution starts with every slot absent and processes indices $0,\ldots,m-1$ exactly once in order. At index $i$ the policy sees only its preceding history and $i$. The execution reads $f(i)$ only if the policy queries; otherwise it records a skip. It never revisits an index.
--
--   $$\mathrm{output}(f,A)=A_{\mathrm{output}}(\mathrm{finalHistory}),\qquad\mathrm{queries}=\#\{i:\mathrm{history}(i)\text{ records a queried real value}\}.$$
--
--   The execution freezes after $m$ arrivals. Future values and skipped values cannot enter the observed history.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1, printed/PDF p.3; §§5–6, printed/PDF pp.26–36.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequencePolicy

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def seqRunPrefix {m : ℕ} {α : Type} (f : Fin m → ℝ) (A : SeqPolicy m α) :
    ℕ → SeqHistory m
  | 0 => fun _ => none
  | t + 1 =>
    let h := seqRunPrefix f A t
    if ht : t < m then
      let i : Fin m := ⟨t, ht⟩
      let ans := if A.1 h i then some (f i) else none
      Function.update h i (some ans)
    else h

def seqExecute {m : ℕ} {α : Type} (f : Fin m → ℝ) (A : SeqPolicy m α) : SeqHistory m :=
  seqRunPrefix f A m

def seqOutput {m : ℕ} {α : Type} (f : Fin m → ℝ) (A : SeqPolicy m α) : α :=
  A.2 (seqExecute f A)

def seqQueryCount {m : ℕ} (h : SeqHistory m) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ∃ x : ℝ, h i = some (some x)).card

end StreamTesting.Bipartiteness.Supplement


