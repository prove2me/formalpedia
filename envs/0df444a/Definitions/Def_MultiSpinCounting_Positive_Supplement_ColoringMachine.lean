-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Supplement_ColoringMachine
-- name    : MultiSpinCounting_Positive_Supplement_ColoringMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:52.054935+00:00
-- url     : https://prove2.me/theorems/ec0cd156-9122-4638-a40f-b9b890944bb7
-- title:
--   Graph serialization and the uniform machine event for counting colorings
-- statement:
--   Let $N(G,q)=|\Omega(G,q)|$ count all proper assignments of colors in $[q]$ to the labeled graph $G$. This uses the published proper list-coloring set with every list equal to $[q]$.
--   The graph serialization records $n$, the edge count, and all pairs $i<j$ forming edges in lexicographic order, with binary integer encodings and separators. A tolerance $\varepsilon$ is a rational encoded in binary. The input is the graph serialization, a separator, and the tolerance encoding. No coloring, count, or other computed quantity is part of the input.
--   For the published finite-stack bit machine $M$ and natural exponent $C$, the event $\operatorname{Good}(M,C,q,G)$ means $N(G,q)>0$ and, for every rational $0<\varepsilon<1$, there are a rational output $\widehat Z$ and a halting time $m$ with
--   $$m\le\left(\frac{n+\operatorname{bit}(\varepsilon)}{\varepsilon}\right)^C,\quad M(G,\varepsilon)=\widehat Z\text{ within }m\text{ steps},\quad N(G,q)\le\widehat Z\le(1+\varepsilon)N(G,q).$$
--   Runs uses the existing finite-control, finite-stack-alphabet TM2 semantics. Each fixed-program macro uses a bounded number of stack operations; its fixed factor is absorbed by the exponent for sufficiently large $n$. This event keeps colorability and every tolerance inside the same high-probability statement in Theorem 1.7.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 3, 5, 30–31, computation model; Theorem 1.7 and its proof

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Encoding
import Definitions.Def_ConeL2G_properColorings

noncomputable section
open scoped Classical

namespace MultiSpinCounting.Positive.Supplement
open OnlineCRS.Combine

/-- Counts every labeled proper coloring, without quotienting by color permutations. -/
def coloringCount {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) : ℕ :=
  (ConeL2G.properColorings G (fun _ => (Finset.univ : Finset (Fin q)))).card

/-- Serialization only: n, edge count, lexicographically ordered pairs i<j. -/
def encGraph {n : ℕ} (G : SimpleGraph (Fin n)) : List Sym :=
  let es := (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)
  encNat n ++ [3] ++ encNat es.card ++ [3] ++
    ((es.toList.mergeSort (fun e f => decide
      (e.1.val * n + e.2.val ≤ f.1.val * n + f.2.val))).flatMap
      (fun e => encNat e.1.val ++ [3] ++ encNat e.2.val ++ [3]))

/-- The single event in Theorem 1.7 includes colorability and every binary tolerance.
M is the published fixed finite-stack TM2 machine, not a free output/time pair. -/
def Good {n : ℕ} (M : BitMachine) (C q : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  0 < coloringCount G q ∧ ∀ ε : ℚ, 0 < ε → ε < 1 →
    ∃ (Zhat : ℚ) (m : ℕ),
      (m : ℝ) ≤ (((n : ℝ) + (encRat ε).length) / (ε : ℝ)) ^ C ∧
      Runs M (encGraph G ++ [3] ++ encRat ε) (encRat Zhat) m ∧
      (coloringCount G q : ℝ) ≤ (Zhat : ℝ) ∧
      (Zhat : ℝ) ≤ (1 + (ε : ℝ)) * (coloringCount G q : ℝ)

end MultiSpinCounting.Positive.Supplement


