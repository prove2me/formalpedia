-- Prove2me | Definitions.Def_DistLTLSynth_Char_Geometric
-- name    : DistLTLSynth_Char_Geometric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:15:47.18295+00:00
-- url     : https://prove2.me/theorems/174f69dc-97f4-47de-a2fc-0e163f2617de
-- title:
--   Edge index j (Lemma 4.4 recursion), intervals J(h) and the map π : Γ^ω → [0, 1]
-- statement:
--   With offsets $\delta(1\to2)=0$, $\delta(1\leftrightarrow2)=1$, $\delta(1\leftarrow2)=2$, the edge index of a finite graph history is $j(\varepsilon)=0$ and
--   $$j(hg)=3j(h)+\begin{cases}\delta(g)&j(h)\text{ even}\\ 2-\delta(g)&j(h)\text{ odd,}\end{cases}$$
--   so $j(h)\in\{0,\dots,3^{|h|}-1\}$ is the left-to-right position of $h$'s edge in the round-$|h|$ inputless view complex (Lemma 4.4). $J(h) := [\,j(h)/3^{|h|},\ (j(h)+1)/3^{|h|}\,]$ (Eq. (1)). For $w\in\Gamma^\omega$ the intervals $J(w[\ldots r])$ are nested of length $3^{-r}$ and $\pi(w)$ is their common point, here written $\pi(w)=\sup_r j(w[\ldots r])/3^r$.
--
--   **Formalization Note.** The paper defines $j$ geometrically and proves the recursion as Lemma 4.4; the recursion is taken as the definition. $\pi$ is real-valued; Lemma 2.4 asserts its range is $[0,1]$.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 7 (PDF 8), §2.5 and Eq. (1); p. 16 (PDF 17), δ and Lemma 4.4

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model

namespace DistLTLSynth.Char

/-- The offsets `δ(1 → 2) = 0`, `δ(1 ↔ 2) = 1`, `δ(1 ← 2) = 2` (§4, p. 16). -/
def delta : CommGraph → ℕ
  | CommGraph.oneToTwo => 0
  | CommGraph.both => 1
  | CommGraph.twoToOne => 2

/-- The edge index `j(h) ∈ {0, …, 3^{|h|} - 1}` of a finite graph history, by the recursion of
Lemma 4.4: `j(ε) = 0` and `j(hg) = 3 j(h) + δ(g)` if `j(h)` is even,
`3 j(h) + 2 - δ(g)` if `j(h)` is odd. -/
def jIdx (h : List CommGraph) : ℕ :=
  h.foldl (fun a g => 3 * a + if a % 2 = 0 then delta g else 2 - delta g) 0

/-- The interval `J(h) := [j(h)/3^{|h|}, (j(h)+1)/3^{|h|}]` (Eq. (1), p. 7). -/
def J (h : List CommGraph) : Set ℝ :=
  Set.Icc ((jIdx h : ℝ) / 3 ^ h.length) (((jIdx h : ℝ) + 1) / 3 ^ h.length)

/-- `π : Γ^ω → [0, 1]`: the unique common point of the nested intervals `J(w[...r])`,
written as the supremum of their left endpoints `j(w[...r]) / 3^r` (a nondecreasing sequence
bounded by `1`). -/
noncomputable def piMap (w : ℕ → CommGraph) : ℝ :=
  ⨆ r : ℕ, (jIdx (pre w r) : ℝ) / 3 ^ r

end DistLTLSynth.Char


