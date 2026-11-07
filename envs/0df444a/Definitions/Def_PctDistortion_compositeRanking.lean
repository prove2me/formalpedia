-- Prove2me | Definitions.Def_PctDistortion_compositeRanking
-- name    : PctDistortion_compositeRanking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:54.902931+00:00
-- url     : https://prove2.me/theorems/7c96c55d-2ea5-4357-b731-99bbb843e752
-- title:
--   The composite election of Lemma 1
-- statement:
--   Let $\mathcal E_G=(V_G,C_G,\vec\succ_G)$ be an election whose candidates are the nodes $i$ of $G$, and $\mathcal E_i=(V_i,C_i,\vec\succ_i)$ elections, one for each $i$. The **composite election** has candidates $C=\biguplus_i C_i$ and voters $V=V_G\times\prod_i V_i$. Voter $v=(v_G,(v_i)_i)$ ranks $c\in C_i$ ahead of $c'\in C_{i'}$ iff
--
--   1. $i\ne i'$ and $v_G$ ranks $i$ ahead of $i'$, or
--   2. $i=i'$ and $v_i$ ranks $c$ ahead of $c'$.
--
--   Lemma 1 shows that its α-majority digraph is the composition $G[H_1,\dots,H_k]$ of the α-majority digraphs.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 1, p.10

import Mathlib
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

namespace PctDistortion

/-- The ranking profile of **Lemma 1's composite election**. Candidates are `C = ⊎_i C_i`
(`Σ i, Ci i`), voters are `V = V_G × ∏_i V_i`, and voter `v = (v_G, (v_i)_i)` ranks
`c ∈ C_i` ahead of `c' ∈ C_{i'}` iff either `i ≠ i'` and `v_G` ranks `i` ahead of `i'` in
`E_G`, or `i = i'` and `v_i` ranks `c` ahead of `c'` in `E_i`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 1, p.10: "Consider an election E = (V, C, ≻⃗) with candidates C = ⊎_{i∈V} Ci and voters
V = VG × ∏_{i∈V} Vi. The voter v = (vG, (vi)i∈V) ∈ V ranks the candidates as follows. Let c ∈ Ci,
c′ ∈ Ci′ be two candidates: if i ≠ i′, then v ranks c ahead of c′ if and only if vG ranks i ahead
of i′. If i = i′, then v ranks c ahead of c′ if and only if vi ranks c ahead of c′." -/
def compositeRanking {I VG : Type} {Vi Ci : I → Type} (EG : Election VG I)
    (Ei : ∀ i, Election (Vi i) (Ci i)) (v : VG × ∀ i, Vi i) (c c' : Σ i, Ci i) : Prop :=
  (c.1 ≠ c'.1 ∧ EG.prefers v.1 c.1 c'.1) ∨
    (∃ (i : I) (u u' : Ci i), c = ⟨i, u⟩ ∧ c' = ⟨i, u'⟩ ∧ (Ei i).prefers (v.2 i) u u')

end PctDistortion


