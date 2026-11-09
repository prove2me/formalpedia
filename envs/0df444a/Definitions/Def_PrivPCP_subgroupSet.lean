-- Prove2me | Definitions.Def_PrivPCP_subgroupSet
-- name    : PrivPCP_subgroupSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:26.499577+00:00
-- url     : https://prove2.me/theorems/fe84f4bb-299e-421f-b5a5-7cea21239aed
-- title:
--   A subgroup of $\mathbb F_q^\times$ as a subset of $\mathbb F_q$
-- statement:
--   For a multiplicative subgroup $S\le\mathbb F_q^\times$, the finite set $\{u\in\mathbb F_q: u\in S\}$ of its elements in $\mathbb F_q$. It has $|S|$ elements and is the evaluation set of the Reed–Solomon codes $\mathrm{RS}(S,t)$ of Conjecture 4.2, Theorem 4.11 and §4.1.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Conjecture 4.2, p.14 (PDF p.16)

import Mathlib

namespace PrivPCP

open Classical

/-- A multiplicative subgroup `S ≤ 𝔽_q^×` as the finite set of its elements in `𝔽_q` (Bafna, Vyas, *Private
PCPs from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Conjecture 4.2, p.14: "let
`S_1, …, S_r ⩽ F_q^×` be multiplicative subgroups"), the evaluation set of the Reed–Solomon codes on it. Its
size is `|S|` (`Units.val` is injective). -/
noncomputable def subgroupSet {q : ℕ} [NeZero q] (S : Subgroup (ZMod q)ˣ) : Finset (ZMod q) :=
  Finset.univ.filter fun x => ∃ u ∈ S, (u : ZMod q) = x

end PrivPCP


