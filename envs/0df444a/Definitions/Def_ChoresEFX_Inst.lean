-- Prove2me | Definitions.Def_ChoresEFX_Inst
-- name    : ChoresEFX_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:05:37.199447+00:00
-- url     : https://prove2.me/theorems/1e39fcec-1e02-4b08-9d81-36b011e5071b
-- title:
--   Instances, their well-formedness, and the input and output encodings
-- statement:
--   An **instance** consists of $n$ agents, $m$ chores and a rational cost matrix $(c_i(g))$. It is **well formed** if $n\ge1$ and every cost is nonnegative. Zero costs are allowed.
--
--   The input word of Algorithm 1 lists $n$, $m$, the cost matrix row by row and $\varepsilon$. The input word of Algorithm 5 lists $n$, $m$, the cost matrix and $k$. The output word lists the owners $\sigma(0),\dots,\sigma(m-1)$ of the chores.
--
--   These encodings give the words on which the running-time statements of the mission are posed.
--
--   **Formalization Note** All numbers use the published self-delimiting binary codes `ExponomialAssortment.FPTAS.encodeNat` and `encodeRat`. The encodings are injective, which is proved in the mission's verification file. Words that encode no instance are not constrained. The paper's standing $n\ge2$ (p.5) is relaxed to $n\ge1$; its proof says "The case n = 1 is immediate" (p.19).
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), §2, p.5; Algorithm 1, p.7; Algorithm 5, p.14

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine

namespace ChoresEFX

open ExponomialAssortment.FPTAS

/-- **An input instance**: `n` agents, `m` chores and a rational cost matrix `(c_i(g))`.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC
2027 submission (manuscript sha256 b26d14cf…), §2, p.5: "the input is a cost matrix".

**Formalization Note.** Agents are `Fin n` and chores are `Fin m`, both 0-indexed. -/
structure Inst where
  n : ℕ
  m : ℕ
  c : Fin n → Fin m → ℚ

/-- **Well-formed instances**: at least one agent and nonnegative costs (§2, p.5, `c_i : 2^M → ℚ≥0`).

**Formalization Note.** Zero costs are allowed and matter: the scaling branch of Algorithm 1 exists
for them. The paper's standing `n ≥ 2` is relaxed to `n ≥ 1`, since the proof of Theorem 1.1 says "The
case n = 1 is immediate" (p.19); with `n = 0` and `m ≥ 1` no allocation exists. -/
def Inst.WellFormed (I : Inst) : Prop := 1 ≤ I.n ∧ ∀ i g, 0 ≤ I.c i g

/-- The cost matrix cast to the reals, for use with `cost`, `IsAlphaEFX` and `IsAlphaEFkX`. -/
noncomputable def Inst.realCost (I : Inst) : Fin I.n → Fin I.m → ℝ := fun i g => (I.c i g : ℝ)

/-- The cost matrix row by row, in the published self-delimiting code for rationals. -/
def encMatrix (I : Inst) : List Bool :=
  (List.finRange I.n).flatMap fun i => (List.finRange I.m).flatMap fun g => encodeRat (I.c i g)

/-- **The input word of Algorithm 1**: `n`, `m`, the cost matrix and `ε`.

**Formalization Note.** Every number is in the self-delimiting code of the published
`ExponomialAssortment.FPTAS.encodeNat`/`encodeRat` (numbers in binary, reduced numerator then
denominator). The encoding is injective (`Solutions/verification/ChoresEFX_Sanity.lean`). Words that
encode no instance are not constrained. -/
def encInput (I : Inst) (ε : ℚ) : List Bool :=
  encodeNat I.n ++ encodeNat I.m ++ encMatrix I ++ encodeRat ε

/-- The input word of Algorithm 5 (BRBI): `n`, `m`, the cost matrix and `k` (Qin et al., STOC 2027
submission, Algorithm 5, p.14). -/
def encBrbiInput (I : Inst) (k : ℕ) : List Bool :=
  encodeNat I.n ++ encodeNat I.m ++ encMatrix I ++ encodeNat k

/-- **The output word**: the owners `σ(0), …, σ(m−1)` of the chores, each in the published
self-delimiting code. For fixed `m` this is injective in `σ`
(`Solutions/verification/ChoresEFX_Sanity.lean`). -/
def encAlloc {n m : ℕ} (σ : Fin m → Fin n) : List Bool :=
  (List.finRange m).flatMap fun g => encodeNat (σ g).val

end ChoresEFX


