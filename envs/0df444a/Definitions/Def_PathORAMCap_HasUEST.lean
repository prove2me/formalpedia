-- Prove2me | Definitions.Def_PathORAMCap_HasUEST
-- name    : PathORAMCap_HasUEST
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:02.183039+00:00
-- url     : https://prove2.me/theorems/ce8cd7fe-48ff-41eb-b396-c976e40dd17a
-- title:
--   Uniform exponential stash tail bound (Definition 2.1)
-- statement:
--   Fix a positive integer $Z$. The family $\{P_{Z,N}:N\ge1\}$ **admits a uniform exponential stash tail bound** (UEST bound) if there are constants $C\ge1$ and $c>0$, depending only on $Z$, such that for every integer $N\ge1$, every instance $(s,\alpha)$ of $P_{Z,N}$ and every integer $R\ge0$,
--
--   $$\mathbb P\bigl[S(P_{Z,N}(s,\alpha);s)>R\bigr]\le Ce^{-cR}.$$
--
--   The same pair $C,c$ must serve every database size, sequence length, address order and stash capacity. This is the guarantee whose minimal capacity the paper determines.
--
--   **Formalization Note** $C$ and $c$ are quantified before $N$, the instance and $R$; $R$ is a natural number and the event is strict. $\mathbb P$ is the uniform probability on the label space (the published `OAI.TreeEdit.FiniteProbability.probability`).
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Definition 2.1, pp.7–8 (PDF pp.10–11), eq. (2)

import Mathlib
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_PathORAMCap_stashSize

set_option autoImplicit false

open OAI.TreeEdit.FiniteProbability

namespace PathORAMCap

/-- **Uniform exponential stash tail bound** (Definition 2.1, Chang, Au, *The Minimum Bucket Capacity
for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), pp.7–8 (PDF pp.10–11)):
"For a fixed positive integer Z, the family {PZ,N : N ≥ 1} admits a uniform exponential stash tail
bound (UEST bound) if there exist constants C ≥ 1 and c > 0, depending only on Z, such that for every
integer N ≥ 1, every instance (s, α) of PZ,N, and every integer R ≥ 0,
P[S(PZ,N(s, α); s) > R] ≤ Ce−cR."

**Formalization Note.** `C` and `c` are chosen before `N`, the instance and `R`. An instance is
`s ≥ 1` and `α : Fin s → Fin N`. `P` is the uniform probability on the label space `Labels N s`
(`OAI.TreeEdit.FiniteProbability.probability`, the count of outcomes divided by their number). -/
def HasUEST (Z : ℕ) : Prop :=
  ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ N : ℕ, 1 ≤ N → ∀ s : ℕ, 1 ≤ s → ∀ α : Fin s → Fin N, ∀ R : ℕ,
      probability (fun ω : Labels N s => R < stashSize Z α ω s) ≤ C * Real.exp (-(c * R))

end PathORAMCap


