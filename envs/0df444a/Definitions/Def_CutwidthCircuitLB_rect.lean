-- Prove2me | Definitions.Def_CutwidthCircuitLB_rect
-- name    : CutwidthCircuitLB_rect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:29.319014+00:00
-- url     : https://prove2.me/theorems/6bc46fa3-2924-4e24-9572-cf5a67491bb8
-- title:
--   Rectangle $P \times Q$ for a split $[n] = U \sqcup V$
-- statement:
--   Split the coordinates $\{1, \dots, n\}$ into disjoint sets $U$ and $V = [n] \setminus U$. For $P \subseteq \{0,1\}^U$ and $Q \subseteq \{0,1\}^V$, the **rectangle** $P \times Q$ is the set of inputs $x \in \{0,1\}^n$ whose $U$-part $x|_U$ lies in $P$ and whose $V$-part $x|_V$ lies in $Q$; its **sides** are $P$ and $Q$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.3, p.7

import Mathlib

namespace CutwidthCircuitLB

/-- The **rectangle** `P × Q` with respect to the split `[n] = U ⊔ Uᶜ` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.3, p.7):
for `P ⊆ {0,1}^U` and `Q ⊆ {0,1}^(Uᶜ)`, the set of inputs whose `U`-part lies in `P` and whose
`Uᶜ`-part lies in `Q`. -/
def rect {n : ℕ} (U : Finset (Fin n)) (P : Set ({j // j ∈ U} → Bool))
    (Q : Set ({j // j ∈ Uᶜ} → Bool)) : Set (Fin n → Bool) :=
  {x | (fun j : {j // j ∈ U} => x j.1) ∈ P ∧ (fun j : {j // j ∈ Uᶜ} => x j.1) ∈ Q}

end CutwidthCircuitLB


