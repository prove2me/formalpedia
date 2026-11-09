-- Prove2me | Definitions.Def_HypRecov_inclusionMatrix
-- name    : HypRecov_inclusionMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:56.15884+00:00
-- url     : https://prove2.me/theorems/d57166f5-79da-4c21-b9ce-837da24b492e
-- title:
--   The inclusion matrix $W_{q,r}$ and its crossing submatrix $B_{S,q}$
-- statement:
--   Let $V=\{0,\dots,n-1\}$. The **inclusion matrix** $W_{q,r}$ has rows indexed by the $q$-subsets $A$ and columns by the $r$-subsets $e$ of $V$, with $(W_{q,r})_{A,e}=\mathbf 1[A\subseteq e]$; a terminal stream state is $y=W_{q,r}x$ for the edge-indicator vector $x$.
--
--   For $V=S\,\dot\cup\,T$, a set is **crossing** if it meets both $S$ and $T$. The **crossing submatrix** $B_{S,q}$ is the submatrix of $W_{q,r}$ with crossing rows and crossing columns, with real entries.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §2, p.5 (PDF p.6); §3, p.6 (PDF p.7)

import Mathlib

namespace HypRecov

/-- **The inclusion matrix `W_{q,r}`.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous
Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), §2, p.5 (PDF p.6): "The
inclusion matrix W_{q,r} has rows indexed by A ∈ (V choose q) and columns by e ∈ (V choose r), with
(W_{q,r})_{A,e} = 1[A ⊆ e]."

`inclusionMatrix 𝕜 n q r` has rows the `q`-subsets and columns the `r`-subsets of `Fin n`, as
subtypes `{A // A.card = q}`. -/
def inclusionMatrix (𝕜 : Type) [Zero 𝕜] [One 𝕜] (n q r : ℕ) :
    Matrix {A : Finset (Fin n) // A.card = q} {e : Finset (Fin n) // e.card = r} 𝕜 :=
  fun A e => if A.1 ⊆ e.1 then 1 else 0

/-- A vertex set is **crossing** for `V = S ∪̇ T` if it meets both parts (ibid., §3, p.6). -/
def IsCrossing {n : ℕ} (S A : Finset (Fin n)) : Prop := (A ∩ S).Nonempty ∧ (A \ S).Nonempty

instance {n : ℕ} (S A : Finset (Fin n)) : Decidable (IsCrossing S A) :=
  inferInstanceAs (Decidable ((A ∩ S).Nonempty ∧ (A \ S).Nonempty))

/-- **The crossing submatrix `B_{S,q}`** (ibid., §3, p.6, PDF p.7): "Let B_{S,q} be the submatrix of
W_{q,r} with crossing rows and crossing columns." Rows: crossing `q`-sets; columns: crossing
`r`-sets. -/
def crossingMatrix (n q r : ℕ) (S : Finset (Fin n)) :
    Matrix {A : Finset (Fin n) // A.card = q ∧ IsCrossing S A}
      {e : Finset (Fin n) // e.card = r ∧ IsCrossing S e} ℝ :=
  fun A e => if A.1 ⊆ e.1 then 1 else 0

end HypRecov


