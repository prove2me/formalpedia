-- Prove2me | Definitions.Def_LinSSWorst_Supplement_MSP
-- name    : LinSSWorst_Supplement_MSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:46:04.797781+00:00
-- url     : https://prove2.me/theorems/3cc25a4b-925a-4522-84f0-5dfe8cc6afe5
-- title:
--   Monotone span programs, acceptance and computing an access structure (Definition 7.2)
-- statement:
--   A **monotone span program** is $\mathcal M=(K,M,\rho,v)$ with $K$ a field, $M$ a $d\times e$ matrix over $K$, $\rho:[d]\to[n]$ a labelling of the rows by parties, and $v\in K^e\setminus\{0\}$ the target vector. Its **size** is $d$. For a coalition $A\subseteq[n]$, $\mathcal M$ **accepts** $A$ if the rows of $M$ whose labels lie in $A$ span $v$; $\mathcal M$ **computes** an access structure $f$ if it accepts $A$ exactly when $f(A)=1$.
--
--   Monotone span programs over finite fields are equivalent to linear secret-sharing schemes [KW93]; they are the objects of the lower bound Theorem 7.1.
--
--   **Formalization Note** The field is a parameter `K`; `d` and `e` are arbitrary (also $0$); span is the $K$-linear span in $K^e$.
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Definition 7.2, p.23

import Mathlib

namespace LinSSWorst.Supplement

/-- A **monotone span program** (Definition 7.2, p.23, [KW93]), from O. Nir, *Resolving the Worst-Case
Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of 2026-11-02, sha256
5521cfdb…): a quadruple `(K, M, ρ, v)` with `K` a field, `M` a `d × e` matrix over `K`, `ρ : [d] → [n]` a
labelling of the rows by parties, and a target vector `v ∈ Kᵉ \ {0}`. Its **size** is the number `d` of
rows.

**Formalization Note.** The field `K` is a parameter of the structure; `d` and `e` are arbitrary natural
numbers (also `0`); rows and columns are indexed by `Fin d`, `Fin e` and parties by `Fin n`. -/
structure MSP (K : Type*) [Field K] (n : ℕ) where
  /-- the number of rows (the size) -/
  d : ℕ
  /-- the number of columns -/
  e : ℕ
  /-- the matrix -/
  M : Matrix (Fin d) (Fin e) K
  /-- the row labelling `ρ : [d] → [n]` -/
  ρ : Fin d → Fin n
  /-- the target vector -/
  v : Fin e → K
  v_ne_zero : v ≠ 0

/-- The program **accepts** the coalition `A` (Definition 7.2) if the rows of `M` whose labels lie in `A`
span `v`.

**Formalization Note.** A coalition is `A : Fin n → Bool`; "span" is the `K`-linear span in `Kᵉ`. -/
def MSP.Accepts {K : Type*} [Field K] {n : ℕ} (P : MSP K n) (A : Fin n → Bool) : Prop :=
  P.v ∈ Submodule.span K (Set.range fun i : {i : Fin P.d // A (P.ρ i) = true} => P.M i.1)

/-- The program **computes** the access structure `f` (Definition 7.2) if it accepts `A` exactly when
`f(A) = 1`. -/
def MSP.Computes {K : Type*} [Field K] {n : ℕ} (P : MSP K n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ A : Fin n → Bool, P.Accepts A ↔ f A = true

end LinSSWorst.Supplement


