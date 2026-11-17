-- Prove2me | Definitions.Def_PairwiseRealize_Supplement_Fiber
-- name    : PairwiseRealize_Supplement_Fiber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:26:23.8702+00:00
-- url     : https://prove2.me/theorems/bf2d1d82-5d7b-4f86-9a67-f1202f775242
-- title:
--   §2.4, p.5 — the fiber $\mathcal F(b)$, shattered sets, exact extensions, and the inputs of Theorem 2.3
-- statement:
--   Let $V=\{0,1\}^n$ be the cube of rows and $w_x=(1,(x_i)_i,(x_ix_j)_{i<j})\in\mathbb Z^m$, $m=1+n+\binom n2$, the pairwise statistics of a row. For an integer target $b\in\mathbb Z^m$ the **fiber** is
--   $$\mathcal F(b)=\Big\{F:V\to\{0,1\}\ :\ \sum_{x\in V}F(x)\,w_x=b\Big\}.$$
--   Each $F$ is identified with the set $S=F^{-1}(1)\subseteq V$, so $\mathcal F(b)$ is the family of exact realizations of $b$ by distinct rows of the full cube.
--
--   1. Given $Q\subseteq V$ and an assignment $\alpha:Q\to\{0,1\}$, a set $S$ is an **exact extension** of $\alpha$ if $S\in\mathcal F(b)$ and, for every $x\in Q$, $x\in S$ exactly when $\alpha(x)=1$.
--   2. $Q$ is **shattered** by $\mathcal F(b)$ if every assignment $\alpha:Q\to\{0,1\}$ has an exact extension. The positions of $Q$ are rows $x\in V$ (entries of a truth table), not the $n$ input coordinates.
--   3. The **construction input** for $(n,\delta,b)$, $\delta\in\mathbb N$, is $n$ and $\delta$ in binary followed by the coordinates of $b$ as signed binary numerals; the **extension input** appends the membership table of $\{x\in Q:\alpha(x)=1\}$.
--
--   These objects state Theorem 2.3: a single set $Q$ of positions on which every bit pattern can be completed to an exact realization.
--
--   **Formalization Note** An assignment is a function on all rows of which only the values on $Q$ matter. The encodings reuse `encodeNat`, `encodeInt` (`ContingencyTables`) and `featList`, `tableCode` (`PairwiseRealize.Model`, `PairwiseRealize.Machine`).
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §2.4, p.5 (PDF p.6), definition of F(b) and of shattering; Theorem 2.3, p.5 (PDF p.6), the algorithm inputs

import Mathlib
import Definitions.Def_ContingencyTables
import Definitions.Def_PairwiseRealize_Model
import Definitions.Def_PairwiseRealize_Machine

namespace PairwiseRealize.Supplement

/-!
# The fiber `F(b)`, shattered sets, exact extensions, and the inputs of Theorem 2.3

K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission
(manuscript sha256 62090516…), §2.4 "Prescribed entries and fiber size", printed p.5 (PDF p.6):
"Let F(b) = {F : V → {0,1} : Σ_x F(x) w_x = b}. A set Q ⊆ V is shattered by this fiber if every
assignment Q → {0,1} occurs as the restriction of one of its members. Here a position in Q is one of
the N possible input rows of a truth table, not one of its n input coordinates." Theorem 2.3, p.5:
"Given b and an integer promised lower bound δ, a deterministic algorithm constructs Q … Given any
assignment α : Q → {0,1}, the algorithm finds an exact extension".

**Formalization Note** A member `F : V → {0,1}` of the fiber is identified with the set
`S = F⁻¹(1) ⊆ V`, so `F(b)` is the finset of all `S` with `Σ_{x∈S} w_x = b`, i.e. the exact
realizations of `b` in the full cube (`IsRealization n univ b S` of the published
`PairwiseRealize.Model`). An assignment `α : Q → {0,1}` is a function `Row n → Bool` of which only the
values on `Q` matter. The algorithm inputs reuse the published encodings of `PairwiseRealize.Machine`
and `ContingencyTables`: `n` and `δ` in binary, the coordinates of `b` as signed binary numerals in the
order `featList n`, and the assignment `α` as the membership table of `{x ∈ Q : α x = 1}`.
-/

open OAI.MatchingFPRAS

/-- The fiber `F(b) = {F : V → {0,1} : Σ_x F(x) w_x = b}` (§2.4, p.5), each `F` identified with
`S = F⁻¹(1)`: the finset of exact realizations of `b` by distinct rows of the full cube `V`. -/
noncomputable def fiber (n : ℕ) (b : Feat n → ℤ) : Finset (Finset (Row n)) := by
  classical
  exact Finset.univ.filter fun S => IsRealization n Finset.univ b S

/-- `S` is an exact extension of the assignment `α` on `Q` for the target `b`: `S` is a member of
the fiber `F(b)` (`Σ_{x∈S} w_x = b`) whose indicator agrees with `α` at every position `x ∈ Q`. -/
def IsExtension (n : ℕ) (b : Feat n → ℤ) (Q : Finset (Row n)) (α : Row n → Bool)
    (S : Finset (Row n)) : Prop :=
  IsRealization n Finset.univ b S ∧ ∀ x ∈ Q, (x ∈ S ↔ α x = true)

/-- `Q ⊆ V` is shattered by the fiber `F(b)` (§2.4, p.5): every assignment `Q → {0,1}` is the
restriction to `Q` of some member of `F(b)`. Positions are rows `x ∈ V`, not input coordinates. -/
def IsShattered (n : ℕ) (b : Feat n → ℤ) (Q : Finset (Row n)) : Prop :=
  ∀ α : Row n → Bool, ∃ S, IsExtension n b Q α S

/-- The input of the construction algorithm of Theorem 2.3: `n` and the integer promised lower bound
`δ` in binary, then the coordinates of the integer target `b` in the order `featList n`. -/
def promiseInput (n δ : ℕ) (b : Feat n → ℤ) : List Symbol :=
  encodeNat n ++ encodeNat δ ++ ((featList n).map fun f => encodeInt (b f)).flatten

/-- The input of the extension algorithm of Theorem 2.3: the construction input followed by the
assignment `α : Q → {0,1}`, written as the membership table of `{x ∈ Q : α x = 1}`. -/
def extensionInput (n δ : ℕ) (b : Feat n → ℤ) (Q : Finset (Row n)) (α : Row n → Bool) :
    List Symbol :=
  promiseInput n δ b ++ tableCode n (Q.filter fun x => α x = true)

end PairwiseRealize.Supplement


