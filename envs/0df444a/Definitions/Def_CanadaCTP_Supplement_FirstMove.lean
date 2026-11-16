-- Prove2me | Definitions.Def_CanadaCTP_Supplement_FirstMove
-- name    : CanadaCTP_Supplement_FirstMove
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:36:59.715296+00:00
-- url     : https://prove2.me/theorems/9b16158f-f7dc-4d48-a0e7-5def740290c4
-- title:
--   The first-move decision problem as a language; NP-hardness and coNP-hardness
-- statement:
--   An input is a disjoint-path instance with rational data and an edge $(i,j)$. Each edge distribution is a list of pairs (value $a/b$, probability $c/d$) written with natural numbers $a,b,c,d$; the input is written as a string over a seven-letter alphabet (binary digits and separators that delimit numbers, pairs, edges, paths and the instance).
--
--   For a class $\mathcal C$ of instances, the **first-move language** consists of the codes of inputs such that the lists are valid distributions (positive denominators and probabilities, distinct values, probabilities summing to $1$), the instance lies in $\mathcal C$ and is a CTP instance, $(i,j)$ is an edge, and **some optimal adaptive policy traverses edge $(i,j)$ as its first move**. Strings that are not codes are not in the language.
--
--   The two classes used are: every path has exactly two edges (Theorem 2); every path has exactly two edges, a constant first edge and a second edge with support of size at most $3$ (Theorem 6).
--
--   A language $L$ is **NP-hard** (resp. **coNP-hard**) if every language in NP (resp. coNP) over every finite nonempty alphabet reduces to $L$ by a polynomial-time many-one reduction.
--
--   **Formalization Note** NP, coNP, polynomial-time computability and reductions are those of the published `CookPvsNP_defs` (one-tape Turing machines, time $|x|^k+k$).
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 2, p.4 and p.29; §4, p.20; Theorem 6, p.26

import Mathlib
import Definitions.Def_CanadaCTP_Model
import Definitions.Def_CanadaCTP_Supplement_Optimal
import Definitions.Def_CookPvsNP_defs

namespace CanadaCTP.Supplement

open CanadaCTP

/-! # The first-move decision problem as a language (Theorems 6 and 2)

Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Theorem 2, p.4 (restated p.29), and Theorem 6, p.26: "Deciding whether there exists an optimal
adaptive policy that traverses a given edge as its first move".

**Formalization Note.**
* An input is a disjoint-path instance with rational data plus an edge `(i, j)`. A rational is
  written as a pair of natural numbers `(numerator, denominator)`; an edge distribution is a list of
  quadruples `(a, b, c, d)` meaning "value `a/b` with probability `c/d`"; a path is the list of its
  edges' distributions, an instance the list of its paths (`RatInst`).
* The input string is over the seven-letter alphabet `CSym`: naturals in binary (`Nat.bits`,
  least significant bit first) and separators that delimit numbers, pairs, edges, paths and the
  instance (`encQuery`). Strings that are not codes are not in the language.
* A code is in the language iff its lists are valid distributions (positive denominators, positive
  probabilities, distinct values, probabilities summing to `1`), the instance is a CTP instance in
  the theorem's class, `(i, j)` is an edge, and some optimal adaptive policy (feasible, expected
  cost `= E[Opt]`) traverses edge `(i, j)` as its first move almost surely.
* NP-hard / coNP-hard are with respect to the published `CookPvsNP` classes (one-tape Turing
  machines, polynomial-time many-one reductions), over every finite nonempty source alphabet. -/

/-- A rational instance: paths → edges → (value numerator, value denominator, probability
numerator, probability denominator). -/
abbrev RatInst : Type := List (List (List (ℕ × ℕ × ℕ × ℕ)))

/-- The real (value, probability) pairs of an encoded edge distribution. -/
noncomputable def toPts (e : List (ℕ × ℕ × ℕ × ℕ)) : List (ℝ × ℝ) :=
  e.map fun p => ((p.1 : ℝ) / p.2.1, (p.2.2.1 : ℝ) / p.2.2.2)

/-- An encoded edge distribution is valid: positive denominators, positive probabilities,
distinct values, probabilities summing to `1`. -/
def ValidEdge (e : List (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  (∀ p ∈ e, 0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2) ∧
  ((toPts e).map Prod.fst).Nodup ∧ ((toPts e).map Prod.snd).sum = 1

/-- The `EdgeDist` of a valid encoded edge distribution. -/
noncomputable def ValidEdge.toDist {e : List (ℕ × ℕ × ℕ × ℕ)} (h : ValidEdge e) : EdgeDist where
  pts := toPts e
  nodup := h.2.1
  val_nonneg := by
    intro q hq
    simp only [toPts, List.mem_map] at hq
    obtain ⟨p, -, rfl⟩ := hq
    positivity
  prob_pos := by
    intro q hq
    simp only [toPts, List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have := h.1 p hp
    have h1 : (0 : ℝ) < p.2.2.1 := by exact_mod_cast this.2.1
    have h2 : (0 : ℝ) < p.2.2.2 := by exact_mod_cast this.2.2
    exact div_pos h1 h2
  sum_one := h.2.2

/-- Every edge distribution of the rational instance is valid. -/
def AllValid (P : RatInst) : Prop := ∀ path ∈ P, ∀ e ∈ path, ValidEdge e

/-- The instance denoted by a valid rational instance: path `i` is `P[i]`, its edge `j` has the
distribution `P[i][j]`. -/
noncomputable def toInst (P : RatInst) (h : AllValid P) : Inst where
  k := P.length
  m := fun i => (P[i]).length
  X := fun i j => (h (P[i]) (List.getElem_mem i.isLt) ((P[i])[j])
    (List.getElem_mem j.isLt)).toDist

/-- The input alphabet: binary digits and five separators. -/
inductive CSym where
  | b0
  | b1
  | sep
  | endPair
  | endEdge
  | endPath
  | endInst
  deriving DecidableEq

instance : Fintype CSym where
  elems := {CSym.b0, CSym.b1, CSym.sep, CSym.endPair, CSym.endEdge, CSym.endPath, CSym.endInst}
  complete := by intro x; cases x <;> simp

/-- A natural number in binary, least significant bit first (`0` is the empty word). -/
def encNat (n : ℕ) : List CSym := (Nat.bits n).map fun b => if b then CSym.b1 else CSym.b0

/-- Code of one (value, probability) pair. -/
def encPair (p : ℕ × ℕ × ℕ × ℕ) : List CSym :=
  encNat p.1 ++ CSym.sep :: encNat p.2.1 ++ CSym.sep :: encNat p.2.2.1 ++ CSym.sep ::
    encNat p.2.2.2 ++ [CSym.endPair]

/-- Code of one edge distribution. -/
def encEdge (e : List (ℕ × ℕ × ℕ × ℕ)) : List CSym := e.flatMap encPair ++ [CSym.endEdge]

/-- Code of one path. -/
def encPath (p : List (List (ℕ × ℕ × ℕ × ℕ))) : List CSym := p.flatMap encEdge ++ [CSym.endPath]

/-- Code of a query: the instance, then the path index `i` and the edge index `j`. -/
def encQuery (P : RatInst) (i j : ℕ) : List CSym :=
  P.flatMap encPath ++ CSym.endInst :: encNat i ++ CSym.sep :: encNat j

/-- The first-move language over the class of instances cut out by `cls`: codes of queries
`(P, i, j)` with `P` valid and in the class, `toInst P` a CTP instance, `(i, j)` an edge, and
an optimal adaptive policy that traverses edge `(i, j)` as its first move. -/
def firstMoveLang (cls : RatInst → Prop) : CookPvsNP.Lang CSym :=
  { w | ∃ (P : RatInst) (i j : ℕ), w = encQuery P i j ∧ cls P ∧
      ∃ h : AllValid P, (toInst P h).IsCTP ∧
      ∃ (hi : i < P.length) (hj : j < (P[i]).length),
      ∃ (Mem : Type) (π : Policy (toInst P h) Mem),
        IsOptimal (toInst P h) π ∧ TraversesFirst (toInst P h) π ⟨i, hi⟩ ⟨j, hj⟩ }

/-- Theorem 2's class: every path has exactly two edges. -/
def TwoEdgeClass (P : RatInst) : Prop := ∀ path ∈ P, path.length = 2

/-- Theorem 6's class: every path has exactly two edges, the first edge has a constant weight
(support of size `1`) and the second edge a support of size at most `3`. -/
def Thm6Class (P : RatInst) : Prop :=
  ∀ path ∈ P, ∃ e₁ e₂, path = [e₁, e₂] ∧ e₁.length = 1 ∧ e₂.length ≤ 3

/-- NP-hardness (Cook's polynomial-time many-one reductions): every NP language over every finite
nonempty alphabet reduces to `L`. -/
def NPHard {Sym : Type} (L : CookPvsNP.Lang Sym) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.NP Sym' → CookPvsNP.PolyReducible L' L

/-- coNP-hardness: every coNP language over every finite nonempty alphabet reduces to `L`. -/
def CoNPHard {Sym : Type} (L : CookPvsNP.Lang Sym) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.coNP Sym' → CookPvsNP.PolyReducible L' L

end CanadaCTP.Supplement


