-- Prove2me | Definitions.Def_ReadTwiceCount_stateDesc
-- name    : ReadTwiceCount_stateDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:47.78795+00:00
-- url     : https://prove2.me/theorems/e6123695-92ac-4613-846a-0591050f1f3c
-- title:
--   The descriptor of a dangling query: prefix-conditioned states, EQ/NEQ incidences, zero prefixes
-- statement:
--   Let $h$ be a dangling query of a state $H$ whose variable occurs, in the clause $v$. Remove $v$ and list its other literals $x_1,\dots,x_d$ in clause order. The **prefix-conditioned state** $H_i$ is $H-v$ with $x_1,\dots,x_{i-1}$ pinned false. In $H_i$ the variable of $x_i$ either does not occur (a **free factor**) or has a remaining occurrence $z_i$, which is queried: the incidence is $\mathrm{EQ}$ if $z_i$ and $x_i$ have the same sign and $\mathrm{NEQ}$ otherwise, and $p_i=p(H_i,z_i)$.
--
--   The **descriptor of $(H,h)$** is built from these factors:
--
--   1. if the variable of $h$ does not occur, the query is **free**;
--   2. a free factor increases $t$ by one;
--   3. an input with $p_i=0$ makes the whole descriptor a **zero prefix** (the constant $y=1$) if it is $\mathrm{EQ}$, and is omitted if it is $\mathrm{NEQ}$;
--   4. every other input is a **retained child** $(\text{label},H_i,z_i)$.
--
--   The **prefix probability** $Q$ is the probability, under a uniformly random satisfying assignment of $H-v$, that all $x_i$ are false; the factor probability of a free factor is $1/2$, of an $\mathrm{EQ}$ input $p_i$, and of a $\mathrm{NEQ}$ input $1-p_i$.
--
--   The **recognized exact cases** are a free query ($y=1$), a zero prefix ($y=1$), and a descriptor with no retained child and $t\ge1$ ($y=1/(1-2^{-t})$).
--
--   **Formalization Note** The clause $v$ is the first clause containing $h$; for a dangling query whose variable occurs it is the only one.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §2, p.3; §3, pp.3–4

import Mathlib
import Definitions.Def_ReadTwiceCount_pFalse
import Definitions.Def_ReadTwiceCount_Descriptor

namespace ReadTwiceCount

variable {M : ℕ}

/-- One factor of the prefix product (4): a free factor, or an input with its label, its
prefix-conditioned state `Hᵢ` and the queried occurrence `zᵢ`. -/
inductive Factor (M : ℕ)
  | free
  | input (label : Label) (G : Formula M) (z : Lit M)
  deriving DecidableEq

/-- The first occurrence (in clause order, then literal order) of the variable `w` in `G`. -/
def findOcc (G : Formula M) (w : Fin M) : Option (Lit M) :=
  G.clauses.flatten.find? fun l => decide (l.1 = w)

/-- The factors of the literals `x₁, …, x_d`, starting from the state `G` (§3, p.3): before
processing `xᵢ`, the literals `x₁, …, x_{i−1}` are pinned false. If the variable of `xᵢ` no longer
occurs it is a free factor; otherwise its remaining occurrence `zᵢ` is queried in the
prefix-conditioned state `Hᵢ`, with label `EQ` if `zᵢ` and `xᵢ` have the same sign and `NEQ`
otherwise. -/
def prefixFactors : Formula M → List (Lit M) → List (Factor M)
  | _, [] => []
  | G, x :: xs =>
      (match findOcc G x.1 with
        | none => Factor.free
        | some z => Factor.input (if z.2 = x.2 then .EQ else .NEQ) G z) ::
        prefixFactors (G.pinFalse x) xs

/-- The index `v` of the clause containing the dangling literal `h` (the first such clause). -/
def danglingIdx (H : Formula M) (h : Lit M) : ℕ := H.clauses.findIdx fun C => decide (h ∈ C)

/-- `H − v`: the state with the clause containing `h` removed. -/
def removeClause (H : Formula M) (h : Lit M) : Formula M := ⟨H.clauses.eraseIdx (danglingIdx H h)⟩

/-- The other literals `x₁, …, x_d` of the clause `v` containing `h`, in clause order. -/
def otherLits (H : Formula M) (h : Lit M) : List (Lit M) :=
  (H.clauses.getD (danglingIdx H h) []).erase h

/-- **The prefix factors of a dangling query** `(H, h)` in its clause `v` (He, *A Deterministic
Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027 submission, manuscript sha256
7a2a9dcd…, §3, p.3): the factors of `x₁, …, x_d`, starting from `H − v`. -/
def factorsOf (H : Formula M) (h : Lit M) : List (Factor M) :=
  prefixFactors (removeClause H h) (otherLits H h)

/-- The probability that a factor's literal `xᵢ` is false given the prefix (§3, p.3): `1/2` for a
free factor, `pᵢ = p(Hᵢ, zᵢ)` for `EQ` and `1 − pᵢ` for `NEQ`. -/
def Factor.prob : Factor M → ℚ
  | .free => 1 / 2
  | .input .EQ G z => pFalse G z
  | .input .NEQ G z => 1 - pFalse G z

/-- **The prefix probability `Q`** (§3, p.3): the probability, under a uniformly random satisfying
assignment of `H − v`, that all other literals `x₁, …, x_d` of the clause `v` of `h` are false. -/
def prefixQ (H : Formula M) (h : Lit M) : ℚ :=
  ((Finset.univ.filter fun σ : Fin M → Bool =>
      (removeClause H h).eval σ = true ∧ ∀ x ∈ otherLits H h, σ x.1 ≠ x.2).card : ℚ) /
    (Z (removeClause H h) : ℚ)

/-- The outcome of constructing a descriptor: a free query, a zero prefix (the constant `y = 1`), or
a descriptor with `t` free factors and its retained children `(label, Hᵢ, zᵢ)` in order. -/
inductive DescResult (M : ℕ)
  | free
  | zeroPrefix
  | desc (t : ℕ) (children : List (Label × Formula M × Lit M))
  deriving DecidableEq

/-- Fold the factors into a descriptor (§3, p.3): a free factor increments `t`; an input with
`pᵢ = 0` stops with a zero prefix if it is `EQ` and is omitted if it is `NEQ`; every other input is a
retained child. -/
def collect : List (Factor M) → DescResult M
  | [] => .desc 0 []
  | .free :: fs =>
      match collect fs with
      | .desc t cs => .desc (t + 1) cs
      | r => r
  | .input lbl G z :: fs =>
      if pFalse G z = 0 then
        (match lbl with
          | .EQ => .zeroPrefix
          | .NEQ => collect fs)
      else
        match collect fs with
        | .desc t cs => .desc t ((lbl, G, z) :: cs)
        | r => r

/-- **The descriptor of a state** (He, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §3,
pp.3–4, displays (4)–(6)): `free` if the variable of `h` does not occur in `H`; otherwise the result
of folding the prefix factors of `h` in its clause. -/
def stateDesc (H : Formula M) (h : Lit M) : DescResult M :=
  if H.occ h.1 = 0 then .free else collect (factorsOf H h)

/-- **The recognized exact cases** (§2, p.3 and §3, p.4): a free query has `y = 1`, a zero prefix
gives `y = 1`, and a descriptor with no retained child and `t ≥ 1` has the exact value
`1/(1 − 2^{−t})`. Every other query has no exact value. -/
def exactValue (H : Formula M) (h : Lit M) : Option ℚ :=
  match stateDesc H h with
  | .free => some 1
  | .zeroPrefix => some 1
  | .desc t [] => if 1 ≤ t then some (1 / (1 - (1 / 2 : ℚ) ^ t)) else none
  | .desc _ (_ :: _) => none

end ReadTwiceCount


