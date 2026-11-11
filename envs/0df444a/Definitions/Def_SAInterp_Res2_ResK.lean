-- Prove2me | Definitions.Def_SAInterp_Res2_ResK
-- name    : SAInterp_Res2_ResK
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:36:09.14612+00:00
-- url     : https://prove2.me/theorems/46f178ef-723e-4391-a907-7c30c4b4c1e4
-- title:
--   Res(k) proofs and refutations with symbol-count size (Definition 8.3, Figure 6) and the XOR composition F ∘ ⊕
-- statement:
--   A **term** is a finite set of literals (their conjunction) and a **DNF** a finite set of terms (their disjunction); the empty DNF is $\bot$, and the disjunction of two DNFs is their union. A **$k$-DNF** has only nonempty terms with at most $k$ literals. A clause $\ell_1\vee\dots\vee\ell_r$ of a CNF $F$ is read as the DNF of the unit terms $\{\ell_1\},\dots,\{\ell_r\}$.
--
--   A **$\mathrm{Res}(k)$ proof** from $F$ (Definition 8.3) is a sequence of $k$-DNFs $G_1,\dots,G_s$ in which every line is a clause of $F$ or is obtained from earlier lines by one of the rules of Figure 6, where $A,B$ are DNFs and $\ell,\ell_i$ literals:
--   $$\frac{A\vee\bigwedge_i\ell_i\qquad A\vee\ell}{A\vee(\ell\wedge\bigwedge_i\ell_i)}\ (\wedge\text{-Introduction}),\qquad \frac{A\vee\bigwedge_i\ell_i\qquad B\vee\bigvee_i\neg\ell_i}{A\vee B}\ (\text{Cut}),\qquad \frac{A}{A\vee B}\ (\text{Weakening}),\qquad \frac{}{\ell\vee\neg\ell}\ (\text{Axiom Introduction}).$$
--   It is a **refutation** if its last line is $\bot$. Its **size** is its number of symbols, counted as $\sum_t\bigl(1+\sum_{T\in G_t}|T|\bigr)$.
--
--   For a CNF $F$ over variables $x_i$, **$F\circ\oplus$** (p. 45) is the CNF over $y_i,z_i$ obtained by replacing each positive occurrence of $x_i$ by $(y_i\vee z_i)\wedge(\neg y_i\vee\neg z_i)$ and each negative occurrence by $(y_i\vee\neg z_i)\wedge(\neg y_i\vee z_i)$ and distributing $\vee$ over $\wedge$: each clause $C$ yields one clause for every choice of one of the two gadget clauses per literal of $C$.
--
--   **Formalization Note.** Lines are sets, so $\vee$ is commutative and idempotent. The conjunction $\bigwedge_i\ell_i$ in $\wedge$-Introduction and Cut is required to be nonempty. Premises may be any earlier lines, and a line may be used several times. The symbol count differs from a count of every connective and parenthesis by at most a constant factor. $y_i$ is `Sum.inl i` and $z_i$ is `Sum.inr i`. Resolution itself (cut-only clause proofs, length = number of lines) is the published `IsRefutation` of `MultiplierAssoc206_Resolution_CNF`.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 44, Definition 8.3 and Figure 6; p. 45, definition of F ∘ ⊕

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

open Classical

/-!
# The Res(k) proof system and XOR composition `F ∘ ⊕`

Acheampong, Davis, Robere, *Polynomial Interpolation for Sherali-Adams Lower Bounds*,
STOC 2027 submission (manuscript sha256 8de0a787…), §8 pp. 44–45: Definition 8.3, Figure 6,
and the definition of `F ∘ ⊕` (p. 45).

* Literals and clauses are those of `MultiplierAssoc206_Resolution_CNF`. A term is a finite set
  of literals (their conjunction); a DNF is a finite set of terms (their disjunction), so the
  disjunction of two DNFs is their union and the empty DNF is `⊥`.
* A `k`-DNF has only nonempty terms of at most `k` literals ("Each conjunction appearing in the
  proof must have at most `k` literals occurring").
* A clause `ℓ₁ ∨ … ∨ ℓᵣ` of `F` is the DNF of the singleton terms `{ℓ₁}, …, {ℓᵣ}`.
-/

variable {α : Type}

/-- A term: a finite set of literals, read as their conjunction. -/
abbrev Term (α : Type) := Finset (Literal α)

/-- A DNF: a finite set of terms, read as their disjunction (`∅` is `⊥`). -/
abbrev DNF (α : Type) := Finset (Term α)

/-- The negation of a literal. -/
def negLiteral (l : Literal α) : Literal α := (l.1, !l.2)

/-- A `k`-DNF: every term is nonempty and has at most `k` literals. -/
def IsKDNF (k : ℕ) (G : DNF α) : Prop := ∀ T ∈ G, T.Nonempty ∧ T.card ≤ k

/-- A clause as a DNF of unit terms. -/
noncomputable def clauseDNF (C : Clause α) : DNF α := C.image fun l => {l}

/-- `∧`-Introduction (Figure 6): from `A ∨ ⋀ᵢ ℓᵢ` and `A ∨ ℓ` infer `A ∨ (ℓ ∧ ⋀ᵢ ℓᵢ)`. -/
def AndIntro (G₁ G₂ G : DNF α) : Prop :=
  ∃ (A : DNF α) (T : Term α) (l : Literal α), T.Nonempty ∧
    G₁ = insert T A ∧ G₂ = insert {l} A ∧ G = insert (insert l T) A

/-- Cut (Figure 6): from `A ∨ ⋀ᵢ ℓᵢ` and `B ∨ ⋁ᵢ ¬ℓᵢ` infer `A ∨ B`. -/
def Cut (G₁ G₂ G : DNF α) : Prop :=
  ∃ (A B : DNF α) (T : Term α), T.Nonempty ∧
    G₁ = insert T A ∧ G₂ = B ∪ T.image (fun l => {negLiteral l}) ∧ G = A ∪ B

/-- Weakening (Figure 6): from `A` infer `A ∨ B`. -/
def Weakening (G₁ G : DNF α) : Prop := ∃ B : DNF α, G = G₁ ∪ B

/-- Axiom Introduction (Figure 6): `ℓ ∨ ¬ℓ`, with no premise. -/
def AxiomIntro (G : DNF α) : Prop := ∃ l : Literal α, G = {{l}, {negLiteral l}}

/-- A `Res(k)` proof from `F` (Definition 8.3): a sequence of `k`-DNFs each of which is a clause
of `F`, an instance of Axiom Introduction, or follows from earlier lines by Weakening,
`∧`-Introduction or Cut. -/
def IsResKProof (k : ℕ) (F : CNF α) (P : List (DNF α)) : Prop :=
  ∀ t (ht : t < P.length), IsKDNF k P[t] ∧
    ((∃ C ∈ F, P[t] = clauseDNF C) ∨ AxiomIntro P[t] ∨
      (∃ i, ∃ hi : i < t, Weakening (P[i]'(lt_trans hi ht)) P[t]) ∨
      (∃ i j, ∃ (hi : i < t) (hj : j < t),
        AndIntro (P[i]'(lt_trans hi ht)) (P[j]'(lt_trans hj ht)) P[t] ∨
        Cut (P[i]'(lt_trans hi ht)) (P[j]'(lt_trans hj ht)) P[t]))

/-- A `Res(k)` refutation of `F`: a `Res(k)` proof from `F` whose last line is `⊥`. -/
def IsResKRefutation (k : ℕ) (F : CNF α) (P : List (DNF α)) : Prop :=
  IsResKProof k F P ∧ P.getLast? = some ∅

/-- The number of symbols of a line, counted as one plus its literal occurrences. -/
def dnfSymbols (G : DNF α) : ℕ := 1 + ∑ T ∈ G, T.card

/-- The size of a `Res(k)` proof: the total number of symbols of its lines. -/
def resKSize (P : List (DNF α)) : ℕ := (P.map dnfSymbols).sum

/-- The XOR gadget clauses replacing a literal `(i, b)` of `F`: with `yᵢ = Sum.inl i` and
`zᵢ = Sum.inr i`, the literal `xᵢ` (`b = true`) becomes `(yᵢ ∨ zᵢ) ∧ (¬yᵢ ∨ ¬zᵢ)` and `¬xᵢ`
(`b = false`) becomes `(yᵢ ∨ ¬zᵢ) ∧ (¬yᵢ ∨ zᵢ)`; `c` selects one of the two clauses. -/
noncomputable def xorGadget (l : Literal α) (c : Bool) : Clause (α ⊕ α) :=
  {(Sum.inl l.1, c), (Sum.inr l.1, xor c (!l.2))}

/-- `C ∘ ⊕`: the CNF obtained from the clause `C` by the XOR substitution and distribution of
`∨` over `∧`, one clause for every choice of a gadget clause for each literal of `C`. -/
noncomputable def xorClause (C : Clause α) : CNF (α ⊕ α) :=
  (Finset.univ : Finset (C → Bool)).image fun f => C.attach.biUnion fun l => xorGadget l.1 (f l)

/-- `F ∘ ⊕` (p. 45): the union of `C ∘ ⊕` over the clauses `C` of `F`, over the variables
`y = Sum.inl`, `z = Sum.inr`. -/
noncomputable def xorCNF (F : CNF α) : CNF (α ⊕ α) := F.biUnion xorClause

end SAInterp.Res2


