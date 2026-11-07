-- Prove2me | Definitions.Def_FixpReciprocal_basicFIXP
-- name    : FixpReciprocal_basicFIXP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:48:43.526202+00:00
-- url     : https://prove2.me/theorems/24e77195-80cd-4ffa-802d-c6930d65a7aa
-- title:
--   Basic FIXP instances and their search problem (Definition 3.1)
-- statement:
--   A **basic FIXP instance** specifies a nonempty rational polytope $D\subseteq\mathbb R^n$, that is, a bounded set defined by finitely many linear inequalities with rational coefficients, together with an algebraic circuit for a continuous map $F:D\to D$, every operation being defined throughout $D$. Its solutions are the fixed points of $F$:
--   $$\mathrm{Sol}=\{x\in D: F(x)=x\}.$$
--
--   By Brouwer's theorem every such instance has a solution. The class FIXP is defined by reduction to this problem.
--
--   **Formalization Note** The polytope is a list of rows $(a,b)$, meaning $a\cdot x\le b$, each of length $n$. Boundedness and nonemptiness are clauses, as are continuity, the self-map property and definedness; as in the paper, these conditions are not required to be recognizable in polynomial time. A solution must lie in $D$, because the Lean evaluation is total. Continuity follows from definedness; it is kept because the definition states it.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Definition 3.1 and footnote 3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_FixpReciprocal_AlgCircuit

namespace FixpReciprocal

open OnlineCRS.Combine

/-- **The data of a basic FIXP instance:** the rows `(a, b)` of a system `a · x ≤ b` with rational
entries, and an algebraic circuit.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.1 and footnote 3, p.10. -/
structure BasicData where
  /-- the rows `(a, b)` of the polytope -/
  rows : List (List ℚ × ℚ)
  /-- the algebraic circuit -/
  circ : AlgCircuit

/-- The set `D` defined by the rows: all `x` with `a · x ≤ b` for each row. -/
def BasicData.dom (d : BasicData) : Set (Fin d.circ.n → ℝ) :=
  {x | ∀ r ∈ d.rows, ∑ i : Fin d.circ.n, ((r.1.getD i.val 0 : ℚ) : ℝ) * x i ≤ (r.2 : ℝ)}

/-- **A basic FIXP instance (Definition 3.1):** a nonempty rational polytope `D` (a bounded set defined by
finitely many rational linear inequalities) and an algebraic circuit for a continuous map `F : D → D`,
every operation being defined throughout `D`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.1 and footnote 3, p.10.

**Formalization Note.** The semantic conditions are clauses of the instance type; as in the paper, they
are not required to be recognizable in polynomial time. `Continuous` is implied by the definedness
clause; it is kept because Definition 3.1 says it. -/
structure BasicData.IsInstance (d : BasicData) : Prop where
  rows_length : ∀ r ∈ d.rows, r.1.length = d.circ.n
  wellFormed : d.circ.WellFormed
  nonempty : d.dom.Nonempty
  bounded : Bornology.IsBounded d.dom
  definedOn : d.circ.DefinedOn d.dom
  continuousOn : ContinuousOn d.circ.evalOut d.dom
  mapsTo : Set.MapsTo d.circ.evalOut d.dom d.dom

/-- Basic FIXP instances. -/
def BasicInst : Type := {d : BasicData // d.IsInstance}

/-- Numeric form of an operation (tag, constant, arguments). -/
def AlgOp.code : AlgOp → ℕ × ℚ × ℕ × ℕ
  | .const q => (0, q, 0, 0)
  | .add i j => (1, 0, i, j)
  | .sub i j => (2, 0, i, j)
  | .mul i j => (3, 0, i, j)
  | .div i j => (4, 0, i, j)
  | .min i j => (5, 0, i, j)
  | .max i j => (6, 0, i, j)

theorem AlgOp.code_injective : Function.Injective AlgOp.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [AlgOp.code]

/-- Binary encoding of an operation. -/
def encAlgOp (op : AlgOp) : List Sym :=
  fNat op.code.1 ++ fRat op.code.2.1 ++ fNat op.code.2.2.1 ++ fNat op.code.2.2.2

/-- Binary encoding of a row. -/
def encRow (r : List ℚ × ℚ) : List Sym := fList fRat r.1 ++ fRat r.2

/-- Binary encoding of the data of a basic instance. -/
def encBasicData (d : BasicData) : List Sym :=
  fNat d.circ.n ++ fList encRow d.rows ++ fList encAlgOp d.circ.ops ++ fList fNat d.circ.out

theorem encAlgOp_prefixFree : PrefixFree encAlgOp := by
  intro a b s t h
  simp only [encAlgOp, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree h
  obtain ⟨h2, h⟩ := fRat_prefixFree h
  obtain ⟨h3, h⟩ := fNat_prefixFree h
  obtain ⟨h4, h⟩ := fNat_prefixFree h
  exact ⟨AlgOp.code_injective (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))), h⟩

theorem encRow_prefixFree : PrefixFree encRow := by
  intro a b s t h
  simp only [encRow, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fRat_prefixFree.fList h
  obtain ⟨h2, h⟩ := fRat_prefixFree h
  exact ⟨Prod.ext h1 h2, h⟩

theorem encBasicData_injective : Function.Injective encBasicData := by
  rintro ⟨r, ⟨n, o, u⟩⟩ ⟨r', ⟨n', o', u'⟩⟩ h
  simp only [encBasicData, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree h
  obtain ⟨h2, h⟩ := encRow_prefixFree.fList h
  obtain ⟨h3, h⟩ := encAlgOp_prefixFree.fList h
  have h4 := fNat_prefixFree.fList.injective (by simpa using h)
  simp_all

/-- **Basic FIXP, as a search problem (Definition 3.1):** "The solutions are the fixed points of `F`."

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.1, p.10.

**Formalization Note.** A solution is a point of `D`: `evalOut` is total, so `x ∈ D` is a clause. -/
def basicFIXP : RealSearch where
  Inst := BasicInst
  enc := fun I => encBasicData I.1
  enc_injective := fun _ _ h => Subtype.ext (encBasicData_injective h)
  dim := fun I => I.1.circ.n
  Sol := fun I => {x | x ∈ I.1.dom ∧ I.1.circ.evalOut x = x}

end FixpReciprocal


