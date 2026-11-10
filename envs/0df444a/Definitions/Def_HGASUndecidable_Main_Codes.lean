-- Prove2me | Definitions.Def_HGASUndecidable_Main_Codes
-- name    : HGASUndecidable_Main_Codes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:14:32.67051+00:00
-- url     : https://prove2.me/theorems/85caeeca-55d8-4fb6-90cd-7465f02519c0
-- title:
--   Finite rational polynomial codes and stability decision problems
-- statement:
--   A code decodes by Encodable to (n,d,list of (coordinate,exponent-list,rational coefficient)). Each monomial has n nonnegative exponents and a coordinate below n. Addition in MvPolynomial combines duplicate monomials; validity requires n,d≥1 and total exponent d on the resulting nonzero support. Zero coordinates, including the entire zero field, are homogeneous of every declared degree. HGAS and HLS contain only valid codes, and their two-parameter forms fix the dimension and declared degree exactly. HGASdegree leaves dimension variable. Many-one hardness quantifies over every Mathlib REPred on natural numbers; completeness adds recursive enumerability. Reductions are Mathlib ManyOneReducible and hence total computable maps. The halting set is definedness of the universal partial-recursive evaluator on a natural-number pair. These choices fix a concrete code, not an oracle or an arbitrary predicate.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), §§1,3.1,3.4, printed pp. 1,13–15 (PDF 3,15–17)

import Definitions.Def_HGASUndecidable_Main_Dynamics
import Mathlib.Computability.Reduce
import Mathlib.Computability.PartrecCode

noncomputable section
open scoped BigOperators

namespace HGASUndecidable.Main

/-- Dimension, declared degree, and a finite list of coordinate/monomial/coefficient triples. -/
abbrev RawFieldCode := ℕ × ℕ × List (ℕ × List ℕ × ℚ)

def decodeField (e : ℕ) : Option RawFieldCode := Encodable.decode e

def codeDimension (c : RawFieldCode) : ℕ := c.1
def codeDegree (c : RawFieldCode) : ℕ := c.2.1

def codePolys (c : RawFieldCode) (i : Fin c.1) : QPoly c.1 :=
  (c.2.2.map (fun t => if t.1 = i.val then
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun j : Fin c.1 =>
      t.2.1[j.val]?.getD 0)) t.2.2 else 0)).sum

/-- Support is inspected after duplicate monomials have been combined. -/
def ValidCode (c : RawFieldCode) : Prop :=
  1 ≤ c.1 ∧ 1 ≤ c.2.1 ∧
  (∀ t ∈ c.2.2, t.1 < c.1 ∧ t.2.1.length = c.1) ∧
  ∀ i : Fin c.1, ∀ m ∈ (codePolys c i).support, m.sum (fun _ a => a) = c.2.1

def codeField (c : RawFieldCode) := evalQField (codePolys c)

def HGASall (e : ℕ) : Prop := ∃ c, decodeField e = some c ∧ ValidCode c ∧ GAS (codeField c)
def HLSall (e : ℕ) : Prop := ∃ c, decodeField e = some c ∧ ValidCode c ∧ LyapunovStable (codeField c)
def HGAS (n d e : ℕ) : Prop :=
  ∃ c, decodeField e = some c ∧ ValidCode c ∧ c.1 = n ∧ c.2.1 = d ∧ GAS (codeField c)
def HLS (n d e : ℕ) : Prop :=
  ∃ c, decodeField e = some c ∧ ValidCode c ∧ c.1 = n ∧ c.2.1 = d ∧ LyapunovStable (codeField c)
def HGASdegree (d e : ℕ) : Prop := ∃ n, HGAS n d e

def ManyOneHard (S : ℕ → Prop) : Prop := ∀ A : ℕ → Prop, REPred A → ManyOneReducible A S
def ManyOneComplete (S : ℕ → Prop) : Prop := REPred S ∧ ManyOneHard S

def haltingSet (e : ℕ) : Prop :=
  ((Nat.Partrec.Code.ofNatCode e.unpair.1).eval e.unpair.2).Dom

end HGASUndecidable.Main


