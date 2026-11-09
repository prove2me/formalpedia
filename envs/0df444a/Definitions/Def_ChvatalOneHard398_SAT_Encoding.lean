-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Encoding
-- name    : ChvatalOneHard398_SAT_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:50.637002+00:00
-- url     : https://prove2.me/theorems/93a7262b-226d-419e-9ca7-ff6e4969d51f
-- title:
--   Fixed binary encodings and polynomial-time computation
-- statement:
--   The tape alphabet is the published four-symbol alphabet. Natural numbers, integers, reduced rationals, vectors, and matrix rows use the published binary encoders. Length prefixes frame composite components so separators inside them remain unambiguous. A clause is serialized in canonical variable/polarity order. The decoding input explicitly prefixes its dimension before the square matrix and target; a parameter record prefixes both matrix dimensions.
--
--   $$\operatorname{PolyTime}(e_A,e_B,f)\quad\Longleftrightarrow\quad\text{there exists a TM2 machine computing }e_B(f(x))\text{ in a fixed polynomial of }|e_A(x)|.$$
--
--   The machine and its polynomial are independent of the input. Lemma 18 uses unary $N$ to express the printed $N+\sum|T|$ bound. The residue constructions use unary dimensions, moduli list $p$, and $h$, reflecting their printed numerical parameters; $D$, $H$, and $t$ remain binary. The arithmetic template input is its binary weight list and modulus. Output encodings contain the actual finite structures, tables, and coefficients. None precomputes a semantic answer.
--
--   **Formalization Note** Binary encodings are injective by their dimension headers, lengths, canonical ordering, and canonical rational forms; their lengths are linear in the corresponding structured bit size. The explicitly unary fields implement the source's different numerical complexity measures.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.8, §2, Promise problems; pp.19,21,23, construction-time bounds; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Residue
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_RobustToDynamics_encMat

namespace ChvatalOneHard398.SAT
open OnlineCRS.Combine

/-- Length framing preserves parseability when the component alphabet uses all four symbols. -/
def frame (w : List Sym) : List Sym := encNat w.length ++ [2] ++ w

def encList {A : Type} (e : A → List Sym) (xs : List A) : List Sym :=
  encNat xs.length ++ [2] ++ xs.flatMap (fun x => frame (e x))

def encBool (b : Bool) : List Sym := [if b then 1 else 0]

def encLiteral (l : Literal) : List Sym := encNat l.var ++ [2] ++ encBool l.pos

def encClause (T : Clause) : List Sym := encList encLiteral (orderedLiterals T)

def encFormula (F : Formula) : List Sym :=
  encNat F.N ++ [2] ++ encList encClause F.clauses

/-- Unary dimension for Lemma 18's stated N+Σ|T| complexity. -/
def encExactInput (T : Formula) : List Sym :=
  List.replicate T.N 1 ++ [2] ++ encList encClause T.clauses

def encBDD (x : BDDInput) : List Sym :=
  encNat x.n ++ [2] ++ frame (RobustToDynamics.encMat x.basis) ++ [3] ++ encVec x.target

def encOutput (v : List ℚ) : List Sym := encList encRat v

def encGate (g : Gate) : List Sym :=
  frame (encList encNat g.inputs) ++ frame (encNat g.outputs) ++ encList (encList encBool) g.table

def encFunctional (X : Functional) : List Sym :=
  frame (encNat X.free) ++
  frame (encList (fun I => encList encNat (I.sort (· ≤ ·))) X.choices) ++
  frame (encList encGate X.gates) ++ encList (fun ub => frame (encNat ub.1) ++ encBool ub.2) X.fixings

def encLinear (c : IntLinear) : List Sym :=
  encList (fun uz => frame (encNat uz.1) ++ encInt uz.2) c

def encResidueResult (z : ResidueResult) : List Sym :=
  frame (encFunctional z.model) ++ frame (encList encNat z.digits) ++ encLinear z.quotient

def encResidueInput (a : List ℕ × ℕ) : List Sym :=
  frame (encList encNat a.1) ++ encNat a.2

/-- Unary p,h and dimensions express the precise printed construction-time parameters. -/
def encParams (a : Params) : List Sym :=
  frame (List.replicate a.m 1) ++ frame (List.replicate a.r 1) ++
  frame (encList (fun q => List.replicate q 1) a.p) ++ frame (List.replicate a.h 1) ++
  frame (encNat a.D) ++ frame (RobustToDynamics.encMat (fun i j => (a.H i j : ℚ))) ++
  encVec (fun i => (a.t i : ℚ))

def PolyTime {A B : Type} (ea : A → List Sym) (eb : B → List Sym) (f : A → B) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

end ChvatalOneHard398.SAT


