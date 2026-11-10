-- Prove2me | Definitions.Def_EditGV897_Main_Witnesses
-- name    : EditGV897_Main_Witnesses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:25:10.626232+00:00
-- url     : https://prove2.me/theorems/ba0493fc-1eb4-4119-b908-0fffd87d8a25
-- title:
--   Collision witnesses and signed affine prefix bounds
-- statement:
--   For an indexed affine family $F$, put $d_f(x)=x+f(x)$. For rows $G$ and a finite candidate set $S$, define
--
--   $$W_G(x)=\#\{f\in F:d_f(x)\ne0,\ Gd_f(x)=0\},\quad W_G(S)=\sum_{x\in S}W_G(x),\quad L_G(S)=|S|-W_G(S).$$
--
--   The first count retains occurrence multiplicity and excludes every fixed point. The last value is an integer and may be negative. Cosets and their prefix restrictions are specified as finite sets. Channel separation says that no distinct confusable word has the same syndrome.
--
--   Executable witness counting uses two affine-system counts per family occurrence, subtracting its fixed points. For a partial parity row $p$ of length $j$, $Z_j$ counts surviving witnesses with zero suffix, and $Q_j(p)$ additionally requires zero prefix parity. The executable exact expectation is represented by
--
--   $$2E(p)=T-Z_j+2Q_j(p),\qquad T=W_G(\mathbb F_2^n).$$
--
--   These operations supply every lower-bound and expectation evaluation used by the construction; they are algorithms with genuine bodies, with correctness left to the theorems.
--
--   **Formalization Note** Only subset-count subtraction uses natural numbers, because every fixed-point solution is also a collision-system solution. Signed bounds and doubled expectations use integers. Prefixes are ordered lists with zero-based indices.
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.2 equations (1)–(9) and §4.1 equation (10), printed pp. 7–10 / PDF pp. 8–11

import Definitions.Def_EditGV897_Main_Affine

namespace EditGV897.Main

/-- Specification counts indexed occurrences, not distinct induced affine functions. -/
noncomputable def witnessesAt {n : ℕ} (F : Family n) (G : Rows n) (x : Word n) : ℕ := by
  classical
  exact (F.filter (fun f => decide (differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0)))).length

noncomputable def witnessSum {n : ℕ} (F : Family n) (G : Rows n) (S : Finset (Word n)) : ℕ :=
  ∑ x ∈ S, witnessesAt F G x

noncomputable def signedBound {n : ℕ} (F : Family n) (G : Rows n) (S : Finset (Word n)) : ℤ :=
  (S.card : ℤ) - (witnessSum F G S : ℤ)

noncomputable def affineSet {n : ℕ} (E : List (Equation n)) : Finset (Word n) := by
  classical
  exact Finset.univ.filter (fun x => ∀ e ∈ E, equationHolds e x)

noncomputable def coset {n : ℕ} (G : Rows n) (β : List Bit) : Finset (Word n) := by
  classical
  exact Finset.univ.filter (fun x => syndrome G x = β)

noncomputable def prefixCoset {n : ℕ} (G : Rows n) (β p : List Bit) : Finset (Word n) := by
  classical
  exact (coset G β).filter (fun x => (wordList x).take p.length = p)

/-- Map separation and channel separation are kept distinct until family coverage is proved. -/
def Separated {n : ℕ} (t : ℕ) (G : Rows n) (x : Word n) : Prop :=
  ∀ y : Word n, x ≠ y →
    DeletionHash.MixedEdit.Confusable 1 t (wordList x) (wordList y) →
    syndrome G x ≠ syndrome G y

/-- Pull back the zero equation h·d(x)=0 along the affine difference map. -/
def pullZero {n : ℕ} (d : Affine n) (h : Word n) : Equation n :=
  (fun j => ∑ i, h i * d.matrix i j, dot h d.offset)

def fixedEquations {n : ℕ} (f : Affine n) : List (Equation n) :=
  List.ofFn (fun i : Fin n => ((difference f).matrix i, f.offset i))

def collisionEquations {n : ℕ} (f : Affine n) (G : Rows n) : List (Equation n) :=
  G.map (pullZero (difference f))

/-- The executable count subtracts fixed points separately for each occurrence. -/
def witnessCount {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) : ℕ :=
  (F.map (fun f => affineCount (E ++ collisionEquations f G) -
    affineCount (E ++ fixedEquations f))).sum

def boundCount {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) : ℤ :=
  (affineCount E : ℤ) - (witnessCount F G E : ℤ)

def cosetEquations {n : ℕ} (G : Rows n) (β : List Bit) : List (Equation n) :=
  G.zip β

def prefixEquations (n : ℕ) (p : List Bit) : List (Equation n) :=
  (List.range p.length).map (fun k => (unitWord n k, p[k]?.getD 0))

def prefixBound {n : ℕ} (F : Family n) (G : Rows n) (β p : List Bit) : ℤ :=
  boundCount F G (cosetEquations G β ++ prefixEquations n p)

def zeroSuffixCount {n : ℕ} (F : Family n) (G : Rows n) (j : ℕ) : ℕ :=
  (F.map (fun f =>
    let E := (fixedEquations f).drop j
    affineCount (E ++ collisionEquations f G) - affineCount (E ++ fixedEquations f))).sum

def zeroPrefixCount {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) : ℕ :=
  (F.map (fun f =>
    let E := (fixedEquations f).drop p.length ++ [pullZero (difference f) (listWord n p)]
    affineCount (E ++ collisionEquations f G) - affineCount (E ++ fixedEquations f))).sum

/-- Exactly 2E(p); integer arithmetic never rounds the conditional expectation. -/
def twiceExpectation {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) : ℤ :=
  (witnessCount F G [] : ℤ) - (zeroSuffixCount F G p.length : ℤ) +
    2 * (zeroPrefixCount F G p : ℤ)

end EditGV897.Main


