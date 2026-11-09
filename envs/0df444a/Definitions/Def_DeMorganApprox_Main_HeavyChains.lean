-- Prove2me | Definitions.Def_DeMorganApprox_Main_HeavyChains
-- name    : DeMorganApprox_Main_HeavyChains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:52.45554+00:00
-- url     : https://prove2.me/theorems/04e2b53c-c830-47c3-b922-75c4ccda11cf
-- title:
--   §5.2 — heavy chains, helper targets and the constructed span program of a formula
-- statement:
--   Fix a De Morgan formula $T$. At every internal node the **heavy child** is the child with more leaves; on a tie a **tie rule** chooses either child; the other child is **light**. A **heavy chain** (Definition 5.4) starts at the root or at an internal light child, follows heavy children, and ends at a leaf. Its internal nodes $v_1,\dots,v_{k-1}$ contribute the side **terminals** $z_1,\dots,z_{k-1}$ (their light children) and the bottom leaf gives $z_k$. A terminal that is a leaf $\ell$ is the leaf coordinate $e_\ell$; a terminal that is an internal light child $D$ is the fresh **helper coordinate** $h_D$ of the chain starting at $D$.
--
--   The construction (PDF pp. 20–23) proceeds bottom-up. Each terminal $z_i$ has a balanced bound $S_i$: $S_i=1$ for a leaf and $S_i=S_D$ for a helper. Along the chain, $u_k=z_k$ with $(A_k,B_k)=(1,1)$, and for $j=k-1,\dots,1$ the gate step of Lemma 5.3 is applied to child 1 $=u_{j+1}$ with parameters $(A_{j+1},B_{j+1})$ and child 2 $=z_j$ with parameters $(S_j,S_j)$:
--   $$u_j=\cos\theta_j\,u_{j+1}+\sin\theta_j\,z_j,$$
--   adding the rotation vector $r_j=\sin\theta_j\,u_{j+1}-\cos\theta_j\,z_j$ at OR gates. With $u_C=u_1$ and $(A_C,B_C)=(A_1,B_1)$, put $t=\sqrt{B_C/(A_C+1)}$, $\cos^2\delta_C=\frac1{1+t}$, $\sin^2\delta_C=\frac t{1+t}$, add the always-available **connector**
--   $$g_C=\cos\delta_C\,h_C-\sin\delta_C\,u_C,$$
--   and set $S_C=1+\sqrt{(A_C+1)B_C}$. Every leaf occurrence contributes its own coordinate $e_\ell$ and one listed vector $e_\ell$ labelled by its literal.
--
--   The **constructed program** of $T$ has the leaf and helper coordinates as orthonormal basis, the literal, rotation and connector vectors as columns, and target $h_R$ for the root chain $R$ (for a single leaf, the leaf program with target $e_\ell$). The **chain program** of a chain with top $T$ is the same without $h_C$ and $g_C$, with target $u_C$. The **chain block** of $C$ consists of its rotation vectors and its connector. Lemmas 5.5–5.9 are statements about these objects.
--
--   **Formalization Note** Nodes are addressed by paths `List Bool` from the root of the formula the objects are built for ($\texttt{false}$ = left child). Coordinates are `Coord.leaf p` and `Coord.helper p`; columns are `Col.lit p`, `Col.rot p`, `Col.conn p`; finite coordinate and column sets are computed recursively, so the ambient spaces of different subtrees are orthogonal by construction. The tie rule is a function of the node's path. `chainParams` gives $(A,B)$ of the chain running down from the root, `helperBound` gives $S$ (1 at a leaf), and `terminals` lists $z_1,\dots,z_k$ from top to bottom. In each chain, child 1 of a gate is the heavy continuation, which fixes the sign of $r_j$ (the source notes the sign is immaterial, PDF pp. 25–26). Leaves carry literals rather than fresh formal variables $y_\ell$.
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), §5.2, Definition 5.4, construction in Lemmas 5.5–5.6, PDF pp. 20–23 (printed pp. 18–21), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; Lemma 5.3 angles PDF pp. 18–19 (printed pp. 16–17)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_GateComposition

/-!
The heavy-chain span program of §5.2 (PDF pp. 20–23, Definition 5.4, Lemmas 5.5–5.6).

Nodes of a formula are addressed by relative paths `List Bool` from its root (`false` = left
child, `true` = right child). Coordinates are the leaf occurrences (`Coord.leaf p`) and the helper
coordinates `h_C` of chain tops (`Coord.helper p`); columns are the literal vectors of the
leaves (`Col.lit p`), the OR-rotation vectors (`Col.rot p`) and the connectors (`Col.conn p`).
Every definition is relative to the formula it is applied to, so the objects of a subformula are
those of the whole formula with the path prefix removed.
-/

namespace DeMorganApprox.Main

/-- A tie rule: on a node whose two children have equally many leaves, `tie p` is the direction
of the heavy child of the node at relative path `p` (`false` = left). -/
abbrev TieRule := List Bool → Bool

/-- The tie rule seen from the child in direction `d`. -/
def TieRule.sub (tie : TieRule) (d : Bool) : TieRule := fun p => tie (d :: p)

/-- Ambient coordinates: leaf coordinates `e_ℓ` and helper coordinates `h_C`. -/
inductive Coord : Type where
  | leaf (p : List Bool) : Coord
  | helper (p : List Bool) : Coord
  deriving DecidableEq

/-- Columns: literal vectors, OR-rotation vectors, connector vectors. -/
inductive Col : Type where
  | lit (p : List Bool) : Col
  | rot (p : List Bool) : Col
  | conn (p : List Bool) : Col
  deriving DecidableEq

/-- Prefix the path of a coordinate by `d`. -/
def Coord.cons (d : Bool) : Coord → Coord
  | leaf p => leaf (d :: p)
  | helper p => helper (d :: p)

/-- Split off the first direction of a coordinate's path. -/
def Coord.uncons : Coord → Option (Bool × Coord)
  | leaf (d :: p) => some (d, leaf p)
  | helper (d :: p) => some (d, helper p)
  | _ => none

/-- Prefix the path of a column by `d`. -/
def Col.cons (d : Bool) : Col → Col
  | lit p => lit (d :: p)
  | rot p => rot (d :: p)
  | conn p => conn (d :: p)

/-- Split off the first direction of a column's path. -/
def Col.uncons : Col → Option (Bool × Col)
  | lit (d :: p) => some (d, lit p)
  | rot (d :: p) => some (d, rot p)
  | conn (d :: p) => some (d, conn p)
  | _ => none

/-- The standard basis vector of a coordinate. -/
def basisV (k : Coord) : Coord → ℝ := fun k' => if k' = k then 1 else 0

/-- Transport a vector of the child in direction `d` to the parent's coordinates. -/
def liftV (d : Bool) (v : Coord → ℝ) : Coord → ℝ := fun k =>
  match k.uncons with
  | some (d', k') => if d' = d then v k' else 0
  | none => 0

variable {m : ℕ}

/-- The child in direction `d` (`false` = left `φ`, `true` = right `ψ`). -/
def pick (d : Bool) (φ ψ : Formula m) : Formula m := if d then ψ else φ

/-- The gate `φ ∨ ψ` (`isOr = true`) or `φ ∧ ψ`. -/
def mkGate (isOr : Bool) (φ ψ : Formula m) : Formula m := if isOr then .or φ ψ else .and φ ψ

/-- Direction of the heavy child: the child with more leaves; the tie rule decides equality. -/
def heavyDir (tie : TieRule) (φ ψ : Formula m) : Bool :=
  if φ.leaves < ψ.leaves then true else if ψ.leaves < φ.leaves then false else tie []

/-- The balanced bound exported by a terminal `L` whose chain parameters are `p`: `1` for a leaf,
`1 + √((A+1)B)` for an internal chain top (Lemma 5.6 proof, PDF pp. 22–23). -/
noncomputable def helperBoundOf (L : Formula m) (p : ℝ × ℝ) : ℝ :=
  if L.isLeaf then 1 else 1 + Real.sqrt ((p.1 + 1) * p.2)

/-- Parent parameters at a gate: child 1 is the heavy child (chain parameters `(A₁,B₁)`),
child 2 is the light child (balanced bound `S`, so `(A₂,B₂) = (S,S)`). -/
noncomputable def nodeParams (isOr : Bool) (tie : TieRule) (φ ψ : Formula m)
    (pφ pψ : ℝ × ℝ) : ℝ × ℝ :=
  let d := heavyDir tie φ ψ
  let pH := if d then pψ else pφ
  let S := helperBoundOf (pick (!d) φ ψ) (if d then pφ else pψ)
  gateParams isOr pH.1 pH.2 S S

/-- The gate angle `(cos θ, sin θ)` at a gate, with the same convention. -/
noncomputable def nodeAngle (isOr : Bool) (tie : TieRule) (φ ψ : Formula m)
    (pφ pψ : ℝ × ℝ) : ℝ × ℝ :=
  let d := heavyDir tie φ ψ
  let pH := if d then pψ else pφ
  let S := helperBoundOf (pick (!d) φ ψ) (if d then pφ else pψ)
  gateAngle isOr pH.1 pH.2 S S

/-- `(A, B)`: the witness parameters of the internal target of the heavy chain running down from
the root of the formula (Lemma 5.5); `(1, 1)` at the bottom leaf. -/
noncomputable def chainParams (tie : TieRule) : Formula m → ℝ × ℝ
  | .lit _ _ => (1, 1)
  | .and φ ψ =>
      nodeParams false tie φ ψ (chainParams (tie.sub false) φ) (chainParams (tie.sub true) ψ)
  | .or φ ψ =>
      nodeParams true tie φ ψ (chainParams (tie.sub false) φ) (chainParams (tie.sub true) ψ)

/-- The balanced witness bound `S` of the program of a formula: `1` for a leaf, and
`S_C = 1 + √((A_C+1)B_C)` for a formula whose root is the top of the chain `C`. -/
noncomputable def helperBound (tie : TieRule) (T : Formula m) : ℝ :=
  helperBoundOf T (chainParams tie T)

/-- The gate angle at the root of the formula (`(1, 0)` for a leaf, never used). -/
noncomputable def rootAngle (tie : TieRule) : Formula m → ℝ × ℝ
  | .lit _ _ => (1, 0)
  | .and φ ψ =>
      nodeAngle false tie φ ψ (chainParams (tie.sub false) φ) (chainParams (tie.sub true) ψ)
  | .or φ ψ =>
      nodeAngle true tie φ ψ (chainParams (tie.sub false) φ) (chainParams (tie.sub true) ψ)

/-- The connector angle `(cos δ, sin δ)` (Lemma 5.6 proof, PDF pp. 22–23):
`sin²δ / cos²δ = t = √(B/(A+1))`, i.e. `cos²δ = 1/(1+t)`, `sin²δ = t/(1+t)`. -/
noncomputable def connAngle (A B : ℝ) : ℝ × ℝ :=
  let t := Real.sqrt (B / (A + 1))
  (Real.sqrt (1 / (1 + t)), Real.sqrt (t / (1 + t)))

/-- The coordinate a formula exports as a terminal: `e_ℓ` for a leaf, `h_C` otherwise. -/
def exportKey (L : Formula m) : Coord := if L.isLeaf then .leaf [] else .helper []

/-- The exported target vector of a formula (its terminal target `z`). -/
def exportV (L : Formula m) : Coord → ℝ := basisV (exportKey L)

/-- One gate step of the internal target: `u_j = cos θ_j u_{j+1} + sin θ_j z_j`. -/
noncomputable def uStep (isOr : Bool) (tie : TieRule) (φ ψ : Formula m)
    (uφ uψ : Coord → ℝ) : Coord → ℝ :=
  let d := heavyDir tie φ ψ
  let a := nodeAngle isOr tie φ ψ (chainParams (tie.sub false) φ) (chainParams (tie.sub true) ψ)
  a.1 • liftV d (if d then uψ else uφ) + a.2 • liftV (!d) (exportV (pick (!d) φ ψ))

/-- The internal target `u_C` of the heavy chain running down from the root (Lemma 5.5);
the bottom leaf coordinate `u_k = z_k` at a leaf. -/
noncomputable def chainU (tie : TieRule) : Formula m → Coord → ℝ
  | .lit _ _ => basisV (.leaf [])
  | .and φ ψ => uStep false tie φ ψ (chainU (tie.sub false) φ) (chainU (tie.sub true) ψ)
  | .or φ ψ => uStep true tie φ ψ (chainU (tie.sub false) φ) (chainU (tie.sub true) ψ)

/-- The vectors of the columns introduced at the root gate `T = φ ∘ ψ`: the OR-rotation vector
`r = sin θ u_{j+1} − cos θ z_j` (zero at an AND gate, where it is never a column) and the
connector `g_C = cos δ_C h_C − sin δ_C u_C`. -/
noncomputable def topCol (isOr : Bool) (tie : TieRule) (φ ψ : Formula m) : Col → Coord → ℝ
  | .rot [] =>
      let d := heavyDir tie φ ψ
      let a := nodeAngle isOr tie φ ψ (chainParams (tie.sub false) φ)
        (chainParams (tie.sub true) ψ)
      if isOr then
        a.2 • liftV d (chainU (tie.sub d) (pick d φ ψ)) - a.1 • liftV (!d) (exportV (pick (!d) φ ψ))
      else 0
  | .conn [] =>
      let p := chainParams tie (mkGate isOr φ ψ)
      let c := connAngle p.1 p.2
      c.1 • basisV (.helper []) - c.2 • chainU tie (mkGate isOr φ ψ)
  | _ => 0

/-- One gate step of the column vectors: columns below a child are the child's, transported. -/
noncomputable def colStep (isOr : Bool) (tie : TieRule) (φ ψ : Formula m)
    (cφ cψ : Col → Coord → ℝ) (j : Col) : Coord → ℝ :=
  match j.uncons with
  | some (d, j') => liftV d ((if d then cψ else cφ) j')
  | none => topCol isOr tie φ ψ j

/-- The vector of every column key (only keys in the column sets below are columns). The literal
vector of the leaf at path `p` is its leaf coordinate `e_ℓ`. -/
noncomputable def colVec (tie : TieRule) : Formula m → Col → Coord → ℝ
  | .lit _ _, j => if j = .lit [] then basisV (.leaf []) else 0
  | .and φ ψ, j => colStep false tie φ ψ (colVec (tie.sub false) φ) (colVec (tie.sub true) ψ) j
  | .or φ ψ, j => colStep true tie φ ψ (colVec (tie.sub false) φ) (colVec (tie.sub true) ψ) j

/-- Labels: a literal vector is labelled by its leaf's literal; rotation and connector vectors
are always available. -/
def colLabel : Formula m → Col → Label m
  | .lit i b, _ => if b then .pos i else .neg i
  | .and φ ψ, j =>
      match j.uncons with
      | some (false, j') => colLabel φ j'
      | some (true, j') => colLabel ψ j'
      | none => .always
  | .or φ ψ, j =>
      match j.uncons with
      | some (false, j') => colLabel φ j'
      | some (true, j') => colLabel ψ j'
      | none => .always

/-- Columns of a terminal's full program: its chain columns plus its connector if internal. -/
def fullColsOf (L : Formula m) (s : Finset Col) : Finset Col :=
  if L.isLeaf then s else insert (.conn []) s

/-- Coordinates of a terminal's full program: its chain coordinates plus `h_C` if internal. -/
def fullCoordsOf (L : Formula m) (s : Finset Coord) : Finset Coord :=
  if L.isLeaf then s else insert (.helper []) s

/-- One gate step of the chain column set: the heavy child's chain columns, the light child's
full program columns, and the rotation column at an OR gate. -/
def colsStep (isOr : Bool) (tie : TieRule) (φ ψ : Formula m) (cφ cψ : Finset Col) :
    Finset Col :=
  let d := heavyDir tie φ ψ
  (if d then cψ else cφ).image (Col.cons d) ∪
    (fullColsOf (pick (!d) φ ψ) (if d then cφ else cψ)).image (Col.cons (!d)) ∪
    (if isOr then {Col.rot []} else ∅)

/-- The columns of the program with the internal target `u_C` of the chain from the root. -/
def chainCols (tie : TieRule) : Formula m → Finset Col
  | .lit _ _ => {.lit []}
  | .and φ ψ => colsStep false tie φ ψ (chainCols (tie.sub false) φ) (chainCols (tie.sub true) ψ)
  | .or φ ψ => colsStep true tie φ ψ (chainCols (tie.sub false) φ) (chainCols (tie.sub true) ψ)

/-- One gate step of the chain coordinate set. -/
def coordsStep (tie : TieRule) (φ ψ : Formula m) (cφ cψ : Finset Coord) : Finset Coord :=
  let d := heavyDir tie φ ψ
  (if d then cψ else cφ).image (Coord.cons d) ∪
    (fullCoordsOf (pick (!d) φ ψ) (if d then cφ else cψ)).image (Coord.cons (!d))

/-- The coordinates of the program with the internal target `u_C` (no `h_C` of the root). -/
def chainCoords (tie : TieRule) : Formula m → Finset Coord
  | .lit _ _ => {.leaf []}
  | .and φ ψ => coordsStep tie φ ψ (chainCoords (tie.sub false) φ) (chainCoords (tie.sub true) ψ)
  | .or φ ψ => coordsStep tie φ ψ (chainCoords (tie.sub false) φ) (chainCoords (tie.sub true) ψ)

/-- Columns of the program of the whole formula. -/
def fullCols (tie : TieRule) (T : Formula m) : Finset Col := fullColsOf T (chainCols tie T)

/-- Coordinates of the program of the whole formula. -/
def fullCoords (tie : TieRule) (T : Formula m) : Finset Coord := fullCoordsOf T (chainCoords tie T)

/-- The terminals `z₁, …, z_k` of the chain from the root, top to bottom (Definition 5.4): the
light children along the heavy path, then the bottom leaf; each with its tie rule. -/
def terminals (tie : TieRule) : Formula m → List (TieRule × Formula m)
  | .lit i b => [(tie, .lit i b)]
  | .and φ ψ =>
      (tie.sub (!heavyDir tie φ ψ), pick (!heavyDir tie φ ψ) φ ψ) ::
        (if heavyDir tie φ ψ then terminals (tie.sub true) ψ else terminals (tie.sub false) φ)
  | .or φ ψ =>
      (tie.sub (!heavyDir tie φ ψ), pick (!heavyDir tie φ ψ) φ ψ) ::
        (if heavyDir tie φ ψ then terminals (tie.sub true) ψ else terminals (tie.sub false) φ)

/-- The coordinates of the terminal targets `z₁, …, z_k` of the chain from the root. -/
def terminalKeys (tie : TieRule) : Formula m → Finset Coord
  | .lit _ _ => {.leaf []}
  | .and φ ψ =>
      insert (Coord.cons (!heavyDir tie φ ψ) (exportKey (pick (!heavyDir tie φ ψ) φ ψ)))
        ((if heavyDir tie φ ψ then terminalKeys (tie.sub true) ψ
          else terminalKeys (tie.sub false) φ).image (Coord.cons (heavyDir tie φ ψ)))
  | .or φ ψ =>
      insert (Coord.cons (!heavyDir tie φ ψ) (exportKey (pick (!heavyDir tie φ ψ) φ ψ)))
        ((if heavyDir tie φ ψ then terminalKeys (tie.sub true) ψ
          else terminalKeys (tie.sub false) φ).image (Coord.cons (heavyDir tie φ ψ)))

/-- The OR-rotation columns of the chain from the root. -/
def rotCols (tie : TieRule) : Formula m → Finset Col
  | .lit _ _ => ∅
  | .and φ ψ =>
      (if heavyDir tie φ ψ then rotCols (tie.sub true) ψ
        else rotCols (tie.sub false) φ).image (Col.cons (heavyDir tie φ ψ))
  | .or φ ψ =>
      insert (.rot [])
        ((if heavyDir tie φ ψ then rotCols (tie.sub true) ψ
          else rotCols (tie.sub false) φ).image (Col.cons (heavyDir tie φ ψ)))

/-- The columns of the chain block `V_C` (Lemma 5.8): the OR-rotation vectors of the chain from
the root and its connector `g_C`. -/
def chainBlockCols (tie : TieRule) (T : Formula m) : Finset Col :=
  insert (.conn []) (rotCols tie T)

/-- The program of the chain from the root with its internal target `u_C` (Lemma 5.5). -/
noncomputable def chainProgram (tie : TieRule) (T : Formula m) :
    SpanProgram m (chainCoords tie T) (chainCols tie T) where
  target k := chainU tie T k.1
  vec j k := colVec tie T j.1 k.1
  label j := colLabel T j.1

/-- The span program constructed for a formula (§5.2): for a leaf, the leaf program of
Lemma 5.2; otherwise the program of Lemma 5.6 with target the helper coordinate `h_C` of the
chain from the root. -/
noncomputable def program (tie : TieRule) (T : Formula m) :
    SpanProgram m (fullCoords tie T) (fullCols tie T) where
  target k := exportV T k.1
  vec j k := colVec tie T j.1 k.1
  label j := colLabel T j.1

end DeMorganApprox.Main


