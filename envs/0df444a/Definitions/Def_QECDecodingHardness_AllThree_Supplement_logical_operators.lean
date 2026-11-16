-- Prove2me | Definitions.Def_QECDecodingHardness_AllThree_Supplement_logical_operators
-- name    : QECDecodingHardness_AllThree_Supplement_logical_operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:46:46.012805+00:00
-- url     : https://prove2.me/theorems/8ce3c84d-4fd5-4535-a062-7aac58de786e
-- title:
--   Logical-operator representatives and the logical decision tasks of the three decoding scenarios
-- statement:
--   A **Pauli operator modulo phase** on a finite qubit set $Q$ is a map $P : Q \to \mathbb F_2^2$, $q \mapsto (x_P(q), z_P(q))$, where $(1,0)$, $(0,1)$, $(1,1)$ stand for $X$, $Z$, $Y$ (the same per-qubit encoding as the base mission's errors). Two Paulis $P, R$ anticommute exactly when their **symplectic product**
--
--   $$\langle P, R\rangle = \sum_{q\in Q} \big(x_P(q)\,z_R(q) + z_P(q)\,x_R(q)\big) \in \mathbb F_2$$
--
--   equals $1$. A **stabilizer code** is given by a finite list of generators; the stabilizer group modulo phase is the $\mathbb F_2$-span of the generators. A **representative of a logical operator** is a Pauli $P$ with $\langle g, P\rangle = 0$ for every generator $g$ and $P$ not in that span. Any Pauli type and any support shape is allowed.
--
--   The three codes are built from the base mission's published coordinates:
--
--   1. **Color code** of order $k$ (distance $2k+1$): qubits are the triangles of `colorQubits k`; each check vertex $v$ of `colorChecks k` carries an $X$ generator and a $Z$ generator, both supported on the triangles incident to $v$.
--   2. **Surface code** on the $L\times L$ patch: qubits are the edges of `surfaceQubits L`; an $X$ generator at every vertex of `surfaceXChecks L` on its incident edges and a $Z$ generator at every face on its boundary edges.
--   3. **Two-patch code** of the transversal CNOT setting: two copies (patch 1 = control, patch 2 = target) of the $L\times L$ surface code, with every generator of each patch acting as the identity on the other.
--
--   The **logical effect** of an error is the error itself in the two code-capacity settings. In tCNOTZ, it is the end-of-circuit $Z$ Pauli frame: each data $Z$ fault on patch 1 contributes $Z$ on its edge of patch 1; a data $Z$ fault on patch 2 at time $t \le t_G - 1 = L-2$ (before the gate) is conjugated by the CNOT ($Z_{\rm target} \mapsto Z_{\rm control}Z_{\rm target}$) into $Z$ on its edge of both patches; a data fault at $t \ge t_G$ (after the gate) stays on patch 2; measurement bit-flips contribute nothing; contributions are summed in $\mathbb F_2$.
--
--   A query of the **logical decision problem** in a scenario consists of a base decoding instance (size parameter and full syndrome $\sigma$) together with a logical representative $P$ of that instance's code. Its predicate is
--
--   $$\exists E:\ E \text{ is a minimum-weight error with syndrome } \sigma \ \text{ and } \ \langle \mathrm{eff}(E), P\rangle = 1,$$
--
--   which is false when $\sigma$ is infeasible. The encoded task's input is the base nonsuccinct encoding of the instance followed by the $2|Q|$ bits of $P$; its only accepted answer is the one-bit word $[\mathrm{true}]$ if the predicate holds and $[\mathrm{false}]$ otherwise. This gives the three tasks `colorLogicalTask`, `surfaceLogicalTask` and `cnotLogicalTask` whose NP-hardness is Theorem 7.
--
--   **Formalization Note** The base `colorCodeZ` lists only the $X$ checks (only $Z$ errors occur); the $Z$ checks needed to define logical operators are added here from the same vertex list. Square-lattice families use $L = k+1$ as in the base `familySystem`, so every positive lattice size is a query. The tCNOTZ timing follows the base model: $t_G = L-1$, data faults at $t_G$ occur after the gate, data layers $t = 0,\dots,2L-2$.
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), p.3 (stabilizer codes; color code with X and Z checks on vertices), p.4 (surface code; tCNOTZ setting, error after the gate at t_G), p.17, Theorem 7 (logical operator, anticommutation)

import Definitions.Def_QECDecodingHardness_AllThree_search_hardness

namespace QECDecodingHardness.AllThree.Supplement

/-- A Pauli operator modulo phase on the finite qubit set `Q`, one binary pair
`(x, z)` per qubit exactly as in the base `LocalFault`: `(1,0)` is X, `(0,1)` is Z,
`(1,1)` is Y. Composition modulo phase is addition. -/
abbrev Pauli (Q : Type) := Q → LocalFault

/-- Binary symplectic product: `1` iff the two Paulis anticommute. A Y on a qubit
anticommutes with an X or a Z on that qubit. -/
def symplectic {Q : Type} [Fintype Q] (P R : Pauli Q) : Bit :=
  ∑ q, ((P q).1 * (R q).2 + (P q).2 * (R q).1)

/-- A stabilizer code on the qubit set `Q`, given by a finite list of generators
(Paulis modulo phase). -/
structure StabilizerCode (Q : Type) where
  generators : List (Pauli Q)

/-- Membership in the stabilizer group modulo phase: the binary vector lies in the
`F₂`-span of the generators. -/
def InStabilizerGroup {Q : Type} (C : StabilizerCode Q) (P : Pauli Q) : Prop :=
  P ∈ Submodule.span (ZMod 2) {g : Pauli Q | g ∈ C.generators}

/-- A representative of a (nontrivial) logical operator: commutes with every
stabilizer generator and is not itself a stabilizer modulo phase. Any Pauli type
and any support shape is allowed. -/
def IsLogicalRep {Q : Type} [Fintype Q] (C : StabilizerCode Q) (P : Pauli Q) : Prop :=
  (∀ g ∈ C.generators, symplectic g P = 0) ∧ ¬ InStabilizerGroup C P

/-- Section II.1, p.3: the triangular color code of order `k` (distance `2k+1`).
Qubits are the base `colorQubits k` (the columns of `colorCodeZ k`); every check
vertex of `colorChecks k` carries both an X and a Z generator, supported on the
incident triangles. `colorCodeZ` lists only the X checks; the Z checks are added here
from the same coordinates. -/
def colorStabilizerCode (k : ℕ) : StabilizerCode (Fin (colorCodeZ k).locations) where
  generators :=
    (colorChecks k).flatMap (fun v =>
      [fun q => (if v ∈ triangleVertices ((colorQubits k).get q) then 1 else 0, 0),
       fun q => (0, if v ∈ triangleVertices ((colorQubits k).get q) then 1 else 0)])

/-- Section II.2, p.4: the `L×L` surface code on the base `surfaceQubits L` (the
qubit locations of `surfaceCodeXYZ L`). X generators at the vertices
`surfaceXChecks L` on the incident edges; Z generators at the faces
`surfaceZChecks L` on their boundary edges. -/
def surfaceStabilizerCode (L : ℕ) : StabilizerCode (Fin (surfaceCodeXYZ L).locations) where
  generators :=
    (surfaceXChecks L).map (fun v =>
      fun q => (if edgeAtVertex v ((surfaceQubits L).get q) then 1 else 0, 0)) ++
    (surfaceZChecks L).map (fun f =>
      fun q => (0, if edgeAtFace f ((surfaceQubits L).get q) then 1 else 0))

/-- The two-patch code of tCNOTZ: qubit `(false, q)` is edge `q` of patch 1
(control), `(true, q)` of patch 2 (target). Generators are every generator of each
patch, tensored with the identity on the other patch. -/
def twoPatchStabilizerCode (L : ℕ) :
    StabilizerCode (Bool × Fin (surfaceCodeXYZ L).locations) where
  generators :=
    ([false, true] : List Bool).flatMap (fun a =>
      (surfaceStabilizerCode L).generators.map (fun g =>
        fun bq => if bq.1 = a then g bq.2 else 0))

/-- Contribution of one tCNOTZ fault location to the Z bit of the end-of-circuit
Pauli frame on qubit `(b, q)`. A data Z fault `(a, e, t)` on edge `e` stays on that
edge of patch `a`; if it sits on patch 2 (`a = true`) before the gate, i.e.
`t ≤ t_G - 1 = L - 2` (`t + 1 < L`), the transversal CNOT (control patch 1, target
patch 2, `Z_t ↦ Z_c Z_t`) copies it onto patch 1. Data faults at `t ≥ t_G = L - 1`
are after the gate (base convention). Measurement bit-flips contribute nothing. -/
def cnotFrameContribution (L : ℕ) (fault : CNOTFault) (b : Bool) (e : SquareEdge) : Bit :=
  match fault with
  | .inl (a, e', t) =>
      if e' = e ∧ (b = a ∨ (a = true ∧ b = false ∧ t + 1 < L)) then 1 else 0
  | .inr _ => 0

/-- Logical effect of a tCNOTZ spacetime error: its Z Pauli frame propagated to the
end of the circuit (after the last data-fault layer `t_f = 2L-2`), summed over time
in `F₂`. -/
def cnotLogicalEffect (L : ℕ) (err : Error (transversalCNOTZ L)) :
    Pauli (Bool × Fin (surfaceCodeXYZ L).locations) :=
  fun bq => (0, ∑ i : Fin (transversalCNOTZ L).locations,
    (err i).2 * cnotFrameContribution L ((cnotFaults L).get i) bq.1 ((surfaceQubits L).get bq.2))

/-- Bits of a Pauli on `Fin n`, `(x, z)` per qubit in order (as `encodeError`). -/
def encodePauli {n : ℕ} (P : Pauli (Fin n)) : List Bool :=
  (List.finRange n).flatMap (fun q => [decide ((P q).1 = 1), decide ((P q).2 = 1)])

/-- A query of the logical decision problem: a base decoding instance (size
parameter and full syndrome) and a logical representative of that instance's code. -/
abbrev LogicalQuery (f : DecodingFamily) (Q : ℕ → Type) [∀ k, Fintype (Q k)]
    (code : ∀ k, StabilizerCode (Q k)) :=
  Σ I : DecodingInstance f, {P : Pauli (Q I.1) // IsLogicalRep (code I.1) P}

/-- Some minimum-weight error with the query's syndrome anticommutes with the query's
logical representative (through `effect`). False on infeasible syndromes. -/
def AnticommutingMinimumExists (f : DecodingFamily) (Q : ℕ → Type) [∀ k, Fintype (Q k)]
    (code : ∀ k, StabilizerCode (Q k))
    (effect : ∀ k, Error (familySystem f k) → Pauli (Q k))
    (q : LogicalQuery f Q code) : Prop :=
  ∃ e : Error (familySystem f q.1.1),
    IsMinimumError (familySystem f q.1.1) q.1.2 e ∧ symplectic (effect q.1.1 e) q.2.1 = 1

/-- The encoded one-bit decision task: input is the base nonsuccinct encoding of the
decoding instance followed by the bits of `P`; the unique accepted answer is `[true]`
if some minimum-weight error anticommutes with `P`, and `[false]` otherwise. -/
def logicalDecisionTask (f : DecodingFamily) (Q : ℕ → Type) [∀ k, Fintype (Q k)]
    (code : ∀ k, StabilizerCode (Q k))
    (effect : ∀ k, Error (familySystem f k) → Pauli (Q k))
    (encodeP : ∀ k, Pauli (Q k) → List Bool) : EncodedSearchTask where
  Query := LogicalQuery f Q code
  encode q := encodeDecodingInstance q.1 ++ encodeP q.1.1 q.2.1
  accepts q a :=
    (a = [true] ∧ AnticommutingMinimumExists f Q code effect q) ∨
    (a = [false] ∧ ¬ AnticommutingMinimumExists f Q code effect q)

/-- ColorCodeZ: a Z error is itself its logical effect. -/
def colorLogicalTask : EncodedSearchTask :=
  logicalDecisionTask .colorCodeZ (fun k => Fin (colorCodeZ k).locations)
    colorStabilizerCode (fun _ e => e) (fun _ P => encodePauli P)

/-- SurfaceCodeXYZ (size parameter `k`, lattice `L = k+1` as in `familySystem`):
a Pauli error is itself its logical effect. -/
def surfaceLogicalTask : EncodedSearchTask :=
  logicalDecisionTask .surfaceCodeXYZ (fun k => Fin (surfaceCodeXYZ (k + 1)).locations)
    (fun k => surfaceStabilizerCode (k + 1)) (fun _ e => e) (fun _ P => encodePauli P)

/-- tCNOTZ (lattice `L = k+1`): logical effect is the propagated end-of-circuit frame;
`P` is encoded patch 1 then patch 2. -/
def cnotLogicalTask : EncodedSearchTask :=
  logicalDecisionTask .transversalCNOTZ
    (fun k => Bool × Fin (surfaceCodeXYZ (k + 1)).locations)
    (fun k => twoPatchStabilizerCode (k + 1)) (fun k e => cnotLogicalEffect (k + 1) e)
    (fun _ P => encodePauli (fun q => P (false, q)) ++ encodePauli (fun q => P (true, q)))

end QECDecodingHardness.AllThree.Supplement


