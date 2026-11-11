-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_Query
-- name    : ShortestPlanarDisjoint_Main_Query
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:44.480971+00:00
-- url     : https://prove2.me/theorems/b3370ce0-9c96-400e-aea1-fcbecc0d623a
-- title:
--   Constructed Pfaffian query, finite selector and deletion semantics
-- statement:
--   For a genuine cut, incoming seam sides are determined by lifting primal edges to a disk parametrization and taking one-sided limits. Sorting crossings by position along each canonically oriented primal edge yields its actual ordered seam word. Conditional choice of a mathematical disk parametrization asserts no existence or computational cost and is not an input oracle.
--
--   For all disk states within b=max(1,total crossings), set A_D,E equal to the coefficient of the proposed leading monomial of D in p_E. Let b_E indicate that tracing E gives the prescribed terminal pairing. The selector vector is a solution of A^T gamma=b when one exists and zero otherwise. Nonsingularity, existence and uniqueness are theorem conclusions. Define I_M(p) as the gamma-weighted sum of these actual coefficient maps and
--
--   $$F^\ell_{G',M}(z)=I_M(\operatorname{Pf}K^\ell_{G'}(z)).$$
--
--   Edge deletion retains the original vertex set, cut, port indexing, state set and selector. It only removes edge blocks. Reduced states can be selected by equality of nonzero signatures; existence, uniqueness and pairing preservation are conclusions. The state series retains the original configuration costs. QueryCorrect includes the exact equation (13), the selector system and all three Section 4.1 guarantees. It is a proposition to prove, never a field assumed of an embedding or an algorithm. Finite output arrays contain every coefficient through the degree bound; higher coefficients must vanish by the query theorem.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Sections 4.1, 5.4–5.5, equation (13), p. 23 (PDF p. 25)

import Definitions.Def_ShortestPlanarDisjoint_Main_Seams
import Definitions.Def_ShortestPlanarDisjoint_Main_Configuration

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
noncomputable section

instance : Nonempty TrianglePoint :=
  ⟨⟨![1,0,0], by simp [Fin.forall_fin_succ, Fin.sum_univ_succ]⟩⟩

def clipUnit (x : ℝ) : unitInterval :=
  ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The actual primal edge through a flag, parametrized from its vertex to the
other endpoint. Both half-edges use the barycentric 0--1 sides. -/
def RibbonEmbedding.edgePoint {n k : ℕ} {I : RoutingInput n k}
    (E : RibbonEmbedding I) (flag : Fin E.flags) (t : unitInterval) : E.Carrier := by
  let u : ℝ := t
  have hu0 : 0 ≤ u := t.property.1
  have hu1 : u ≤ 1 := t.property.2
  exact if h : u ≤ 1/2 then E.point flag
    ⟨![1-2*u,2*u,0], by
      constructor
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]⟩
  else E.point (E.flip 0 flag)
    ⟨![2*u-1,2-2*u,0], by
      constructor
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]; ring⟩

def CutParameters.sidePoint {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (W : CutParameters E r) (s : Fin r) (side : Bool) (time : ℝ) : TrianglePoint :=
  let u := if W.direction s side then time else 1-time
  W.walk (clipUnit ((1-u) * (W.interval (.inr (s,side))).1 +
    u * (W.interval (.inr (s,side))).2))

/-- Identify the incoming copy by lifting the actual primal edge to the cut
disk and taking its one-sided limit. This is a semantic definition of a finite
crossing bit, not a geometric oracle supplied to the algorithm. -/
def SeamCode.incomingSide {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) (W : CutParameters E r) (s : Fin r)
    (a : SurfaceSegment E.embedding) : Bool := by
  classical
  let time : ℝ := (((List.ofFn (S.curve s).segment).idxOf a + 1 : ℕ) : ℝ) / (S.curve s).length
  let position := clipUnit ((a.last.coordinate 1 : ℝ) / 2)
  let localSide := if Filter.Tendsto
    (fun t : unitInterval => Function.invFun W.map (E.embedding.edgePoint a.flag t))
    (nhdsWithin position {t : unitInterval | (t : ℝ) < (position : ℝ)})
    (nhds (W.sidePoint s false time)) then false else true
  exact if E.embedding.vertex a.flag < E.embedding.vertex (E.embedding.flip 0 a.flag)
    then localSide else !localSide

def SeamCode.edgeWords {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) : EdgeWords n r := by
  classical
  exact fun edge => match S.parameters with
  | none => []
  | some W =>
    let all := (List.finRange r).flatMap fun s =>
      ((S.crossings s).filter fun a =>
        s(E.embedding.vertex a.flag, E.embedding.vertex (E.embedding.flip 0 a.flag)) = edge).map fun a =>
        let u := E.embedding.vertex a.flag
        let v := E.embedding.vertex (E.embedding.flip 0 a.flag)
        let q := a.last.coordinate 1 / 2
        (if u < v then q else 1-q, s, S.incomingSide W s a)
    ((all.mergeSort (fun a b => a.1 ≤ b.1)).map fun a => a.2)

def BoundedCounts (r b : ℕ) := {q : Fin r → ℕ // ∀ s, q s ≤ b}

instance (r b : ℕ) : Fintype (BoundedCounts r b) := by
  classical
  apply Fintype.ofInjective (fun q : BoundedCounts r b =>
    fun s => (⟨q.val s, Nat.lt_succ_of_le (q.property s)⟩ : Fin (b+1)))
  intro q u h
  apply Subtype.ext
  funext s
  exact congrArg Fin.val (congrFun h s)

def DiskState.raw {k f r b : ℕ} {L : DiskLayout k f r} (D : DiskState L b) :
    (q : BoundedCounts r b) × Equiv.Perm (DiskEndpoint k r q.val) :=
  ⟨⟨D.q, fun s => le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)) D.budget⟩,
    D.mate⟩

instance {k f r b : ℕ} (L : DiskLayout k f r) : Fintype (DiskState L b) := by
  classical
  apply Fintype.ofInjective DiskState.raw
  intro D E h
  cases D with
  | mk q budget mate inv nf nc nr =>
    cases E with
    | mk q' budget' mate' inv' nf' nc' nr' =>
      have hq : q = q' := congrArg (fun z => z.1.val) h
      subst q'
      have hm : mate = mate' := by
        exact eq_of_heq ((Sigma.mk.inj_iff.mp h).2)
      subst mate'
      rfl

def statePairingIndicator {k f r b : ℕ} {L : DiskLayout k f r}
    (sameOrder : Fin r → Bool) (M : TerminalPairing k) (D : DiskState L b) : ZMod 2 := by
  classical
  exact if ∀ i, (D.traceFrom sameOrder (.inl i)).2 = some (M.mate i) then 1 else 0

def stateMatrix {k f r b : ℕ} (L : DiskLayout k f r) (sameOrder : Fin r → Bool) :
    Matrix (DiskState L b) (DiskState L b) (ZMod 2) :=
  fun D E => (E.signature sameOrder).coeff D.topExponent

/-- The defining finite system A^T gamma=b. Outside the nonsingular source
case the fallback is zero; nonsingularity is never assumed by the definition. -/
def selectorVector {k f r b : ℕ} (L : DiskLayout k f r) (sameOrder : Fin r → Bool)
    (M : TerminalPairing k) : DiskState L b → ZMod 2 := by
  classical
  exact if h : ∃ gamma : DiskState L b → ZMod 2,
      ∀ E, ∑ D, gamma D * stateMatrix L sameOrder D E =
        statePairingIndicator sameOrder M E
    then Classical.choose h else fun _ => 0

def pairingFunctional {k f r b : ℕ} (L : DiskLayout k f r) (sameOrder : Fin r → Bool)
    (M : TerminalPairing k) (p : SignatureRing k r) : ZMod 2 :=
  ∑ D : DiskState L b, selectorVector L sameOrder M D * p.coeff D.topExponent

def RoutingInput.delete {n k : ℕ} (I : RoutingInput n k) (removed : Finset I.Edge) :
    RoutingInput n k :=
  { I with graph := I.graph.deleteEdges {e | ∃ a ∈ removed, a.val = e} }

/-- The promised query is defined from the Pfaffian, not from the linkage sum.
The original cut, ports, and selector are retained under every deletion. -/
def SeamCode.query {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) (removed : Finset I.Edge) (ell : Sym2 (Fin n) → ℕ) :
    Polynomial (ZMod 2) :=
  let p := matchingPfaffian (portMatrix (I.delete removed) S.edgeWords ell)
  p.sum fun d coefficient => Polynomial.monomial d
    (pairingFunctional (b := max 1 S.crossingCount) S.layout S.sameOrder I.pairing coefficient)

/-- Selection by equal nonzero signature is the unique reduced state when it
exists. Equality with the geometric return reduction is a theorem obligation. -/
def SeamCode.reducedState {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) (removed : Finset I.Edge) (C : GraphConfiguration (I.delete removed)) :
    Option (DiskState S.layout (max 1 S.crossingCount)) := by
  classical
  exact (Finset.univ : Finset (DiskState S.layout (max 1 S.crossingCount))).toList.find?
    fun D => C.signature S.edgeWords ≠ 0 ∧ C.signature S.edgeWords = D.signature S.sameOrder

def SeamCode.stateSeries {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) (removed : Finset I.Edge) (ell : Sym2 (Fin n) → ℕ)
    (D : DiskState S.layout (max 1 S.crossingCount)) : Polynomial (ZMod 2) := by
  classical
  exact ∑ C : GraphConfiguration (I.delete removed),
    if S.reducedState removed C = some D then Polynomial.monomial (C.cost ell) 1 else 0

/-- All three §4.1 guarantees, plus the exact §5.4 equation (13), as conclusions
to be established for the constructed cut and Pfaffian query. -/
def SeamCode.QueryCorrect {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) : Prop :=
  ∀ (removed : Finset I.Edge) (ell : Sym2 (Fin n) → ℕ),
    (∀ e ∈ I.graph.edgeSet, 0 < ell e) →
    (∃! gamma : DiskState S.layout (max 1 S.crossingCount) → ZMod 2,
      ∀ E, ∑ D, gamma D * stateMatrix S.layout S.sameOrder D E =
        statePairingIndicator S.sameOrder I.pairing E) ∧
    (∀ C : GraphConfiguration (I.delete removed), C.signature S.edgeWords ≠ 0 →
      ∃! D : DiskState S.layout (max 1 S.crossingCount),
        C.signature S.edgeWords = D.signature S.sameOrder ∧
        ((C.words S.edgeWords).paths.map (fun p => (p.1,p.2.1))) =
          ((D.words S.sameOrder).paths.map (fun p => (p.1,p.2.1)))) ∧
    (S.query removed ell =
      ∑ D : DiskState S.layout (max 1 S.crossingCount),
        if statePairingIndicator S.sameOrder I.pairing D = 1 then
          S.stateSeries removed ell D else 0) ∧
    (IsEmpty (Linkage (I.delete removed)) → S.query removed ell = 0) ∧
    (∀ L : Linkage (I.delete removed), L.IsMinimumFor ell →
      (∀ d < L.costWith ell, (S.query removed ell).coeff d = 0) ∧
      ((∀ K : Linkage (I.delete removed), K.IsMinimumFor ell → K = L) →
        (S.query removed ell).coeff (L.costWith ell) = 1))

def deletionBits {n k : ℕ} {I : RoutingInput n k} (removed : Finset I.Edge) : List Bool := by
  classical
  exact numberBits removed.card ++ removed.toList.flatMap fun e =>
    numbersBits ((e.val.toFinset.sort (· ≤ ·)).map Fin.val)

def SeamCode.queryBits {n k f r : ℕ} {I : RoutingInput n k} {E : FaceInput I f}
    (S : SeamCode E r) (deleted : List (Finset I.Edge)) (L : ℕ) : List Bool :=
  deleted.flatMap fun removed => (List.range (n*L+1)).map fun d =>
    decide ((S.query removed I.weight).coeff d = 1)

end
end ShortestPlanarDisjoint.Main


