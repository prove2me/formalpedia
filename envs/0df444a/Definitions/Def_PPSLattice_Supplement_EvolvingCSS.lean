-- Prove2me | Definitions.Def_PPSLattice_Supplement_EvolvingCSS
-- name    : PPSLattice_Supplement_EvolvingCSS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T08:08:59.277974+00:00
-- url     : https://prove2.me/theorems/52771aab-65cc-42c0-86e0-84915de6f5b6
-- title:
--   Computational secret sharing for evolving graphs
-- statement:
--   An evolving-graph CSS scheme has polynomial-time setup, vertex addition, and reconstruction, creates a public share and dealer state, adds vertices with neighborhoods among earlier vertices, and reconstructs using only the shares belonging to a set containing an edge. Adaptive security allows neighborhoods and corruptions to interleave and requires only that the final corrupted vertices form an independent set.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 6.16 and Construction 6.17, pp.51–53

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_Supplement_RPPS
import Definitions.Def_PPSLattice_decBin
import Definitions.Def_PPSLattice_decSet
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_RestrictedDec_Adversary

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- An evolving graph is represented by its sequential neighborhoods: entry `t-1` is
`S_t ⊆ [t-1]`. -/
abbrev EvolvingGraph := List (Finset ℕ)

def EvolvingGraph.Valid (G : EvolvingGraph) : Prop :=
  ∀ t ∈ Finset.Icc 1 G.length, G.getD (t - 1) ∅ ⊆ Finset.Icc 1 (t - 1)

def EvolvingGraph.Adj (G : EvolvingGraph) (u v : ℕ) : Prop :=
  (u < v ∧ u ∈ G.getD (v - 1) ∅) ∨ (v < u ∧ v ∈ G.getD (u - 1) ∅)

def EvolvingGraph.Independent (G : EvolvingGraph) (C : Finset ℕ) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ G.Adj u v

def EvolvingGraph.ContainsEdge (G : EvolvingGraph) (A : Finset ℕ) : Prop :=
  ∃ u ∈ A, ∃ v ∈ A, G.Adj u v

/-- A CSS syntax for rigid evolving graphs (Definition 6.16, pp.51--52). -/
structure EvolvingCSS where
  setup : ℕ → ℕ → ℕ → Bool → PMF (Str × Str)
  addVertex : ℕ → ℕ → ℕ → ℕ → Str → Finset ℕ → PMF (Str × Str)
  recon : ℕ → EvolvingGraph → Finset ℕ → Str → List Str → Option Bool

private def encNatSet (S : Finset ℕ) : Str :=
  BeyondDS.tup ((S.sort (· ≤ ·)).map encBin)

private def encGraph (G : EvolvingGraph) : Str := BeyondDS.tup (G.map encNatSet)

/-- Polynomial-time syntax for CSS. The two bound encoders distinguish the ordinary unary-bound
interface from the binary-bound unbounded variants of Definition 6.16. -/
def EvolvingCSS.EfficientWithBounds (C : EvolvingCSS) (encQ encD : ℕ → Str) : Prop :=
  PPTSampler (fun x : ℕ × ℕ × ℕ × Bool =>
      BeyondDS.tup [encNat x.1, encQ x.2.1, encD x.2.2.1, [x.2.2.2]])
    (fun x => (C.setup x.1 x.2.1 x.2.2.1 x.2.2.2).map fun z => BeyondDS.tup [z.1, z.2]) ∧
  PPTSampler (fun x : ℕ × ℕ × ℕ × ℕ × Str × Finset ℕ =>
      BeyondDS.tup [encNat x.1, encQ x.2.1, encD x.2.2.1, encBin x.2.2.2.1,
        x.2.2.2.2.1, encNatSet x.2.2.2.2.2])
    (fun x => (C.addVertex x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
      x.2.2.2.2.2).map fun z => BeyondDS.tup [z.1, z.2]) ∧
  PolyTimeOn (fun x : ℕ × EvolvingGraph × Finset ℕ × Str × List Str =>
      BeyondDS.tup [encNat x.1, encGraph x.2.1, encNatSet x.2.2.1,
        x.2.2.2.1, BeyondDS.tup x.2.2.2.2])
    (fun x => match C.recon x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 with
      | none => [] | some b => [b])

def EvolvingCSS.Efficient (C : EvolvingCSS) : Prop :=
  C.EfficientWithBounds encNat encNat

/-- Only the shares named by `A` are supplied to reconstruction; other list positions are blank
totalization cells, not shares available to the decoder. -/
def restrictShares (A : Finset ℕ) (shares : List Str) : List Str :=
  shares.mapIdx fun j sh => if j + 1 ∈ A then sh else []

/-- Run `AddVertex` sequentially and collect all vertex shares. -/
noncomputable def cssBuild (C : EvolvingCSS) (lam Q D : ℕ) : ℕ →
    EvolvingGraph → Str → List Str → PMF (List Str × Str)
  | 0, _, st, shares => PMF.pure (shares, st)
  | t + 1, G, st, shares =>
      (C.addVertex lam Q D (G.length - t) st (G.getD (G.length - t - 1) ∅)).bind fun z =>
        cssBuild C lam Q D t G z.2 (shares ++ [z.1])

/-- Negligible-error correctness for every graph history and every authorized set. -/
def EvolvingCSS.Correct (C : EvolvingCSS) : Prop :=
  ∃ nu : ℕ → ℝ, NoisyOWMPC.Negligible nu ∧ ∀ lam Q D : ℕ,
    1 ≤ lam → 1 ≤ Q → 1 ≤ D →
    ∀ G : EvolvingGraph, G.length ≤ 2 ^ lam → G.Valid →
      (∀ t ∈ Finset.Icc 1 G.length, (G.getD (t - 1) ∅).card ≤ D) →
      ∀ A ⊆ Finset.Icc 1 G.length, G.ContainsEdge A → ∀ s : Bool,
        1 - nu lam ≤ (((C.setup lam Q D s).bind fun z =>
          (cssBuild C lam Q D G.length G z.2 []).map fun out =>
            decide (C.recon lam G A z.1 (restrictShares A out.1) = some s)) true).toReal

inductive CSSMove
  | add (S : Finset ℕ)
  | corrupt (v : ℕ)
  | guess (b : Bool)

def decCSSMove (w : Str) : CSSMove :=
  let fs := BeyondDS.untup w
  match fs.getD 0 [] with
  | [false, false] => .add (decSet (fs.getD 1 []))
  | [false, true] => .corrupt (decBin (fs.getD 1 []))
  | _ => .guess ((fs.getD 1 []).headD false)

open Classical in
/-- Adaptive evolving-graph game. Neighborhoods and corruptions are interleaved; independence and
the collusion bound are checked on the final graph, allowing a later vertex to acquire edges to
an already corrupted one exactly as Definition 6.16 permits. -/
noncomputable def cssRun (C : EvolvingCSS) (A : RestrictedDec.Adversary) (lam Q D : ℕ)
    (b : Bool) (sh0 : Str) : ℕ → EvolvingGraph → Str → List Str → Finset ℕ → Str → Str → PMF Bool
  | 0, _, _, _, _, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, G, dealer, shares, corrupt, ast, input =>
      (A.activate lam ast input).bind fun r =>
        match decCSSMove r.2 with
        | .add S =>
            if S ⊆ Finset.Icc 1 G.length ∧ S.card ≤ D then
              (C.addVertex lam Q D (G.length + 1) dealer S).bind fun z =>
                cssRun C A lam Q D b sh0 fuel (G ++ [S]) z.2 (shares ++ [z.1]) corrupt r.1
                  (encBin (G.length + 1))
            else PMF.uniformOfFintype Bool
        | .corrupt v =>
            if v ∈ Finset.Icc 1 G.length then
              cssRun C A lam Q D b sh0 fuel G dealer shares (insert v corrupt) r.1
                (shares.getD (v - 1) [])
            else cssRun C A lam Q D b sh0 fuel G dealer shares corrupt r.1 []
        | .guess b' =>
            if corrupt.card ≤ Q ∧ G.Independent corrupt then PMF.pure (decide (b' = b))
            else PMF.uniformOfFintype Bool

/-- The adversary selects unary bounds `(Q,Δ)` before setup. -/
noncomputable def cssGame (C : EvolvingCSS) (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] []).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let Q := BeyondDS.decNat (fs.getD 0 [])
    let D := BeyondDS.decNat (fs.getD 1 [])
    if 1 ≤ Q ∧ 1 ≤ D then
      (PMF.uniformOfFintype Bool).bind fun b => (C.setup lam Q D b).bind fun z =>
        cssRun C A lam Q D b z.1 (A.p.eval lam + 1) [] z.2 [] ∅ r0.1 z.1
    else PMF.uniformOfFintype Bool

def EvolvingCSS.AdaptivelySecure (C : EvolvingCSS) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((cssGame C A lam) true).toReal - 1 / 2|

def EvolvingCSS.IsScheme (C : EvolvingCSS) : Prop :=
  C.Efficient ∧ C.Correct ∧ C.AdaptivelySecure

/-- Unbounded collusion and degree: with `Q = Δ = 2^λ` supplied in binary, every vertex share
has size polynomial in `λ`, independently of the number of vertices, its degree, and the number of
corruptions (Definition 6.16, Variants, p.52). -/
def EvolvingCSS.UnboundedCollusionDegree (C : EvolvingCSS) : Prop :=
  C.EfficientWithBounds encBin encBin ∧
    ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → ∀ s : Bool,
      ∀ z ∈ (C.setup lam (2 ^ lam) (2 ^ lam) s).support,
        ∀ t st S, S ⊆ Finset.Icc 1 (t - 1) →
          ∀ out ∈ (C.addVertex lam (2 ^ lam) (2 ^ lam) t st S).support,
            out.1.length ≤ (lam + 2) ^ c

def firstEdge (G : EvolvingGraph) (A : Finset ℕ) : ℕ × ℕ :=
  let vs := A.filter fun v => (A.filter fun u => u < v ∧ u ∈ G.getD (v - 1) ∅).Nonempty
  if hv : vs.Nonempty then
    let v := vs.min' hv
    let us := A.filter fun u => u < v ∧ u ∈ G.getD (v - 1) ∅
    if hu : us.Nonempty then (us.min' hu, v) else (1, 1)
  else (1, 1)

open Classical in
/-- Construction 6.17 from a bit-message RPPS. The state retains `pp` because the Lean syntax
passes implicit public parameters explicitly; this does not change any visible share or game. -/
noncomputable def construction617 (E : RPPS) : EvolvingCSS where
  setup lam _ _ s := (E.setup lam (2 ^ lam)).map fun z => (z.1, BeyondDS.tup [z.1, z.2, [s]])
  addVertex lam _ _ t st S :=
    let fs := BeyondDS.untup st
    let pp := fs.getD 0 []
    let msk := fs.getD 1 []
    let s := (fs.getD 2 []).headD false
    (E.kgen lam (2 ^ lam) pp msk S).bind fun sk =>
      (E.skEnc lam (2 ^ lam) pp msk t [s]).map fun ct => (BeyondDS.tup [sk, ct], st)
  recon lam G A pp shares :=
    if G.ContainsEdge A then
      let p := firstEdge G A
      let vf := BeyondDS.untup (shares.getD (p.2 - 1) [])
      let uf := BeyondDS.untup (shares.getD (p.1 - 1) [])
      (E.decode lam (2 ^ lam) pp (G.getD (p.2 - 1) ∅) (vf.getD 0 []) p.1
        (uf.getD 1 [])).bind List.head?
    else none

/-- In Construction 6.17 the public share is exactly the RPPS public parameters for `2^λ`
indices (Theorem 6.19, p.53). -/
def Construction617PublicShare (E : RPPS) (C : EvolvingCSS) : Prop :=
  ∀ lam Q D s, C.setup lam Q D s = (E.setup lam (2 ^ lam)).map fun z =>
    (z.1, BeyondDS.tup [z.1, z.2, [s]])

end PPSLattice.Supplement


