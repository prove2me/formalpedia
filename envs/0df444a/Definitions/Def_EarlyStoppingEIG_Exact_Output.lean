-- Prove2me | Definitions.Def_EarlyStoppingEIG_Exact_Output
-- name    : EarlyStoppingEIG_Exact_Output
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:22.817303+00:00
-- url     : https://prove2.me/theorems/4f367731-535d-405d-b2d3-0303ba6a45cb
-- title:
--   Signed-message reconstruction, completion and root resolution
-- statement:
--   The output subroutine uses the invoking party’s actual view through horizon $h$. It reconstructs entries at depths $d=h,\ldots,2$ and rounds $2\le u\le d$. Own messages and leaf direct receipts are used literally. Internal entries retain only observed signed round-$u$ messages supported by at least $n-t-d$ distinct children. Support is an exact acknowledged receipt, a permitted star completion, or bit-specific $V_b$ completion at round three.
--
--   $$\operatorname{out}_i(h)=1\iff\text{a sender signature on 1 was seen and at least }n-t-1\text{ root children resolve to 1}.$$
--
--   Empty round-three entries receive every justified $V_b$. For $u\ge4$ an empty entry becomes $\star$ only when the specified earlier signed evidence exists. Entries can contain multiple signatures or both bit markers. Markers are local values and cannot be sent as signatures. Reconstruction is represented by finite depth recursion and increasing-round folds.
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), §3.3, pp.18–20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_Messages

namespace EarlyStoppingEIG.Exact

/-- The last three constructors belong only to local reconstruction; wire
messages contain none of these markers. -/
inductive EntryAtom (P : Parameters) where
  | signed : Message P → EntryAtom P
  | bitMarker : Bool → EntryAtom P
  | star : EntryAtom P

abbrev Entry (P : Parameters) := Set (EntryAtom P)
abbrev EntryTable (P : Parameters) := ℕ → Entry P

def EntryReportsBit (P : Parameters) (j : Party P) (e : Entry P) (b : Bool) : Prop :=
  ∃ m, EntryAtom.signed m ∈ e ∧ ReportsBit P j m b

def Supports (P : Parameters) (j k : Party P) (u : ℕ) (m : Message P)
    (child : Entry P) : Prop :=
  (∃ a, EntryAtom.signed a ∈ child ∧ WellFormed P (u + 1) k a ∧
    reported k (u + 1) a j = some (some m)) ∨
  (3 ≤ u ∧ child = {EntryAtom.star}) ∨
  (u = 2 ∧ ∃ b, ReportsBit P j m b ∧ EntryAtom.bitMarker b ∈ child)

/-- Complete an empty entry, using only earlier entries of this same node.
In round three both bit markers can be present. -/
noncomputable def completeEntry (P : Parameters) (j : Party P) (u : ℕ)
    (earlier : EntryTable P) (retained : Entry P) : Entry P := by
  classical
  exact if retained ≠ ∅ then retained else
    if u = 3 then {a | ∃ b, a = EntryAtom.bitMarker b ∧ EntryReportsBit P j (earlier 2) b}
    else if 4 ≤ u ∧ ((∃ b, EntryReportsBit P j (earlier 2) b) ∨
      ∃ v, 3 ≤ v ∧ v < u ∧ ∃ m, EntryAtom.signed m ∈ earlier v)
      then {EntryAtom.star} else ∅

/-- One node, with its children already computed. Earlier rounds are filled in
increasing order; only signed messages actually seen by the horizon can be
retained at an internal node. -/
noncomputable def computeNode (P : Parameters) (i : Party P) (v : LocalView P)
    (h : ℕ) (w : List (Party P)) (children : Party P → EntryTable P) : EntryTable P := by
  classical
  exact (List.range (w.length + 1)).foldl (fun table u =>
    if 2 ≤ u ∧ u ≤ w.length then
      let j := w.getLastD P.sender
      let retained : Entry P :=
        if j = i then {a | ∃ m, v.own u = some m ∧ a = EntryAtom.signed m}
        else if w.length = h then
          {a | ∃ m, v.receipt u j = some m ∧ a = EntryAtom.signed m}
        else {a | ∃ m, a = EntryAtom.signed m ∧ Seen P v h m ∧ WellFormed P u j m ∧
          P.n - P.t - w.length ≤
            (Finset.univ.filter (fun k => k ∉ w ∧ Supports P j k u m (children k (u + 1)))).card}
      Function.update table u (completeEntry P j u table retained)
    else table) (fun _ => ∅)

/-- Bottom-up reconstruction. The fuel is the remaining depth, and is always
instantiated by h minus the node depth. No theorem or agreement certificate
occurs in this computation. -/
noncomputable def reconstructAux (P : Parameters) (i : Party P) (v : LocalView P)
    (h : ℕ) : ℕ → List (Party P) → EntryTable P
  | 0, w => computeNode P i v h w (fun _ _ => ∅)
  | fuel + 1, w => computeNode P i v h w
      (fun k => reconstructAux P i v h fuel (w ++ [k]))

noncomputable def reconstructed (P : Parameters) (i : Party P) (v : LocalView P)
    (h : ℕ) (w : List (Party P)) (u : ℕ) : Entry P := by
  classical
  exact if IsPath P w ∧ 2 ≤ w.length ∧ w.length ≤ h ∧ 2 ≤ u ∧ u ≤ w.length
    then reconstructAux P i v h (h - w.length) w u else ∅

noncomputable def rootChildOne (P : Parameters) (i : Party P) (v : LocalView P)
    (h : ℕ) (j : Party P) : Prop :=
  EntryReportsBit P j (reconstructed P i v h [P.sender, j] 2) true

/-- ΠOutput, pp.19–20. The entry functions describe the reconstruction even
when the first line returns zero without needing to evaluate them. -/
noncomputable def output (P : Parameters) (i : Party P) (v : LocalView P) (h : ℕ) : Bool := by
  classical
  exact if (∃ m, Seen P v h m ∧ IsSenderBit P m true) ∧
    P.n - P.t - 1 ≤ (Finset.univ.filter (fun j => j ≠ P.sender ∧ rootChildOne P i v h j)).card
    then true else false

end EarlyStoppingEIG.Exact


