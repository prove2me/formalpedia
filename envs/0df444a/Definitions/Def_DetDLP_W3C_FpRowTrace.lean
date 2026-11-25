-- Prove2me | Definitions.Def_DetDLP_W3C_FpRowTrace
-- name    : DetDLP_W3C_FpRowTrace
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:24:49.410003+00:00
-- url     : https://prove2.me/theorems/b5455fb6-4f8d-561b-8328-774701b34fc1
-- title:
--   Finite-field prefix descent and certified row updates
-- statement:
--   For a positive root the greedy prefix search selects a violated exact shift row. Slot 8 consumes its canonical HNF query and returns a valid encoded coset preserving the true label and halving the cardinality.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpTraceStep
import Definitions.Def_DetDLP_W3C_FpOracles
import Definitions.Def_DetDLP_W3C_FpLoopSound

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpRowTrace
open FpTraceStep FpStep BlockLookup

/-- One prefix descent and one exact HNF intersection preserve the true label,
    while halving the represented coset when the selected row is violated. -/
theorem descend_update {q : w3_Query} {L : ℕ} (width : ∀ X Y, (q.code X Y).length = L)
    {u : List Bool} (hu : u.length < L) (hroot : 0 < w3c_massAt q u)
    {pos : Bool} (hpos : pos = decide (0 < w3c_massAt q (u ++ [false])))
    {M N : ℕ} [NeZero M] {z : w3_Label M N} {s t : w3_Rep M N}
    {r : w3_Row M N} (hs : Stage2Trace.Invariant z s) (hr : w3_holds r z)
    (hupt : w3_update r s t)
    (half : 2 * Nat.card (w3_coset t) ≤ Nat.card (w3_coset s))
    {k : ℕ} (cap : Nat.card (w3_coset s) ≤ 2^(k+1)) :
    (u ++ [!pos]).length = u.length + 1 ∧
      0 < w3c_massAt q (u ++ [!pos]) ∧
      Stage2Trace.Invariant z t ∧ Nat.card (w3_coset t) ≤ 2^k := by
  obtain ⟨hlen, hmass⟩ := prefix_invariant q width hu hroot hpos
  obtain ⟨hinv, hcap⟩ := hnf_invariant hs hr hupt half cap
  exact ⟨hlen, hmass, hinv, hcap⟩

/-- The machine's phase-8 query is exactly the mathematical HNF update input. -/
theorem update_query_exact {M N : ℕ} [NeZero M] (s : FpState)
    (x : Fin N → ℕ) (B : Matrix (Fin N) (Fin N) ℤ) (r : Fin N → ZMod M)
    (rhs : ℕ) (raw : List ℤ) (hM : s.p - 1 = M)
    (hN : (decodeBlocks s.blocksWord).flatten.length + 2 = N)
    (hr : raw.map (fun z : ℤ => (z : ZMod M)) = List.ofFn r) :
    queryInput 8 {s with repWord := encodeCosetRep x B, pktWord := rowPkt M rhs raw} =
      encodeCosetUpdateInput M x B (fun i => (r i).val) rhs :=
  update_input s x B r rhs raw hM hN hr

open FpOracles NineOracleLoop FpLoopSound
abbrev calls {en de : Port} (kit : Kit en de) (t s : ℝ) := NineCall (family kit) (outputs kit) t s

/-- The answer actually read at slot 8 encodes the new representative.
    Its oracle budget depends on dimension and modulus, not on the prefix. -/
theorem update_call {en de : Port} (kit : Kit en de) {M N : ℕ} [NeZero M]
    (hM : 2 ≤ M) (hN : 1 ≤ N) (s : FpState) (rep : w3_Rep M N) (row : w3_Row M N)
    (z : w3_Label M N) (inv : Stage2Trace.Invariant z rep) (hz : w3_holds row z)
    (raw : List ℤ) (hm : s.p-1 = M) (hn : (decodeBlocks s.blocksWord).flatten.length+2 = N)
    (hraw : raw.map (fun x : ℤ => (x : ZMod M)) = List.ofFn row.1) :
    ∃ rep' : w3_Rep M N, w3_update row rep rep' ∧ Stage2Trace.Invariant z rep' ∧
      (¬w3_holds row rep.1 → 2*Nat.card (w3_coset rep') ≤ Nat.card (w3_coset rep)) ∧
      let v := {s with repWord := encodeCosetRep (fun i => (rep.1 i).val) rep.2,
                       pktWord := rowPkt M row.2.val raw}
      let budget := polyBound kit.updateC (N+bitLen M)
      calls kit budget budget (tag9 8 (queryInput 8 v))
        (encodeCosetRep (fun i => (rep'.1 i).val) rep'.2) := by
  obtain ⟨rep',hu,hh,hr⟩ := kit.update M N hM hN rep row inv.1 ⟨z,inv.2,hz⟩
  refine ⟨rep',hu,Stage2Trace.preserve inv.2 hz hu,hh,8,_,rfl,?_⟩
  rw [update_query_exact s _ _ row.1 _ raw hm hn hraw]
  exact hr

/-- A positive root determines the complete row word and the corresponding
    certified HNF call. The retained true label bounds the remaining cuts. -/
theorem positive_row {en de : Port} (kit : Kit en de) (q : w3_Query) {L k : ℕ}
    (width : ∀ X Y, (q.code X Y).length = L) (inj : Function.Injective (Function.uncurry q.code))
    (hM : 2 ≤ q.M) (z : w3_Label q.M q.FB.totalCoords) (pass : w3_pass q.FB q.M q.P z)
    (rep : w3_Rep q.M q.FB.totalCoords) (hy : q.y = rep.1) (inv : Stage2Trace.Invariant z rep)
    (cap : Nat.card (w3_coset rep) ≤ 2^(k+1)) (hp : 0 < w3c_massAt q [])
    (s : FpState) (hm : s.p-1 = q.M) (enc : q.V → List Bool)
    (hn : (decodeBlocks s.blocksWord).flatten.length+2 = q.FB.totalCoords)
    (nd : ∀ i, ((q.FB.blocks i).map enc).Nodup) :
    ∃ X Y rep', q.code X Y = DetDLP_W3C_PrefixSearch (w3c_massAt q) L ∧
      w3_cut q.FB q.M q.P rep rep' ∧ Stage2Trace.Invariant z rep' ∧ Nat.card (w3_coset rep') ≤ 2^k ∧
      let raw := shiftRowCounts (blocks q.FB enc) (words q.FB enc X) (words q.FB enc Y)
      let v := {s with repWord := encodeCosetRep (fun i => (rep.1 i).val) rep.2,
                       pktWord := rowPkt q.M (w3_shiftRow q.FB q.M X Y).2.val raw}
      let budget := polyBound kit.updateC (q.FB.totalCoords+bitLen q.M)
      calls kit budget budget (tag9 8 (queryInput 8 v)) (encodeCosetRep (fun i => (rep'.1 i).val) rep'.2) := by
  obtain ⟨_,_,⟨X,Y⟩,⟨he,hg,hw,hbad⟩,_⟩ := w3c_descent q width inj hM hp
  rw [hy] at hw hbad
  have raw := congrArg Prod.fst (shiftRowCounts_correct q.FB enc nd q.M X Y)
  obtain ⟨rep',hu,hi,hh,call⟩ := update_call kit hM q.FB.genCoord.pos s rep _ z inv
    (pass X Y hg) _ hm hn raw
  have half := hh hbad
  exact ⟨X,Y,rep',he,⟨X,Y,hg,hw,hbad,hu,half⟩,hi,(hnf_invariant inv (pass X Y hg) hu half cap).2,call⟩

end DetDLP.W3C.FpRowTrace


