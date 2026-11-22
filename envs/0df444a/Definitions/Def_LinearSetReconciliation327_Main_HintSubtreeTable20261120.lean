-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintSubtreeTable20261120
-- name    : LinearSetReconciliation327_Main_HintSubtreeTable20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:59:55.256257+00:00
-- url     : https://prove2.me/theorems/27a2d7dc-dfa6-40ea-a839-f0f9f9a14450
-- title:
--   LinearSetReconciliation327 — HintSubtreeTable (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintSubtreeTable20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateLayout20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- Moving a subtree's deterministic table preserves its update semantics when the
count, width, and column slots agree and it retains its original public coins. -/
theorem UpLocalTree.of_table_extension (CR : CRFamily) (E F : RAMEnv)
    (i Bc colBase : ℕ) (hEW : 1 < 2 ^ E.W)
    (hW : E.W = F.W) (hPerm : E.perm = F.perm) (hCoeff : E.coeff = F.coeff)
    (h0 : E.det 0 = F.det 0) (h1 : E.det 1 = F.det 1) :
    ∀ (T : Node) (r : T.Seed) k base toff,
      colBase + toff + upTabLen Bc T < 2 ^ E.W →
      (∀ a, colBase + toff ≤ a → a < colBase + toff + upTabLen Bc T → E.det a = F.det a) →
      UpLocalTree CR F i Bc colBase T r k base toff →
      UpLocalTree CR E i Bc colBase T r k base toff := by
  intro T
  induction T with
  | store N =>
      intro r k base toff hEnd hAgree hOld
      exact UpLocalBitsCorrect.of_table_extension CR E F i Bc colBase (.store N) r
        k base toff hEW hW hPerm hCoeff h0 h1 hEnd hAgree hOld
  | cr N t =>
      intro r k base toff hEnd hAgree hOld
      exact UpLocalBitsCorrect.of_table_extension CR E F i Bc colBase (.cr N t) r
        k base toff hEW hW hPerm hCoeff h0 h1 hEnd hAgree hOld
  | direct sch t =>
      intro r k base toff hEnd hAgree hOld
      exact UpLocalBitsCorrect.of_table_extension CR E F i Bc colBase (.direct sch t) r
        k base toff hEW hW hPerm hCoeff h0 h1 hEnd hAgree hOld
  | recursive sch t Xs Ys child ih =>
      intro r k base toff hEnd hAgree hOld
      refine ⟨?_, hOld.2.1, ?_, ?_⟩
      · exact UpLocalBitsCorrect.of_table_extension CR E F i Bc colBase
          (.recursive sch t Xs Ys child) r k base toff hEW hW hPerm hCoeff h0 h1 hEnd hAgree hOld.1
      · intro c f hcN hc hf hf01 s
        apply UpEdgeData.of_env F E i k sch r.1 s c f hW.symm hPerm.symm hCoeff.symm
        apply hOld.2.2.1 c f hcN
        · rwa [← hW]
        · rwa [← hW]
        · exact hf01
      · intro s
        have hTop : upKidOff Bc sch child toff s.val + upTabLen Bc (child s) ≤
            toff + upTabLen Bc (.recursive sch t Xs Ys child) :=
          upKidOff_le_top Bc sch child toff s.val s.isLt
        have hLower : toff ≤ upKidOff Bc sch child toff s.val := by
          unfold upKidOff
          omega
        apply ih s (r.2 s) _ _ (upKidOff Bc sch child toff s.val) (by omega) ?_ (hOld.2.2.2 s)
        intro a ha hb
        exact hAgree a (by omega) (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.UpLocalTree.of_table_extension


