-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxDParent
-- name    : BS2_b3ba934b_MinmaxDParent
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:39:19.723648+00:00
-- url     : https://prove2.me/theorems/2113d624-b770-490a-85b0-753a4bda0e5b
-- title:
--   Sensitivity separation: MinmaxDParent (complete source module)
-- statement:
--   Complete Lean source module `MinmaxDParent` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxDParent.lean; original SHA-256 3945389ddc88d3ad9b7f0780f078547da9b461dcb9289fc3bb8aabcb51d48010; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The strict oriented-union estimate for actual graded min/max parents. -/
import Definitions.Def_BS2_b3ba934b_MinmaxStrictUnion

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxTransfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional
open scoped Classical
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem mm_same (F : L → (I → Bool) → Bool) (t : L) (x y : I → Bool) :
    mm F t t x y=(F t x && F t y) := by
  cases hx : F t x <;> cases hy : F t y <;> simp [mm,hx,hy]

theorem minmax_plain_zero_parent (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l t : L) (hq : S.tolerance l=0)
    (hdef : ∀ u z, S.target l 0 u z=mm F t t u z) :
    parent S F l=ordinaryParent S F t (S.guard l) 0 := by
  funext x
  have hf (w : V) : failed S F l x w=guardFailures S F (S.guard l) x w := rfl
  have he : parent S F l x=true ↔ ordinaryParent S F t (S.guard l) 0 x=true := by
    rw [parent_true_iff,ordinary_parent_true]
    constructor
    · rintro ⟨w,hc,ht⟩
      have hc0 : (failed S F l x w).card=0 := by omega
      rw [hc0,hdef,mm_same] at ht
      refine ⟨w,?_,by simpa only [hf,hq] using hc⟩
      intro c
      cases c <;> simp_all
    · rintro ⟨w,ht,hc⟩
      have hc0 : (failed S F l x w).card=0 := by change (failed S F l x w).card ≤ 0 at hc; omega
      refine ⟨w,by omega,?_⟩
      rw [hc0,hdef,mm_same]
      simp only [ht,Bool.and_true]
  cases h1 : parent S F l x <;> cases h2 : ordinaryParent S F t (S.guard l) 0 x <;> simp_all

theorem minmax_strictD_parent (S : Stage L I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j k l : L) (P : PairData S F i j) (Q : PairData S F j k)
    (hjzero : S.tolerance j=0) (hlzero : S.tolerance l=0)
    (tl : L) (hldef : ∀ u z, S.target l 0 u z=mm F tl tl u z)
    (hujl : P.strongUpper 0 ≤ tl) (hukl : Q.strongUpper 0 ≤ tl)
    (hglgk : S.guard l ≤ S.guard k)
    (degree aM m0 m1 bm0 bm1 p b0 b1 aD dt dg : ℕ)
    (hd : ∀ v, (outgoing S v).card=degree)
    (haM : ABound F (S.guard j) (S.guard i) aM)
    (hm0 : MBound F (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) m0)
    (hm1 : MBound F (P.weakUpper 0) (P.strongUpper 0) (Q.strongUpper 0) m1)
    (hbm0 : BBound F (P.weakLower 0) (Q.strongLower 0) bm0)
    (hbm1 : BBound F (P.weakUpper 0) (Q.strongUpper 0) bm1)
    (hp : PBound F (S.guard k) (S.guard j) (S.guard i) p)
    (hb0 : BBound F (P.weakLower 0) tl b0) (hb1 : BBound F (P.weakUpper 0) tl b1)
    (haD : ABound F (S.guard l) (S.guard i) aD)
    (hdt : DBound F (P.weakLower 0) (P.strongLower 0) (Q.strongLower 0) tl dt)
    (hdg : DBound F (S.guard l) (S.guard k) (S.guard j) (S.guard i) dg) :
    DBound (parent S F) i j k l
      (max (pairMCost degree 0 (P.strongLower 0) (P.strongUpper 0) (Q.strongLower 0) (Q.strongUpper 0)
          (S.guard j) (S.guard k) aM m0 m1 bm0 bm1 p)
        (max (if P.strongLower 0<Q.strongLower 0 then b1+degree*aD+dt else 0)
          (if S.guard k<S.guard j then b0+b1+(degree-1)*aD+dg else 0))) := by
  intro x hxj hxk
  obtain ⟨v,hcount,hmm⟩ := (parent_true_iff S F j x).1 hxj
  have hjcount : (failed S F j x v).card=0 := by omega
  rw [hjcount,P.strongDef] at hmm
  have hnext : ∀ c, ¬orientedRow S F (Q.strongLower 0) (Q.strongUpper 0) (S.guard k) 0 x v c := by
    intro c hr
    have hon := oriented_implies_parent S F hF k Q.strongLower Q.strongUpper Q.strongLowerMono
      Q.strongUpperMono Q.strongLowerUpper Q.strongDef x v 0 c (Nat.zero_le _) hr
    rw [hxk] at hon
    contradiction
  have haccept : ∀ c y, orientedRow S F (P.weakLower 0) (P.weakUpper 0) (S.guard i) 0 y v c →
      parent S F i y=true := by
    intro c y hr
    exact oriented_implies_parent S F hF i P.weakLower P.weakUpper P.weakLowerMono P.weakUpperMono
      P.weakLowerUpper P.weakDef y v 0 c (Nat.zero_le _) hr
  have hgil : S.guard i ≤ tl := (P.weakGuardTarget 0 (Nat.zero_le _)).trans
    ((P.lowerOrder 0 (Nat.zero_le _)).trans ((P.strongLowerUpper 0 (Nat.zero_le _)).trans hujl))
  have hgli : S.guard l ≤ P.weakLower 0 :=
    hglgk.trans (Q.guards.trans (P.guards.trans (P.weakGuardTarget 0 (Nat.zero_le _))))
  rw [minmax_plain_zero_parent S F l tl hlzero hldef]
  have hbound := oriented_strictD S hT F hF (parent S F i)
    (P.weakLower 0) (P.weakUpper 0) (P.strongLower 0) (P.strongUpper 0)
    (Q.strongLower 0) (Q.strongUpper 0) tl (S.guard i) (S.guard j) (S.guard k) (S.guard l)
    (P.weakLowerUpper 0 (Nat.zero_le _)) (P.lowerOrder 0 (Nat.zero_le _)) (P.upperOrder 0 (Nat.zero_le _))
    hujl ((Q.strongLowerUpper 0 (Nat.zero_le _)).trans hukl) hukl
    P.guards Q.guards hglgk hgil hgli degree aM m0 m1 bm0 bm1 p b0 b1 aD dt dg
    haM hm0 hm1 hbm0 hbm1 hp hb0 hb1 haD hdt hdg x v (hd v) hmm hjcount hnext haccept
  convert hbound using 1
  congr 1
  ext bit
  simp only [Finset.mem_union]

end
end ThreeBoundMinmaxTransfer

#print axioms ThreeBoundMinmaxTransfer.minmax_strictD_parent


