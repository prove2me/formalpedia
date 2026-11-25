-- Prove2me | Definitions.Def_DetDLP_S8C_WireBTN
-- name    : DetDLP_S8C_WireBTN
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:07:16.522462+00:00
-- url     : https://prove2.me/theorems/3dcf55df-ef91-4d34-86fd-aab4de075465
-- title:
--   Boolean wire subdivision and counting
-- statement:
--   Subdivision with equality tensors preserves each assignment uniquely. A bijection of satisfying wire assignments with a finite set identifies its cardinality with the output count for a parsimonious Boolean tensor network.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_W4_M5Subdivision
import Definitions.Def_DetDLP_S8C_TagSpec
set_option autoImplicit false
namespace DetDLP.S8C
open w4_M5Network
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

abbrev WireTest (G : WireGraph) := (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool

/-- Exposing all wire values avoids an additional choice of interface coordinates. -/
noncomputable def wireAccept (G : WireGraph) (T : WireTest G) (x : Fin G.nE → Bool) : Bool := by
  classical exact decide (G.Satisfies T x)

@[simp] theorem wireAccept_iff (G : WireGraph) (T : WireTest G) (x : Fin G.nE → Bool) :
    wireAccept G T x = true ↔ G.Satisfies T x := by classical simp [wireAccept]

theorem wireParsimonious (G : WireGraph) (T : WireTest G) :
    IsParsimonious G.subdivision (G.subdivisionTensor T) G.leftHalf (fun x => wireAccept G T x = true) := by
  apply G.subdivision_isParsimonious T id
  refine ⟨Function.injective_id, fun z => ⟨?_,?_⟩⟩
  · intro h; exact ⟨z, ⟨fun _ => rfl,(wireAccept_iff ..).mp h⟩,fun x hx => funext hx.1⟩
  · rintro h ⟨x,hx,ht⟩; have he : x = z := funext hx
    exact h ((wireAccept_iff ..).mpr (he ▸ ht))

theorem wireCard {A : Type} [Fintype A] (G : WireGraph) (T : WireTest G)
    (e : {x // G.Satisfies T x} ≃ A) :
    (Finset.univ.filter (fun x => wireAccept G T x = true)).card = Fintype.card A := by
  classical
  let F := Finset.univ.filter (fun x => wireAccept G T x = true)
  let f : {x // x ∈ F} ≃ {x // G.Satisfies T x} := Equiv.subtypeEquivRight (fun x => by simp [F])
  exact (Fintype.card_coe F).symm.trans (Fintype.card_congr (f.trans e))

/-- Adapter for any concrete family of raw wire graphs. Its caller supplies only
    arithmetic semantics, uniform encoded outputs, and numerical shape bounds. -/
theorem wireRealizes (make port : List Bool → List Bool) (L s b : ℕ) (w : List Bool)
    (G : WireGraph) (T : WireTest G) {A : Type} [Fintype A]
    (e : {x // G.Satisfies T x} ≃ A) (hs : 2 ≤ s) (hb : b ≤ s)
    (he : 2*G.nE < s) (hv : G.nV+G.nE ≤ s^L)
    (hd : max (Finset.univ.sup G.deg) 2 ≤ Nat.ceil ((s : ℝ)^((9 : ℝ)/10)))
    (h1 : s + w.length ≤ L * blockCount b * b) (h2 : s + w.length ≤ L*(b+1)^L)
    (hm : make w = encodeBTNInstance w G.subdivision s s 1)
    (hp : ∀ (v : Fin G.subdivision.nV) (a : Fin (G.subdivision.deg v) → Bool),
      let z := encodePortQuery w v.val (List.ofFn a)
      z.length ≤ L*(s+w.length+1)^L ∧ port z = encodeNatListBin [if G.subdivisionTensor T v a then 1 else 0]) :
    Realizes make port L w b (Fintype.card A) := by
  exact ⟨s,G.subdivision,G.subdivisionTensor T,G.nE,G.leftHalf,wireAccept G T,wireParsimonious G T,
    wireCard G T e,hs,hb,by simpa using he,hv,(G.subdivision_maxDeg_le _ fun v =>
      Finset.le_sup (f := G.deg) (Finset.mem_univ v)).trans hd,h1,h2,hm,hp⟩

end DetDLP.S8C


