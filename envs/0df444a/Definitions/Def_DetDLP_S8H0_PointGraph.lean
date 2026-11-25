-- Prove2me | Definitions.Def_DetDLP_S8H0_PointGraph
-- name    : DetDLP_S8H0_PointGraph
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:50:41.299554+00:00
-- url     : https://prove2.me/theorems/4a62b6a6-bfce-4a15-b0c4-e9a1d98236b4
-- title:
--   Graph-to-point bijection for the elliptic-curve order check
-- statement:
--   A copy-cycle wired graph has satisfying assignments in bijection with points on the input elliptic curve.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_GateSemantics

set_option autoImplicit false
namespace DetDLP.S8H0.PointGraph
open GateSemantics GateRoutes RegisterMap S8H.ECPointArithmetic S8H.ECPointSlots
open ResidueWires SignalBank NamedBlocks S8J.CircuitRealizes

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))

theorem curve_iff (u : U p) (h : canonical p (raw u)) :
    CurveRows.rawCheck (raw u) ↔ checkCurve (typed u h).1 (typed u h).2 := by
  let v := typed u h
  have hz (z : ZMod p) (a : Fin (2^(d p))) (he : z.val = a.val) : a = 0 ↔ z = 0 := by
    constructor
    · intro hh; apply ZMod.val_injective p; simpa only [hh,ZMod.val_zero,Fin.val_zero] using he
    · intro hh; apply Fin.ext; simpa [hh] using he.symm
  have heq (x y : ZMod p) (a b : Fin (2^(d p))) (hx : x.val = a.val) (hy : y.val = b.val) :
      a = b ↔ x = y := by
    constructor
    · intro h; apply ZMod.val_injective p; rw [hx,hy,h]
    · intro h; apply Fin.ext; rw [←hx,←hy,h]
  change (if (raw u).1.1 then _ else _) ↔ (if (raw u).1.1 then _ else _)
  cases (raw u).1.1 <;> simp only [Bool.false_eq_true,if_false,if_true]
  · exact heq _ _ _ _ (outVal u h 2) (outVal u h 5)
  · exact and_congr (hz _ _ (coordX u h)) (hz _ _ (coordY u h))

theorem network_accept (u : U p) : (network (hd p) p (coeff E)).OK u ↔ accepts E (raw u) := by
  refine (network_iff (hd p) p (coeff E) u).trans ?_; constructor
  · rintro ⟨h,g,c⟩
    exact ⟨h,(SevenChecks.physical_iff ..).mpr ⟨fun i => (hash_iff E u h i).mp (g i),(curve_iff u h).mp c⟩⟩
  · rintro ⟨h,ht⟩
    obtain ⟨hg,hc⟩ := (SevenChecks.physical_iff ..).mp ht
    exact ⟨h,fun i => (hash_iff E u h i).mpr (hg i),(curve_iff u h).mpr hc⟩

def zeroLast (n : ℕ) : B (n+1) :=
  ⟨⟨AnchoredLayout.anchors 1,fun g a => !(a ⟨g,rfl⟩)⟩,fun _ => Fin.last n⟩

theorem zeroLast_iff {n : ℕ} (u : Bits (n+1)) : (zeroLast n).OK u ↔ u (Fin.last n) = false := by
  change (∀ _ : Fin 1, Bool.not (u (Fin.last n)) = true) ↔ _
  simp

def net (p : ℕ) (c : Coeff) := joinB (zeroLast ((S (d p) (e p)).size)) (network (hd p) p c)

def dropLast {n : ℕ} : {u : Bits (n+1) // u (Fin.last n) = false} ≃ Bits n where
  toFun u := u.val ∘ Fin.castSucc
  invFun u := ⟨Fin.lastCases (motive := fun _ => Bool) false u,by simp⟩
  left_inv u := by
    apply Subtype.ext; funext i; induction i using Fin.lastCases with
    | last => simp [u.property]
    | cast i => simp
  right_inv u := by funext i; simp [Function.comp_def]

private def liftEq {A B : Type} {P : A → Prop} (e : {x // P x} ≃ B) (Q : B → Prop) :
    {x // ∃ h : P x, Q (e ⟨x,h⟩)} ≃ {z // Q z} where
  toFun x := ⟨e ⟨x.val,x.property.choose⟩,x.property.choose_spec⟩
  invFun z := ⟨(e.symm z.val).val,(e.symm z.val).property,by simpa using z.property⟩
  left_inv x := Subtype.ext (congrArg (fun a : {x // P x} => a.val) (e.symm_apply_apply ⟨x.val,x.property.choose⟩))
  right_inv z := Subtype.ext (e.apply_symm_apply z.val)

noncomputable def bankEquiv : {u // (net p (coeff E)).OK u} ≃ {w // accepts E w} := by
  let dec := dropLast.trans (S (d p) (e p)).decode
  refine (Equiv.subtypeEquivRight (q := fun u => ∃ h : u (Fin.last _) = false, accepts E (dec ⟨u,h⟩)) ?_).trans (liftEq dec _)
  intro u; rw [net,joinB_iff,zeroLast_iff,network_accept]; exact ⟨fun h => ⟨h.1,h.2⟩,fun ⟨h,a⟩ => ⟨h,a⟩⟩

abbrev C (p : ℕ) (c : Coeff) := AnchoredLayout.block (net p c).core ((S (d p) (e p)).size+1)
abbrev W (p : ℕ) (c : Coeff) := AnchoredLayout.wiring (net p c).core (net p c).name
abbrev layout (p : ℕ) (c : Coeff) := circuit (C p c) (W p c)
abbrev tests (p : ℕ) (c : Coeff) := test (C p c) (W p c)

noncomputable def logicalEquiv : Logical (C p (coeff E)) (W p (coeff E)) ≃ {w // accepts E w} :=
  (AnchoredLayout.assignments _ _).trans (bankEquiv E)

noncomputable def points [E.IsElliptic] :
    {x // (w3_factorGraph (layout p (coeff E))).Satisfies (w3_factorChecks _ (tests p (coeff E))) x} ≃ E.toAffine.Point :=
  (S8J.CircuitRealizes.decode _ _).trans ((logicalEquiv E).trans (orderPoints E))

end DetDLP.S8H0.PointGraph


