-- Prove2me | Definitions.Def_FixedPolyominoSquare_SquareCounting_Amplifier
-- name    : FixedPolyominoSquare_SquareCounting_Amplifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:55.00851+00:00
-- url     : https://prove2.me/theorems/d57c4c09-a51f-4d5d-acdb-177d87c914bf
-- title:
--   The four coupled side-activity tracks and private dummy
-- statement:
--   For fixed $Q\geq1$, a tile carries four activity bits and one index for each side. Inactive indices are normalized, and adjacent active sides on a tile have equal indices. Opposite active sides retain independent indices when no adjacent active side joins them. The colours are the actual four-coordinate atomic labels from the source, with the twelve fixed atoms distinct from the four families of dead labels.
--
--   $$W_{\rm col}=H(w_W,g_E,s_c,n_c),\quad E_{\rm col}=H(g_W,e_E,s_c,n_c),\quad S_{\rm col}=V(w_c,e_c,s_S,g_{Nv}),\quad N_{\rm col}=V(w_c,e_c,g_{Sv},n_N).$$
--
--   The activity class specifies a constant bit on each geometric boundary side. Its count filters all open assignments by those boundary bits. The dummy has a fresh colour on every edge, disjoint from every existing colour, and is adjoined as one extra tile type. The indices $1,\ldots,Q$ are represented by $\operatorname{Fin}(Q)$, so the normalized inactive value is zero rather than one; this is a bijective relabeling.
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), pp. 10–11, Theorem 5.1 and its local rules

import Mathlib
import Definitions.Def_FixedPolyominoSquare_SquareCounting_WangModel

namespace FixedPolyominoSquare.SquareCounting

noncomputable section
attribute [local instance] Classical.propDecidable

def perpendicularSides (D E : Fin 4) : Prop :=
  (D.val < 2 ∧ 2 ≤ E.val) ∨ (E.val < 2 ∧ 2 ≤ D.val)

abbrev AmplifierData (Q : ℕ) :=
  {d : (Fin 4 → Bool) × (Fin 4 → Fin Q) //
    (∀ D, d.1 D = false → (d.2 D).val = 0) ∧
    (∀ D E, perpendicularSides D E → d.1 D = true → d.1 E = true → d.2 D = d.2 E)}

instance amplifierDataFintype (Q : ℕ) : Fintype (AmplifierData Q) := Fintype.ofFinite _

/-- Twelve private fixed atoms, and four disjoint families of dead labels. -/
abbrev AmplifierAtom (Q : ℕ) := Fin 12 ⊕ (Fin 4 × Fin Q)
abbrev AmplifierColour (Q : ℕ) := Fin 4 → AmplifierAtom Q

def fixedAtom {Q : ℕ} (i : Fin 12) : AmplifierAtom Q := Sum.inl i
def deadAtom {Q : ℕ} (D : Fin 4) (q : Fin Q) : AmplifierAtom Q := Sum.inr (D, q)

/-- Fixed atoms in order: gW,gE,gS,gN,gWc,gEc,gSv,gNv,aW,aE,aS,aN. -/
def ampWest {Q : ℕ} (d : AmplifierData Q) : AmplifierColour Q :=
  ![if d.val.1 0 then deadAtom 0 (d.val.2 0) else fixedAtom 0,
    fixedAtom 1, if d.val.1 2 then fixedAtom 10 else fixedAtom 2,
    if d.val.1 3 then fixedAtom 11 else fixedAtom 3]

def ampEast {Q : ℕ} (d : AmplifierData Q) : AmplifierColour Q :=
  ![fixedAtom 0, if d.val.1 1 then deadAtom 1 (d.val.2 1) else fixedAtom 1,
    if d.val.1 2 then fixedAtom 10 else fixedAtom 2,
    if d.val.1 3 then fixedAtom 11 else fixedAtom 3]

def ampSouth {Q : ℕ} (d : AmplifierData Q) : AmplifierColour Q :=
  ![if d.val.1 0 then fixedAtom 8 else fixedAtom 4,
    if d.val.1 1 then fixedAtom 9 else fixedAtom 5,
    if d.val.1 2 then deadAtom 2 (d.val.2 2) else fixedAtom 6, fixedAtom 7]

def ampNorth {Q : ℕ} (d : AmplifierData Q) : AmplifierColour Q :=
  ![if d.val.1 0 then fixedAtom 8 else fixedAtom 4,
    if d.val.1 1 then fixedAtom 9 else fixedAtom 5, fixedAtom 6,
    if d.val.1 3 then deadAtom 3 (d.val.2 3) else fixedAtom 7]

def ampDataOf (Q : ℕ) (u : Fin (Fintype.card (AmplifierData Q))) : AmplifierData Q :=
  (Fintype.equivFin (AmplifierData Q)).symm u

def amplifier (Q : ℕ) : WangSystem where
  types := Fintype.card (AmplifierData Q)
  horizontal := Fintype.card (AmplifierColour Q)
  vertical := Fintype.card (AmplifierColour Q)
  west u := Fintype.equivFin _ (ampWest (ampDataOf Q u))
  east u := Fintype.equivFin _ (ampEast (ampDataOf Q u))
  south u := Fintype.equivFin _ (ampSouth (ampDataOf Q u))
  north u := Fintype.equivFin _ (ampNorth (ampDataOf Q u))

def onSide (n : ℕ) (p : Cell) (D : Fin 4) : Prop :=
  if D = 0 then p.1 = 0 else if D = 1 then p.1 = (n : ℤ) - 1 else
  if D = 2 then p.2 = 0 else p.2 = (n : ℤ) - 1

def InActivityClass (Q n : ℕ) (η : Fin 4 → Bool)
    (f : WangAssignment (amplifier Q) (square n)) : Prop :=
  ∀ p : square n, ∀ D, onSide n p.val D → (ampDataOf Q (f p)).val.1 D = η D

def activityCount (Q n : ℕ) (η : Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter fun f : WangAssignment (amplifier Q) (square n) =>
    WangMatches (amplifier Q) (square n) f ∧ InActivityClass Q n η f).card

/-- Dummy colour zero occurs nowhere in the old system, in either direction. -/
def withDummy (W : WangSystem) : WangSystem where
  types := W.types + 1
  horizontal := W.horizontal + 1
  vertical := W.vertical + 1
  west := Fin.cases 0 (fun u => (W.west u).succ)
  east := Fin.cases 0 (fun u => (W.east u).succ)
  south := Fin.cases 0 (fun u => (W.south u).succ)
  north := Fin.cases 0 (fun u => (W.north u).succ)

end
end FixedPolyominoSquare.SquareCounting


