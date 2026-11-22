-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintSubtreeDet20261120
-- name    : LinearSetReconciliation327_Main_HintSubtreeDet20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:26:50.742899+00:00
-- url     : https://prove2.me/theorems/c034dbf5-416d-4970-975a-13ed252d366d
-- title:
--   LinearSetReconciliation327 — HintSubtreeDet (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintSubtreeDet20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintSubtreeTable20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintChildUpdateAction20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- The saved updater keeps its original wire format. Slot 3 gives the calling
decoder's control address when the updater is used as a subtree action. -/
def hintSubtreeDet (W control colBase : ℕ) (items : List UpIt) (columns : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (upDet items.length W colBase items columns) 3 control

theorem hintSubtreeDet_specs (E : RAMEnv) (detBase control colBase tabLen : ℕ)
    (items : List UpIt) (columns : ℕ → ℕ)
    (hCol : 8 + 16 * items.length ≤ colBase)
    (hEnd : colBase + tabLen < 2 ^ E.W)
    (hSpace : detBase + (colBase + tabLen) ≤ 2 ^ E.W)
    (hPlaced : ∀ a < colBase + tabLen,
      E.det (detBase + a) = hintSubtreeDet E.W control colBase items columns a)
    (hFields : ∀ it ∈ items, ∀ f < 16, it.fld f < 2 ^ E.W)
    (hKinds : ∀ it ∈ items, UpItemKind it)
    (hSaves : ∀ it ∈ items, 2 ≤ it.mode → it.sav + 1 < 2 ^ E.W) :
    UpSavedLayout E detBase items ∧
    E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length ∧
    E.det (detBase + 3) = control := by
  have hShift (a : ℕ) (ha : a < colBase + tabLen) :
      (upShiftDetEnv E detBase).det a = hintSubtreeDet E.W control colBase items columns a := by
    change E.det ((detBase + a) % 2 ^ E.W) = _
    rw [Nat.mod_eq_of_lt (by omega : detBase + a < 2 ^ E.W)]
    exact hPlaced a ha
  refine ⟨⟨by omega, ?_, ?_, hKinds, hSaves⟩, ?_, ?_⟩
  · intro j hj f hf
    have ha : 8 + 16 * j + f < colBase + tabLen := by omega
    have hne : 8 + 16 * j + f ≠ 3 := by omega
    have hb := hFields items[j] (List.getElem_mem hj) f hf
    rw [hShift _ ha, hintSubtreeDet, Function.update_of_ne hne, Nat.add_assoc,
      upDet_item _ _ _ _ _ j f hj hf hCol]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
      Nat.mod_eq_of_lt hb]
  · change (upShiftDetEnv E detBase).det (1 % 2 ^ E.W) % 2 ^ E.W = E.W
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ E.W), hShift 1 (by omega)]
    simp [hintSubtreeDet, Nat.mod_eq_of_lt (Nat.lt_two_pow_self : E.W < 2 ^ E.W)]
  · rw [Nat.mod_eq_of_lt (by omega : detBase < 2 ^ E.W)]
    have h := hPlaced 0 (by omega)
    rw [Nat.add_zero] at h
    rw [h]
    simp [hintSubtreeDet, upDet, Nat.mod_eq_of_lt (by omega : items.length < 2 ^ E.W)]
  · rw [hPlaced 3 (by omega)]
    simp [hintSubtreeDet]

theorem hintSubtreeLocal_of_placed (CR : CRFamily) (P : HintParams) (R T : Node)
    (hT : IsSchemeTree P T) (rPublic : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ)
    (detBase control Bc colBase U i k : ℕ) (items : List UpIt) (columns : ℕ → ℕ)
    (hW : 1 < 2 ^ W) (hWpos : 0 < W) (hFits : (hintSpec R).Fits W)
    (hCol : 4 < colBase) (hU : U ≤ 2 ^ W)
    (hBlock : BlockOf R k (schemeNodes T)) (hStatic : UpTreeStatic CR Bc U T)
    (hFull : UpTabFullTree CR Bc columns T 0)
    (hEnd : colBase + upTabLen Bc T < 2 ^ W) (hBits : synLen CR T < 2 ^ W)
    (hSpace : detBase + (colBase + upTabLen Bc T) ≤ 2 ^ W)
    (hPlaced : ∀ a < colBase + upTabLen Bc T,
      det (detBase + a) = hintSubtreeDet W control colBase items columns a) :
    UpLocalTree CR (upShiftDetEnv ((hintSpec R).env W det rPublic) detBase)
      i Bc colBase T (hintKappaAux P R rPublic T hT k) k 0 0 := by
  let E := upShiftDetEnv ((hintSpec R).env W det rPublic) detBase
  let F := (hintSpec R).env W (upDet items.length W colBase items columns) rPublic
  have hShift (a : ℕ) (ha : a < colBase + upTabLen Bc T) (hne : a ≠ 3) :
      E.det a = F.det a := by
    change det ((detBase + a) % 2 ^ W) = upDet items.length W colBase items columns a
    rw [Nat.mod_eq_of_lt (by omega : detBase + a < 2 ^ W), hPlaced a ha,
      hintSubtreeDet, Function.update_of_ne hne]
  apply UpLocalTree.of_table_extension CR E F i Bc colBase hW rfl rfl rfl
    (hShift 0 (by omega) (by decide)) (hShift 1 (by omega) (by decide))
  · change colBase + 0 + upTabLen Bc T < 2 ^ W
    simpa only [Nat.add_zero] using hEnd
  · intro a ha hb
    exact hShift a (by omega) (by omega)
  · exact upLocalTree_of_tables CR P R W items.length Bc colBase U items columns rPublic i
      hW hWpos hFits hCol hU T hT k 0 0 hBlock hStatic hFull (by simpa using hEnd) (by simpa using hBits)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintSubtreeDet_specs
#print axioms LinearSetReconciliation327.Main.hintSubtreeLocal_of_placed


