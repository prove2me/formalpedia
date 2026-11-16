-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2Rec
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRun2Rec
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:15:44.20599+00:00
-- url     : https://prove2.me/theorems/a4df37e2-2ae8-4bb8-816e-808fb4f5e6f8
-- title:
--   R8 opp-bank OneRun2Rec channel on QHNetRec (single width-r child)
-- statement:
--   # Opp-bank `OneRun2Rec` channel
--
--   This is a `QHNetRec` fork of the published corrected one-run opp-bank channel `IntMul_Kappa_R8_Data_BitOppbankOneRun2`. The one-run predicate and the channel \(\mathrm{ch0O}\) are unchanged: each residual of rank \(r\) is a single child of width \(r\), with run list
--
--   $$
--   \mathrm{rs}=[(0,0,r)],
--   $$
--
--   matching Jain's \(\mathtt{bit\_hist.onerun\_hist}\) and \(\mathtt{edge\_of\_pivs}\) at rank \(r\), and avoiding the unsatisfiable length-\((r-1)\) ones-padding of the earlier \(\mathrm{OneRun.oneRun}\) predicate.
--
--   The network
--
--   $$
--   \mathrm{net0O}:\mathrm{QHNet}(\mathbb{Z}/2\mathbb{Z},\,104719230,\,3217907,\,529)
--   $$
--
--   is assembled as \(\mathrm{NB.net}(\mathrm{toNB}(\mathrm{ch0O}))\) at \(\mathrm{codeBound}=64251\), with the same edge families \(e_1,e_2,e_x,e_n,e_i,e_c\) as the parent. The only change is that the carrier import is the total-decoder network `IntMul_Kappa_R8_Data_BitOppbankQHNetRec` rather than `IntMul_Kappa_R8_Data_BitOppbankQHNet`. This lets later densify lemmas (prefix labels and \(\mathrm{LabGates}\)) import the one-run channel together with `QHNetRec` without mixing the two `NB` modules.
--
--   **Formalization Note.** The Lean namespace remains `IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2`. Do not import both `BitOppbankOneRun2` and `BitOppbankOneRun2Rec` in one file, and do not import both `BitOppbankQHNet` and `BitOppbankQHNetRec`. This definition does not close or replace `e0d447f6-cd60-4e42-86c4-534cc0c33db5`.
-- source:
--   Fork of published definition IntMul_Kappa_R8_Data_BitOppbankOneRun2 (definition_id e0d447f6-cd60-4e42-86c4-534cc0c33db5, created 2026-10-28): same corrected one-run opp-bank channel (Jain bit_hist.onerun_hist; single width-r child, no (r-1) pad) and net0O construction, retargeted to import IntMul_Kappa_R8_Data_BitOppbankQHNetRec (definition_id d127abea-7380-4a49-9c5c-c2103f068243, created 2026-11-15) instead of IntMul_Kappa_R8_Data_BitOppbankQHNet (definition_id 52d9e9e0-fe1c-4e6e-80f6-967f6d9be59d, created 2026-10-21). Parent source: Jain round8-oppbank bit_hist.onerun_hist; fixes OneRun b652717e pad bug. Local source: Definitions/Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2Rec.lean (0-sorry).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.dupNamespace false

/-!
# Opp-bank one-run edge families (corrected), on QHNetRec

Jain `bit_hist.onerun_hist`: each residual of rank `r` is **one** child of width `r`
(no `(r-1)` singleton pad). Matches `edge_of_pivs` with `rs = [(0,0,r)]` at `q.rank = r`.

Prior `OneRun.oneRun` required `rs'.length + 1 = r` ones-padding — unsatisfiable for
`rank = r` when `r > 1`, and would over-count width-1 bins vs `oppbankHist`/`bitR8`.

This is the QHNetRec fork of `BitOppbankOneRun2`: the carrier, predicates, and
`ch0O` / `net0O` construction are unchanged, but the network import is the
total-decoder definition `BitOppbankQHNetRec` rather than `BitOppbankQHNet`.
Do not import both OneRun2 and OneRun2Rec (same `OneRunNet2` namespace), and
do not import both QHNet and QHNetRec (same `NB` namespace), in one file.
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open scoped Kronecker

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

open Pnd
def codeBound : ℕ := 64251

/-- One contiguous Bruhat run of width `r` (opp-bank child of rank `r`). -/
def oneRun (r : ℕ) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  0 < r ∧ r < 529 ∧ rs = [(0, 0, r)]

def PE (q : Matrix (Fin 529) (Fin 529) ℚ) (R : List (ℕ × ℕ × ℕ) → Prop)
    (e : Edge 529) : Prop :=
  EdgeQ e q ∧ R e.runs

def dfltE : Edge 529 := ⟨1, [], 1⟩

open Classical in
noncomputable def pickE (P : Edge 529 → Prop) : Edge 529 :=
  if h : ∃ e, P e then Classical.choose h else dfltE

/-- Opp-bank `ch0` with corrected one-run predicates. -/
noncomputable def ch0O : Pnd.Ch where
  S := S0
  Si := Si0
  e1 b o c :=
    if b < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0 Si0 (Dm o c) (Pl b)) (oneRun (rkC o c)))
    else dfltE
  e2 a o c :=
    if a < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0 Si0 (Pl a) (Dm o c)) (oneRun (rkC o c)))
    else dfltE
  ex b :=
    if b < v then pickE (PE (K S0 Si0 1 (1 - Pl b)) (oneRun 22)) else dfltE
  en a t :=
    if a < v ∧ t < v then
      pickE (PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484))
    else dfltE
  ei a :=
    if a < v then pickE (PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22)) else dfltE
  ec a s :=
    if a < v ∧ s < v then pickE (PE (K S0 Si0 (Pl a) (Pl s)) (oneRun 1)) else dfltE

noncomputable def toNB (ch : Pnd.Ch) : NB.Ch where
  S := ch.S
  Si := ch.Si
  e1 := ch.e1
  e2 := ch.e2
  ex := ch.ex
  en := ch.en
  ei := ch.ei
  ec := ch.ec

noncomputable def net0O : QHNet (ZMod 2) 104719230 3217907 529 :=
  NB.net (toNB ch0O)

theorem net0O_T : Tmp = 3217907 := rfl
theorem net0O_W : W = 104719230 := rfl
theorem codeBound_eq : codeBound = 64251 := rfl

theorem runOK_origin {r : ℕ} (hr : 0 < r) (hrm : r < 529) :
    RunOK 529 (0, 0, r) := by
  refine ⟨hr, hrm, ?_, ?_⟩
  · simpa using (by omega : 0 + r ≤ 529)
  · simpa using (by omega : 0 + r ≤ 529)

theorem oneRun_runOK {r : ℕ} {rs : List (ℕ × ℕ × ℕ)} (h : oneRun r rs) :
    ∀ ρ ∈ rs, RunOK 529 ρ := by
  obtain ⟨hr, hrm, hrs⟩ := h
  intro ρ hρ
  simp [hrs] at hρ
  subst hρ
  exact runOK_origin hr hrm

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2


