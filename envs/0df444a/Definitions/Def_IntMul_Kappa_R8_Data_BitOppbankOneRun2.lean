-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRun2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:33:32.076472+00:00
-- url     : https://prove2.me/theorems/e0d447f6-cd60-4e42-86c4-534cc0c33db5
-- title:
--   Corrected one-run opp-bank channel (single width-r child)
-- statement:
--   # OneRun2 — corrected opp-bank one-run predicates
--
--   Jain `bit_hist.onerun_hist` compiles each residual of rank $r$ as **one** contiguous child of width $r$. The prior `OneRun.oneRun` required $(r-1)$ singleton pads, which is unsatisfiable at $\mathrm{rank}=r$ for $r>1$ and would over-count width-$1$ bins versus `oppbankHist`/`Jain.bitR8`.
--
--   This module defines `oneRun r rs := 0 < r ∧ r < 529 ∧ rs = [(0,0,r)]`, densified `ch0O`/`net0O` on `Pnd` projectors, and `codeBound = 64251`.
--
--   **Formalization Note.** Carrier network `OneRunNet2.net0O`.
-- source:
--   Jain round8-oppbank bit_hist.onerun_hist; fixes OneRun b652717e pad bug

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
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
# Opp-bank one-run edge families (corrected)

Jain `bit_hist.onerun_hist`: each residual of rank `r` is **one** child of width `r`
(no `(r-1)` singleton pad). Matches `edge_of_pivs` with `rs = [(0,0,r)]` at `q.rank = r`.

Prior `OneRun.oneRun` required `rs'.length + 1 = r` ones-padding — unsatisfiable for
`rank = r` when `r > 1`, and would over-count width-1 bins vs `oppbankHist`/`bitR8`.
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


