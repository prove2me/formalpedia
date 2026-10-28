-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetD
-- name    : IntMul_Kappa_R8_Data_BitOppbankNetD
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:59:31.982456+00:00
-- url     : https://prove2.me/theorems/88df9bd7-9087-4238-9990-72535d05a3cc
-- title:
--   R8 BitOppbank Defs52 NetD: pickE / PE / SideR / ch0D
-- statement:
--   Densified Defs52 edge layer for the opp-bank bit network at $\mathrm{codeBound}=64251$: run-class predicates $\mathrm{SideR}$, $\mathrm{DataR}$, $\mathrm{AuxR}$, edge selector $\mathrm{pickE}$ via $\mathrm{PE}$/$\mathrm{EdgeQ}$, flag-basis carrier $\mathrm{FB0}$/$S_0$/$S_0^{-1}$, and chosen edges $\mathrm{ch0D}$ feeding $\mathrm{net0D}=\mathrm{net}(\mathrm{ch0D})$.
--
--   $$\mathrm{net0D}:\mathrm{QHNet}(\mathbb{Z}/2\mathbb{Z},\,W,\,T,\,529).$$
--
--   Program/`cs*` stay in published `BitOppbankQHNet`. Projector stubs (`Pl`/`Dm`/`rkC`/`nestOK`) match the Defs51 API pending densified `dimCF` wiring.
-- source:
--   R6 Defs52 NetD retarget; BitOppbankQHNet 52d9e9e0; codeBound=64251

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# R8 opp-bank BitNB edges (Defs52 `NetD` retarget)

Ports `SideR` / `DataR` / `AuxR` / `PE` / `FB0` / densified `ch0D` with `pickE`
from `IntMul_Kappa_R6_Defs52` onto `codeBound = 64251`.

Projector carriers `Pl` / `Dm` / `rkC` / `nestOK` / `xv`/`yv` are **typed stubs**
matching the Defs51/52 API (zero / trivial ranks) so the edge-choice layer and
`net0D := net ch0D` land without pulling the full R6 Defs51 Loc/ChkBit stack.
Replace stubs with densified Defs51 ports (or `import Defs51` on platform) when
Track C densified `dimCF`/`argRel` are wired; `pickE`/`PE`/`EdgeQ` shape stays.

Does **not** redefine `prog`/`cs*` — those stay in `BitOppbankQHNet` (`52d9e9e0`).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.NB

open Matrix Finset
open scoped Kronecker
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB

/-! ## Defs51 API stubs (densified projectors TBD) -/

abbrev V23 := Fin 23 → ℚ
abbrev M23 := Matrix (Fin 23) (Fin 23) ℚ

noncomputable def xv (_T : ℕ) : V23 := 0
noncomputable def yv (_T : ℕ) : V23 := 0
noncomputable def Pl (_T : ℕ) : M23 := 0
noncomputable def Dm (_o _c : ℕ) : M23 := 0
def rkC (_a _b : ℕ) : ℕ := 1
/-- Placeholder nest predicate; densified `nestOK` replaces this. -/
def nestOK (_o _c : ℕ) : Bool := true

def K (S : Matrix (Fin 529) (Pr 23) ℚ) (Si : Matrix (Pr 23) (Fin 529) ℚ)
    (A B : M23) : Matrix (Fin 529) (Fin 529) ℚ :=
  S * (A ⊗ₖ B) * Si

/-! ## Choosing edges (Defs52 NetD) -/

def SideR (r : ℕ) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ rs', rs = sideRuns 23 529 r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
    (runPairs (sideRuns 23 529 r)).length + rs'.length = r

def DataR (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ rs', rs = dataRuns 23 529 ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧ rs'.length = 24

def AuxR (rs : List (ℕ × ℕ × ℕ)) : Prop := rs = auxRuns 19

def PE (q : Matrix (Fin 529) (Fin 529) ℚ) (R : List (ℕ × ℕ × ℕ) → Prop)
    (e : Edge 529) : Prop :=
  EdgeQ e q ∧ R e.runs

/-! ## Flag basis at densified `codeBound` -/

noncomputable def Lab0 : Finset (V23 × V23) :=
  (Finset.range v).image fun T => (xv T, yv T)

noncomputable def idxD : Finset (ℕ × ℕ) :=
  ((Finset.range codeBound) ×ˢ (Finset.range codeBound)).filter
    (fun p => nestOK p.1 p.2 = true)

def I3 : Finset (ℕ × ℕ × ℕ) :=
  Finset.range v ×ˢ (Finset.range codeBound ×ˢ Finset.range codeBound)

def I2 : Finset (ℕ × ℕ) := Finset.range v ×ˢ Finset.range v

attribute [irreducible] idxD I3 I2

noncomputable def Pis0 : Finset M23 :=
  idxD.image (fun p => Dm p.1 p.2) ∪ (Finset.range v).image Pl

attribute [irreducible] Pis0

abbrev FB0 (S : Matrix (Fin ((19 + 4) * (19 + 4))) (Pr (19 + 4)) ℚ)
    (Sinv : Matrix (Pr (19 + 4)) (Fin ((19 + 4) * (19 + 4))) ℚ) : Prop :=
  S * Sinv = 1 ∧ Sinv * S = 1 ∧
      (∀ p ∈ Lab0, AuxE (h := 19) (S * ((1 : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) ⊗ₖ
          (1 - vecMulVec p.1 p.2)) * Sinv) ∧
        AuxE (h := 19) (S * ((1 - vecMulVec p.1 p.2) ⊗ₖ
          (1 : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)) * Sinv)) ∧
      (∀ p ∈ Lab0, ∀ A ∈ Pis0,
        SideE (h := 19) (S * (A ⊗ₖ vecMulVec p.1 p.2) * Sinv) A.rank ∧
        SideE (h := 19) (S * (vecMulVec p.1 p.2 ⊗ₖ A) * Sinv) A.rank) ∧
      (∀ p₁ ∈ Lab0, ∀ p₂ ∈ Lab0,
        DataE (h := 19) (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ
          (1 - vecMulVec p₂.1 p₂.2)) * Sinv))

noncomputable def S0D : Matrix (Fin 529) (Pr 23) ℚ :=
  Classical.epsilon (fun S => ∃ Sinv, FB0 S Sinv)

noncomputable def Si0D : Matrix (Pr 23) (Fin 529) ℚ :=
  Classical.epsilon (fun Sinv => FB0 S0D Sinv)

/-! ## Densified `ch0D` with `pickE` -/

noncomputable def ch0D : Ch where
  S := S0D
  Si := Si0D
  e1 b o c :=
    if b < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0D Si0D (Dm o c) (Pl b)) (SideR (rkC o c)))
    else dfltE
  e2 a o c :=
    if a < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0D Si0D (Pl a) (Dm o c)) (SideR (rkC o c)))
    else dfltE
  ex b :=
    if b < v then pickE (PE (K S0D Si0D 1 (1 - Pl b)) AuxR) else dfltE
  en a t :=
    if a < v ∧ t < v then
      pickE (PE (K S0D Si0D (1 - Pl a) (1 - Pl t)) DataR)
    else dfltE
  ei a :=
    if a < v then pickE (PE (K S0D Si0D (1 - Pl a) 1) AuxR) else dfltE
  ec a s :=
    if a < v ∧ s < v then
      pickE (PE (K S0D Si0D (Pl a) (Pl s)) (SideR 1))
    else dfltE

noncomputable instance instDecEqEdge529 : DecidableEq (Edge 529) := Classical.decEq _

noncomputable def E0 : Finset (Edge 529) :=
  (I3.image fun p => ch0D.e1 p.1 p.2.1 p.2.2) ∪
    (I3.image fun p => ch0D.e2 p.1 p.2.1 p.2.2) ∪
    ((Finset.range v).image ch0D.ex) ∪
    (I2.image fun p => ch0D.en p.1 p.2) ∪
    ((Finset.range v).image ch0D.ei) ∪
    (I2.image fun p => ch0D.ec p.1 p.2) ∪ {dfltE}

attribute [irreducible] E0

def Fam (ch : Ch) (e : Edge 529) : Prop :=
  (∃ b o c, e = ch.e1 b o c) ∨ (∃ a o c, e = ch.e2 a o c) ∨ (∃ b, e = ch.ex b) ∨
    (∃ a t, e = ch.en a t) ∨ (∃ a, e = ch.ei a) ∨ (∃ a s, e = ch.ec a s)

noncomputable def net0D : QHNet (ZMod 2) W Tmp 529 := net ch0D

theorem net0D_W : W = 104719230 := rfl
theorem net0D_T : Tmp = 3217907 := rfl
theorem net0D_codeBound : codeBound = 64251 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.NB


