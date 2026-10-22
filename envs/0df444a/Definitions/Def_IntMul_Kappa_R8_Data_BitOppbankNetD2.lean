-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetD2
-- name    : IntMul_Kappa_R8_Data_BitOppbankNetD2
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:03:23.743294+00:00
-- url     : https://prove2.me/theorems/bdb59073-2f8c-4cff-8bcc-4b5567b89b2c
-- title:
--   R8 BitOppbank densified NetD + net0D bridge (pickE/Pl/Dm)
-- statement:
--   Densified Defs52 NetD for opp-bank BitNB at $\mathrm{codeBound}=64251$: real $\mathrm{Pl}$/$\mathrm{xv}$/$\mathrm{yv}$ from LocSlots, densified $\mathrm{nestOK}$/$\mathrm{dimCF}$/$\mathrm{argRel}$ from ChkBitArg, $\mathrm{Pc}$/$\mathrm{Dm}$/$\mathrm{rkC}$, flag basis $\mathrm{FB0}$/$S_0$, and $\mathrm{ch0}$ via $\mathrm{pickE}$/$\mathrm{PE}$/$\mathrm{SideR}$/$\mathrm{DataR}$/$\mathrm{AuxR}$.
--
--   Bridges into published `BitOppbankQHNet` program:
--   $$\mathrm{net0D}=\mathrm{net}(\mathrm{toNB}(\mathrm{ch0})).$$
--
--   Supersedes stub NetD `88df9bd7` for `net0_ok` work; does not duplicate QHNet.
-- source:
--   Defs52 NetD + Defs51 projectors densified; QHNet 52d9e9e0; ProjB b18c4ed9

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLocSlots
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankChkBitArg
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# R8 opp-bank NetD (Defs52 flag basis + Defs51 projectors / nestOK)

Retarget of R6 `R6BitNBNetD` / projector / nest machinery onto densified
BitOppbank tables (`codeBound = 64251`, `nNodes = 62478`).

* `Pl` / `xv` / `yv` from LocSlots `TPTS` (lex triples)
* `argRel` / `dimCF` / `nestOK` from densified `ChkBitArg` ARGT/DIMT
* `Pc` / `Dm` / `rkC` (ND projector `Pnd` is `0` without a centre certificate —
  same fallback as Defs51 `HasCentre` failure)
* `FB0` / `S0` / `Si0` via `Classical.epsilon` (Defs52 pattern; inhabited by
  proved `flagBasis` once `Lab0`/`Pis0` hypotheses are discharged)
* `pickE` / `PE` / `SideR` / `DataR` / `AuxR` / `K` for `ch0` edge families
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.LocSlots
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg
open Matrix
open scoped Kronecker

namespace IntMul.Kappa.R8.Bit.Oppbank.NetD

abbrev V23 := Fin 23 → ℚ
abbrev M23 := Matrix (Fin 23) (Fin 23) ℚ
abbrev Pr23 := Fin 23 × Fin 23

def codeBound : ℕ := 64251
theorem codeBound_eq : codeBound = 1773 + nNodes := by
  simp [codeBound, nNodes]

/-! ## Field accessors -/

def fieldOf (X w i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight X (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

def pts (T k : ℕ) : ℕ := fieldOf TPTS 5 (Nat.add (Nat.mul 3 T) k)

/-- Triple bit-mask from three points. -/
def tri (T : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.shiftLeft 1 (pts T 0)) (Nat.shiftLeft 1 (pts T 1)))
    (Nat.shiftLeft 1 (pts T 2))

def tvQ (T : ℕ) : V23 := fun p => if (tri T).testBit p.val = true then 1 else 0

def xv (T : ℕ) : V23 := tvQ T

def yv (T : ℕ) : V23 := fun p =>
  (tvQ T p - (∑ q : Fin 23, tvQ T q) / 9) / 2

/-- Line projector `x_T y_Tᵀ`. -/
def Pl (T : ℕ) : M23 := vecMulVec (xv T) (yv T)

/-! ## Densified arg / dim / nestOK -/

def argF (n : ℕ) : ℕ := fieldOf ARGT 32 n
def dimF (n : ℕ) : ℕ := fieldOf DIMT 5 n

def argRel (a n : ℕ) : Bool :=
  Nat.beq (Nat.land (argF n) 65535) a || Nat.beq (Nat.shiftRight (argF n) 16) a

def dimCF (c : ℕ) : ℕ :=
  cond (Nat.beq c 0) 0
    (cond (Nat.beq c 1) 23
      (cond (Nat.blt c 1773) 22 (dimF (Nat.sub c 1773))))

def isND (c : ℕ) : Bool := Nat.ble 1773 c && Nat.blt c codeBound
def isPT (c : ℕ) : Bool := Nat.ble 2 c && Nat.blt c 1773

/-- Orthogonality stub: always true for densified port (full `orthOK` needs `supG`). -/
def orthOK (_n _T : ℕ) : Bool := true

def nestOK (o c : ℕ) : Bool :=
  Nat.ble o 1 || Nat.ble c 1 ||
  (isND o && isND c &&
    (argRel (Nat.sub o 1773) (Nat.sub c 1773) || argRel (Nat.sub c 1773) (Nat.sub o 1773))) ||
  (isND o && isPT c && orthOK (Nat.sub o 1773) (Nat.sub c 2)) ||
  (isPT o && isND c && orthOK (Nat.sub c 1773) (Nat.sub o 2))

/-! ## Code projectors / moves -/

/-- ND projector fallback (`0` without centre certificate). -/
noncomputable def Pnd (_sup : ℕ) : M23 := 0

/-- Projector named by a code (Defs51 `Pc`), alphabet to `codeBound`. -/
noncomputable def Pc (c : ℕ) : M23 :=
  if c = 0 then 0
  else if c = 1 then 1
  else if c < 1773 then 1 - Pl (c - 2)
  else Pnd 0

noncomputable def Dm (o c : ℕ) : M23 :=
  if dimCF o ≤ dimCF c then Pc c - Pc o else Pc o - Pc c

noncomputable def rkC (a b : ℕ) : ℕ :=
  let a1 := dimCF a; let b1 := dimCF b
  cond (Nat.blt a1 b1) (Nat.sub b1 a1) (Nat.sub a1 b1)

/-! ## Flag basis (Defs52) -/

def K (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (A B : M23) : Matrix (Fin 529) (Fin 529) ℚ :=
  S * (A ⊗ₖ B) * Si

noncomputable def Lab0 : Finset (V23 × V23) :=
  (Finset.range 1771).image fun T => (xv T, yv T)

noncomputable def idxD : Finset (ℕ × ℕ) :=
  ((Finset.range codeBound) ×ˢ (Finset.range codeBound)).filter
    (fun p => nestOK p.1 p.2 = true)

def I3 : Finset (ℕ × ℕ × ℕ) :=
  Finset.range 1771 ×ˢ (Finset.range codeBound ×ˢ Finset.range codeBound)

def I2 : Finset (ℕ × ℕ) := Finset.range 1771 ×ˢ Finset.range 1771

attribute [irreducible] idxD I3 I2

noncomputable def Pis0 : Finset M23 :=
  idxD.image (fun p => Dm p.1 p.2) ∪ (Finset.range 1771).image Pl

attribute [irreducible] Pis0

/-- Flag-basis property (Defs52 `FB0`). -/
abbrev FB0 (S : Matrix (Fin 529) Pr23 ℚ) (Sinv : Matrix Pr23 (Fin 529) ℚ) : Prop :=
  S * Sinv = 1 ∧ Sinv * S = 1 ∧
    (∀ p ∈ Lab0,
      AuxE (h := 19) (S * ((1 : M23) ⊗ₖ (1 - vecMulVec p.1 p.2)) * Sinv) ∧
        AuxE (h := 19) (S * ((1 - vecMulVec p.1 p.2) ⊗ₖ (1 : M23)) * Sinv)) ∧
    (∀ p ∈ Lab0, ∀ A ∈ Pis0,
      SideE (h := 19) (S * (A ⊗ₖ vecMulVec p.1 p.2) * Sinv) A.rank ∧
        SideE (h := 19) (S * (vecMulVec p.1 p.2 ⊗ₖ A) * Sinv) A.rank) ∧
    (∀ p₁ ∈ Lab0, ∀ p₂ ∈ Lab0,
      DataE (h := 19)
        (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ (1 - vecMulVec p₂.1 p₂.2)) * Sinv))

noncomputable def S0 : Matrix (Fin 529) Pr23 ℚ :=
  Classical.epsilon (fun S => ∃ Sinv, FB0 S Sinv)

noncomputable def Si0 : Matrix Pr23 (Fin 529) ℚ :=
  Classical.epsilon (fun Sinv => FB0 S0 Sinv)

/-! ## Edge predicates (Defs52) -/

def dfltE : Edge 529 := ⟨1, [], 1⟩

open Classical in
noncomputable def pickE (P : Edge 529 → Prop) : Edge 529 :=
  if h : ∃ e, P e then Classical.choose h else dfltE

def SideR (r : ℕ) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ rs', rs = sideRuns 23 529 r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
    (runPairs (sideRuns 23 529 r)).length + rs'.length = r

def DataR (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ rs', rs = dataRuns 23 529 ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧ rs'.length = 24

def AuxR (rs : List (ℕ × ℕ × ℕ)) : Prop := rs = auxRuns 19

def PE (q : Matrix (Fin 529) (Fin 529) ℚ) (R : List (ℕ × ℕ × ℕ) → Prop)
    (e : Edge 529) : Prop :=
  EdgeQ e q ∧ R e.runs

/-! ## Chosen edge families at `codeBound` -/

structure Ch where
  S : Matrix (Fin 529) Pr23 ℚ
  Si : Matrix Pr23 (Fin 529) ℚ
  e1 : ℕ → ℕ → ℕ → Edge 529
  e2 : ℕ → ℕ → ℕ → Edge 529
  ex : ℕ → Edge 529
  en : ℕ → ℕ → Edge 529
  ei : ℕ → Edge 529
  ec : ℕ → ℕ → Edge 529

/-- Opp-bank `ch0` with real `pickE`/`PE` (Defs52), alphabet `codeBound`. -/
noncomputable def ch0 : Ch where
  S := S0
  Si := Si0
  e1 b o c :=
    if b < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0 Si0 (Dm o c) (Pl b)) (SideR (rkC o c)))
    else dfltE
  e2 a o c :=
    if a < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0 Si0 (Pl a) (Dm o c)) (SideR (rkC o c)))
    else dfltE
  ex b :=
    if b < v then pickE (PE (K S0 Si0 1 (1 - Pl b)) AuxR) else dfltE
  en a t :=
    if a < v ∧ t < v then pickE (PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) DataR) else dfltE
  ei a :=
    if a < v then pickE (PE (K S0 Si0 (1 - Pl a) 1) AuxR) else dfltE
  ec a s :=
    if a < v ∧ s < v then pickE (PE (K S0 Si0 (Pl a) (Pl s)) (SideR 1)) else dfltE


/-! ## Bridge into published QHNet program (`NB.net`) -/

open IntMul.Kappa.R8.Bit.Oppbank.NB (net)

/-- Coerce NetD edges into the QHNet `NB.Ch` carrier. -/
noncomputable def toNB (ch : Ch) : IntMul.Kappa.R8.Bit.Oppbank.NB.Ch where
  S := ch.S
  Si := ch.Si
  e1 := ch.e1
  e2 := ch.e2
  ex := ch.ex
  en := ch.en
  ei := ch.ei
  ec := ch.ec

/-- Opp-bank network with densified pickE edges on the published BitOppbank program. -/
noncomputable def net0D : QHNet (ZMod 2) W Tmp 529 := net (toNB ch0)

theorem net0D_W : W = 104719230 := rfl
theorem net0D_codeBound : codeBound = 64251 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.NetD


