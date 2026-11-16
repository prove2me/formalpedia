-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
-- name    : IntMul_Kappa_R8_Data_BitOppbankLab1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:13:27.3542+00:00
-- url     : https://prove2.me/theorems/014f04cf-7b5c-4157-9e7f-7830355fe016
-- title:
--   Densified stage frames $\Phi_1$/$\mathrm{lab}_1$ and $\mathrm{MovesV}$ at $\mathrm{codeBound}=64251$
-- statement:
--   # Densified stage frames and labels at $\mathrm{codeBound}=64251$
--
--   On the published R8 opp-bank projectors, a stage-one frame at slot $b$ and code $c$ is the rational partial swap of the conjugated Kronecker product of the code projector with the slot hyperplane projector. Writing $K(S,S^{-1};A,B)=S(A\otimes B)S^{-1}$ for the flag-basis conjugation already present in the pack $\mathrm{Pnd}$, one sets
--   $$
--   \Phi_1(S,S^{-1};b,c)=\mathrm{pswQ}\bigl(K(S,S^{-1};\mathrm{Pc}(c),\mathrm{Pl}(b))\bigr),
--   $$
--   $$
--   \Phi_2(S,S^{-1};a,c)=\mathrm{pswQ}\bigl(I-K(S,S^{-1};\mathrm{Pl}(a),\mathrm{Pc}(c))\bigr).
--   $$
--   The corresponding labels at field size $N$ are the entrywise reductions
--   $$
--   \mathrm{lab}_1(S,S^{-1};N,b,c)=\mathrm{red}_N\bigl(\Phi_1(S,S^{-1};b,c)\bigr),
--   \qquad
--   \mathrm{lab}_2(S,S^{-1};N,a,c)=\mathrm{red}_N\bigl(\Phi_2(S,S^{-1};a,c)\bigr).
--   $$
--   The same pack records the two validity predicates used by a stage-one certificate, now at the densified bound rather than the stale generator bound $38286$: a local code map $f$ is valid when $f(w)<64251$ for every local wire $w<N_L=31359$, and a chunk list has valid moves when every recorded move is nested ($\mathrm{nestOK}$) between codes strictly below $64251$.
--
--   These are the R8 retargets of the R6 Defs51/Defs52 frame package ($\Phi_1$, $\mathrm{lab}_1$, $\mathrm{ValidOn}$, $\mathrm{MovesV}$) onto $\mathrm{Pnd}$ ($K$, $\mathrm{Pc}$, $\mathrm{Pl}$, $\mathrm{nestOK}$) and $\mathrm{Defs4}$ ($\mathrm{pswQ}$, $\mathrm{red}_N$). They are the starting point for $\mathrm{lab}_{1,\mathrm{low}}$, $\mathrm{good}K$, $\mathrm{good}D_m$, and $\mathrm{move}_1$, and later for an R6-style $\mathrm{blk1\_{lab}}$ on the QHNetRec carrier.
--
--   **Formalization Note.** The module `IntMul.Kappa.R8.Bit.Oppbank.Lab` imports only `Pnd`, `WireLayout`, and `Defs4`. It does not import `QHNet` or `QHNetRec`, and it does not use the stale `Gen.ValidOn` bound $38286$. `GoodM` is the same coprime-denominator predicate used by the densified `EOKO` pack. Codes $c_{\mathrm{LOW}}=0$, $c_{\mathrm{HIGH}}=1$ agree with `QHNetRec.NB`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: R8 retarget of R6 Defs51/Defs52 Phi1, lab1, ValidOn, MovesV onto published Pnd (K, Pc, Pl, nestOK; codeBound 64251) and Defs4 (pswQ, redM). Not the stale Gen.ValidOn bound 38286.

-- R8 opp-bank stage frames Φ₁ / Φ₂ and reduced labels lab1 / lab2,
-- together with ValidOn / MovesV at densified codeBound = 64251.
-- Imports Pnd (K, Pc, Pl, nestOK) and Defs4 (pswQ, redM). No QHNet / QHNetRec / GenF.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-!
# Densified stage frames and labels (`Φ₁`, `lab1`) at `codeBound = 64251`

Port of the R6 Defs51/Defs52 frame package onto the published R8 `Pnd`
projectors (`Pc`, `Pl`, `K`) and `Defs4` reduction (`pswQ`, `redM`).

* `Φ₁ S Si b c = pswQ (K S Si (Pc c) (Pl b))` — stage-one frame at slot `b`
  and code `c`;
* `Φ₂ S Si a c = pswQ (1 - K S Si (Pl a) (Pc c))` — stage-two frame;
* `lab1` / `lab2` are the reductions of these frames modulo `N`.

`ValidOn` and `MovesV` are the code-validity and nested-move predicates at
the densified bound `SupG.codeBound = 64251` (not the stale R8 `Gen.ValidOn`
bound `38286`, and not R6 Defs51). `nestOK` is `Pnd.nestOK`.
-/

open Matrix
open scoped Kronecker
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.Lab

/-- Standard codes (same values as `QHNetRec.NB`). -/
def cLOW : ℕ := 0
def cHIGH : ℕ := 1
def cPT (T : ℕ) : ℕ := Nat.add 2 T
def cND (n : ℕ) : ℕ := Nat.add 1773 n

/-- Stage-one frame: partial swap of `K (Pc c) (Pl b)`. -/
noncomputable def Φ₁ (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (b c : ℕ) : QMat2 529 :=
  pswQ (K S Si (Pc c) (Pl b))

/-- Stage-two frame: partial swap of `1 - K (Pl a) (Pc c)`. -/
noncomputable def Φ₂ (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (a c : ℕ) : QMat2 529 :=
  pswQ (1 - K S Si (Pl a) (Pc c))

/-- Reduced stage-one label at field size `N`. -/
noncomputable def lab1 (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (N b c : ℕ) : FMat 529 N :=
  redM N (Φ₁ S Si b c)

/-- Reduced stage-two label at field size `N`. -/
noncomputable def lab2 (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (N a c : ℕ) : FMat 529 N :=
  redM N (Φ₂ S Si a c)

/-- All denominators coprime to `N` (same predicate as EOKO / R6 Defs51 `GoodM`). -/
def GoodM (N : ℕ) {l p : Type*} [Fintype l] [Fintype p]
    (A : Matrix l p ℚ) : Prop :=
  ∀ i j, Nat.Coprime (A i j).den N

/-- Instruction / chunk shapes (Defs51 / QHNetRec). -/
abbrev LInstr := ℕ × List ℕ × List (ℕ × ℕ)
abbrev LChunk := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- All local-wire codes are strictly below the densified bound `64251`. -/
def ValidOn (f : ℕ → ℕ) : Prop := ∀ w < NL, f w < codeBound

/-- Every move of a chunk list is nested (`Pnd.nestOK`) between codes `< 64251`. -/
def MovesV (cs : List LChunk) : Prop :=
  ∀ ch ∈ cs, ∀ mv ∈ ch.2.1, nestOK mv.2 ch.1 = true ∧ mv.2 < codeBound ∧ ch.1 < codeBound

theorem cLOW_eq : cLOW = 0 := rfl
theorem cHIGH_eq : cHIGH = 1 := rfl
theorem codeBound_eq : codeBound = 64251 := rfl
theorem NL_eq : NL = 31359 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Lab


