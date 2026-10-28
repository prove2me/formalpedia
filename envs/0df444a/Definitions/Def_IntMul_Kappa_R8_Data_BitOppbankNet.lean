-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet
-- name    : IntMul_Kappa_R8_Data_BitOppbankNet
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:46:02.051071+00:00
-- url     : https://prove2.me/theorems/4572c8be-2481-49ad-8137-faf004ae810d
-- title:
--   R8 BitNB network core W=104719230 T=3217907 m=529
-- statement:
--   # Opp-bank network core (Defs52 retarget)
--
--   Geometry $W=104719230$, $T=3217907$, $m=529$, maps `g1`/`g2`/`ρ`, densified
--   `nNodes`/`codeBound`, and `targetHist` matching `Jain.bitR8` / `BitOppbankHist`.
--   Full `QHNet` `prog`/`ch0` still needs platform `Instr` plus `cs1`/`cs2` from genF.
-- source:
--   Retarget of IntMul_Kappa_R6_Defs52 geometry/wiring; hist from BitOppbankHist

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R8 opp-bank BitNB network core (Defs52 retarget)

`W = 104719230`, `T = 3217907`, `m = 529`, `NR = 27794`.
Densified producer alphabet: `nNodes = 62478`, `codeBound = 64251`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.Net

def h : ℕ := 23
def v : ℕ := 1771
def NR : ℕ := 27794
def N : ℕ := 3136441
def W : ℕ := 104719230
def Tmp : ℕ := 3217907
def m : ℕ := 529
def wEnt : ℕ := 3542
def wAuxEnd : ℕ := 31336
def NL : ℕ := 31359
def nNodes : ℕ := 62478
def codeBound : ℕ := 64251

theorem W_eq : W = 2 * N + 2 * v * NR := by decide
theorem Tmp_eq : Tmp = 46 * v + N := by decide
theorem m_eq : m = h * h := by decide
theorem nNodes_eq : nNodes = 62478 := rfl
theorem codeBound_eq : codeBound = 64251 := rfl
theorem twoN_le_W : 2 * N ≤ W := by decide
theorem N_le_W : N ≤ W := by decide

def g1 (b w : ℕ) : ℕ :=
  if w < v then w * v + b
  else if w < wEnt then N + (w - v) * v + b
  else if w < wAuxEnd then 2 * N + b * NR + (w - wEnt)
  else W + h * b + (w - wAuxEnd)

def g2 (a w : ℕ) : ℕ :=
  if w < v then N + a * v + w
  else if w < wEnt then a * v + (w - v)
  else if w < wAuxEnd then 2 * N + v * NR + a * NR + (w - wEnt)
  else if w < NL then W + h * v + h * a + (w - wAuxEnd)
  else W + 2 * h * v + a * v + (w - NL)

def ρn (g : ℕ) : ℕ :=
  if g < N then g + N else if g < 2 * N then g - N else g

theorem ρn_lt_W (g : ℕ) (hg : g < W) : ρn g < W := by
  simp only [ρn]
  split_ifs with h1 h2
  · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right h1 N) twoN_le_W
  · have hge : N ≤ g := le_of_not_gt h1
    have : g - N < N := Nat.sub_lt_left_of_lt_add hge (by
      -- h2 : g < 2*N
      simpa [Nat.two_mul, Nat.add_comm] using h2)
    exact Nat.lt_of_lt_of_le this N_le_W
  · exact hg

def ρ (w : Fin W) : Fin W := ⟨ρn w.val, ρn_lt_W w.val w.isLt⟩

def targetHist : List (ℕ × ℕ) :=
  [(1, 221936407), (2, 259926128), (3, 38728228), (4, 49343602), (5, 24609816),
   (6, 8068676), (7, 3818276), (8, 4785242), (9, 2992990), (10, 1211364),
   (11, 1445136), (12, 1331792), (13, 1080310), (14, 669438), (15, 2755676),
   (16, 3860780), (17, 1933932), (18, 364826), (19, 13388760), (20, 587972),
   (21, 1771000), (22, 116886), (484, 6272882), (506, 59760624), (507, 453376),
   (508, 173558), (509, 421498), (510, 233772), (511, 205436), (512, 226688),
   (513, 340032), (514, 602140), (515, 173558), (516, 357742), (517, 283360),
   (518, 690690), (519, 389620), (520, 102718), (521, 184184), (522, 584430),
   (523, 350658), (524, 3021326), (525, 13448974), (526, 4558554), (527, 5649490),
   (528, 6233920)]

def targetHist_childCount : ℕ := (targetHist.map (·.2)).sum
theorem targetHist_childCount_eq : targetHist_childCount = 749446467 := by decide

end IntMul.Kappa.R8.Bit.Oppbank.Net


