-- Prove2me | Definitions.Def_Zeta5_SourceGrowthTables
-- name    : Zeta5_SourceGrowthTables
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T15:28:30.954977+00:00
-- url     : https://prove2.me/theorems/a4c662df-1b97-4a50-9a24-c59c88da0656
-- title:
--   Zeta5: growth tables — the class-sum data, the inner/outer profiles $F_{\mathrm{in}}$, $E_{\mathrm{out}}$ and the piecewise grids
-- statement:
--   The definitions of the growth part of the source project: the class-sum data `ivLo`/`ivHi`/`cvLo`/`cvHi` (the three intervals of the class decomposition), `bcoef` (coefficients in the basis $1, A, E$), `aCnt` (the class count $\mathbf 1[c \le v] + \mathbf 1[p-v \le c]$), `ivInd`, `ccount` (continuous interval counts); the class function $\psi_R(k,\beta) = \sum_{i < \mathrm{lrow}(k,\beta)} (k-2i-\beta)/2$; the continuous inner profile $$E_{\mathrm{in}}(x,k) = -2\lambda x\lfloor x\rfloor + 12\lambda x\lfloor \alpha x\rfloor + 2J(\lambda x) - \lambda x k + 2\sum_{i,j} b_{ij}(k)\,c_{ij}(\{x\},\{\alpha x\}),$$with $\lambda = 37/40$, $\alpha = 3/40$, $J(u) = \sum_{j \le 1000}(u - j/2)^+$; the continuous outer profile $$E_{\mathrm{out}}(x) = -2\lambda x\lfloor x\rfloor + 2J(\lambda x) - 2\sum_{i,j} G_{ij}(\lfloor x\rfloor)c_{ij}(\{x\},\{\alpha x\}) + \max(0, 13x/10 - 2),$$whose weighted prime sums bound the local exponents of the inner range $K/20 < p \le K/3$ and the outer range $K/3 < p \le 2h$; and the piecewise grids: the 125-piece inner table `tIn`/`kIn`/`gIn` on $[3,20]$ (table literals `tInL`, `kInL`, `aInL`, `bInL`), the 13-piece outer table `tOut`/`gOut` on $[20/37,3]$ (table literals `tOutL`, `aOutL`, `bOutL`), the piece locator `pieceIdx` (the largest index $i \le m$ with $t_i \le x$) and the assembled function $F_{\mathrm{in}}(x) = g_{\mathrm{in}}(\mathrm{pieceIdx}\, t_{\mathrm{in}}\, 125\, x, x)$. **Formalization Note** Nothing is proved in this module; every definition is reproduced verbatim from the source `Apery/Growth/{ClassSum,TablePrime,OuterPrime,TailPrime,InnerSum,OuterTable,PieceIdx}.lean` in the `Apery` namespace.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/ClassSum.lean, Apery/Growth/TablePrime.lean, Apery/Growth/OuterPrime.lean, Apery/Growth/TailPrime.lean, Apery/Growth/InnerSum.lean, Apery/Growth/OuterTable.lean, Apery/Growth/PieceIdx.lean

import Mathlib
import Definitions.Def_Zeta5_SourceArith

/-!
# The growth tables: `F_in`/`E_out` profiles, piecewise tables, class-sum data

The definitions of the source project `mo271/Zeta5` used to state the three prime-range
estimates of the growth of the normaliser:

* the class-sum data `ivLo`/`ivHi`/`cvLo`/`cvHi`, `bcoef`, `aCnt`, `ivInd`, `ccount` of
  `Apery/Growth/ClassSum.lean` (used to expand the per-class counts in the class basis
  `1, A, E`);
* the functions `Jc`, the continuous functions `E_in(x, k)` and `E_out(x)` of
  `Apery/Growth/TablePrime.lean` and `Apery/Growth/OuterPrime.lean` — the inner/outer
  density profiles whose weighted prime sums bound the local exponents, with coefficients
  `bIn`/`GO` expressed through the class function `psiR`;
* the piecewise grid functions `tIn`/`kIn`/`gIn` (125 pieces on `[3, 20]`, from the
  generated table `tInL`/`kInL`/`aInL`/`bInL`), the outer grid `tOut`/`gOut` (13 pieces on
  `[20/37, 3]`, table `tOutL`/`aOutL`/`bOutL`), the piece locator `pieceIdx` and the
  assembled functions `F_in = gIn ∘ pieceIdx`, `E_out`.

Nothing is proved in this module; every definition is reproduced verbatim from the source.
-/

set_option maxRecDepth 100000

open Finset

namespace Apery

/-! ## The class-sum data (`Apery/Growth/ClassSum.lean`) -/

/-- Lower ends of the three intervals of the class decomposition. -/
def ivLo (p v : ℕ) : Fin 3 → ℕ := ![1, 1, p - v]

/-- Upper ends of the three intervals of the class decomposition. -/
def ivHi (m v : ℕ) : Fin 3 → ℕ := ![m, v, m]

/-- Continuous lower ends. -/
noncomputable def cvLo (f : ℝ) : Fin 3 → ℝ := ![0, 0, 1 - f]

/-- Continuous upper ends. -/
noncomputable def cvHi (f : ℝ) : Fin 3 → ℝ := ![1 / 2, f, 1 / 2]

/-- The coefficients of a class function in the basis `1, A, E`. -/
def bcoef (h : ℕ → ℝ) : Fin 3 → ℝ := ![h 0, h 1 - h 0, h 2 - h 1]

/-- The class count `1[c ≤ v] + 1[p - v ≤ c]`. -/
def aCnt (p v c : ℕ) : ℕ := (if c ≤ v then 1 else 0) + (if p - v ≤ c then 1 else 0)

/-- The indicator of the `i`-th interval. -/
def ivInd (p m v : ℕ) (i : Fin 3) (c : ℕ) : ℝ :=
  if ivLo p v i ≤ c ∧ c ≤ ivHi m v i then 1 else 0

/-- The continuous analogue of an interval count. -/
noncomputable def ccount (f g : ℝ) (i j : Fin 3) : ℝ :=
  max 0 (min (min (cvHi f i) (cvHi g j)) (1 / 2) - max (max (cvLo f i) (cvLo g j)) 0)

/-- The class function `psiR(k, beta) = sum_{i < lrow(k,beta)} (k - 2i - beta)/2`. -/
noncomputable def psiR (k β : ℤ) : ℚ := ∑ i ∈ range (lrow k β), (((k : ℚ) - 2 * i - β) / 2)

/-! ## The tridiagonal weights (`Apery/Growth/TailPrime.lean`) -/

/-- `J(u) = sum_{j ≤ 1000} (u - j/2)^+`. -/
noncomputable def Jc (u : ℝ) : ℝ := ∑ j ∈ (Icc 1 1000 : Finset ℕ), max 0 (u - (j : ℝ) / 2)

/-! ## The continuous inner function (`Apery/Growth/TablePrime.lean`) -/

/-- The class-function coefficients of the inner range. -/
noncomputable def bIn (q q' : ℕ) (k : ℤ) (i j : Fin 3) : ℝ :=
  bcoef (fun a => bcoef (fun b => (psiR k (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) : ℝ)) j) i

/-- **The continuous inner function.** -/
noncomputable def Ein (x : ℝ) (k : ℤ) : ℝ :=
  -2 * (37 / 40 * x) * (⌊x⌋₊ : ℝ) + 12 * (37 / 40 * x) * (⌊3 / 40 * x⌋₊ : ℝ) + 2 * Jc (37 / 40 * x) -
    37 / 40 * x * k +
    2 * ∑ i, ∑ j, bIn ⌊x⌋₊ ⌊3 / 40 * x⌋₊ k i j * ccount (Int.fract x) (Int.fract (3 / 40 * x)) i j

/-! ## The continuous outer function (`Apery/Growth/OuterPrime.lean`) -/

/-- The per-class outer weight sum `G_q(a, delta)`. -/
noncomputable def GO (q a d : ℕ) : ℚ :=
  ∑ i ∈ range (2 * q + a - 2), min 0 ((i : ℚ) + 3 * d - ((2 * q + a : ℕ) + 4 : ℚ) / 2)

/-- The class-function coefficients of the outer range. -/
noncomputable def bGO (q : ℕ) (i j : Fin 3) : ℝ :=
  bcoef (fun a => bcoef (fun b => (GO q a b : ℝ)) j) i

/-- **The continuous outer function** (in the variable `x = K/p`). -/
noncomputable def Eout (x : ℝ) : ℝ :=
  -2 * (37 / 40 * x) * (⌊x⌋₊ : ℝ) + 2 * Jc (37 / 40 * x) -
    2 * ∑ i, ∑ j, bGO ⌊x⌋₊ i j * ccount (Int.fract x) (Int.fract (3 / 40 * x)) i j +
    max 0 (13 / 10 * x - 2)

/-! ## The inner table on `[3, 20]` (125 pieces, `Apery/Growth/InnerSum.lean`) -/

/-- The grid of the inner table. -/
def tInL : List ℚ := [(3), (70/23), (120/37), (10/3), (80/23), (7/2), (160/43), (140/37), (90/23), (4), (160/37), (100/23), (9/2), (200/43), (110/23), (180/37), (5), (120/23), (200/37), (11/2), (240/43), (130/23), (220/37), (6), (140/23), (240/37), (13/2), (280/43), (150/23), (20/3), (160/23), (7), (260/37), (170/23), (320/43), (15/2), (280/37), (180/23), (8), (300/37), (190/23), (360/43), (17/2), (320/37), (200/23), (9), (210/23), (340/37), (400/43), (19/2), (220/23), (360/37), (10), (440/43), (380/37), (240/23), (21/2), (400/37), (250/23), (11), (480/43), (260/23), (420/37), (23/2), (270/23), (440/37), (12), (520/43), (280/23), (460/37), (25/2), (290/23), (480/37), (13), (560/43), (300/23), (40/3), (310/23), (27/2), (500/37), (320/23), (600/43), (14), (520/37), (330/23), (29/2), (540/37), (340/23), (640/43), (15), (560/37), (350/23), (31/2), (360/23), (580/37), (680/43), (16), (370/23), (600/37), (33/2), (380/23), (50/3), (720/43), (620/37), (390/23), (17), (640/37), (400/23), (35/2), (760/43), (410/23), (660/37), (18), (420/23), (680/37), (37/2), (800/43), (430/23), (700/37), (19), (440/23), (720/37), (39/2), (840/43), (450/23), (20)]

/-- The exponents `k_i` of the inner table. -/
def kInL : List ℤ := [2, 3, 3, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 11, 11, 11, 11, 12, 13, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 17, 17, 17, 17, 18, 18, 19, 19, 19, 19, 20, 20, 22, 22, 22, 23, 23, 23, 24, 24, 24, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 28, 28, 28, 28, 29, 30, 31, 31, 31, 32, 32, 32, 32, 33, 33, 33, 34, 34, 34, 34, 35, 35, 36, 36, 36, 36, 37, 37, 37, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 42, 43, 43, 43, 43, 44, 44, 44, 45, 45, 45, 45, 46]

/-- The slopes of the inner table. -/
def aInL : List ℚ := [(18/5), (49/20), (283/40), (277/40), (231/40), (271/40), (71/20), (27/5), (17/4), (17/5), (321/40), (55/8), (63/8), (93/20), (7/2), (107/20), (9/2), (67/20), (319/40), (359/40), (23/4), (23/5), (129/20), (28/5), (89/20), (363/40), (403/40), (137/20), (57/10), (69/10), (23/4), (49/10), (27/4), (28/5), (19/8), (27/8), (8), (137/20), (6), (157/20), (67/10), (139/40), (179/40), (91/10), (159/20), (71/10), (119/20), (39/5), (183/40), (223/40), (177/40), (181/20), (69/10), (147/40), (221/40), (35/8), (43/8), (10), (177/20), (8), (191/40), (29/8), (219/40), (259/40), (213/40), (199/20), (91/10), (47/8), (189/40), (263/40), (303/40), (257/40), (221/20), (51/5), (279/40), (233/40), (145/8), (679/40), (719/40), (793/40), (747/40), (309/20), (73/5), (769/40), (723/40), (763/40), (837/40), (791/40), (331/20), (157/10), (813/40), (767/40), (807/40), (761/40), (167/8), (353/20), (84/5), (313/20), (811/40), (851/40), (161/8), (799/40), (67/4), (93/5), (349/20), (83/5), (849/40), (803/40), (843/40), (357/20), (167/10), (371/20), (177/10), (331/20), (847/40), (887/40), (379/20), (89/5), (393/20), (94/5), (353/20), (891/40), (931/40), (401/20), (189/10)]

/-- The offsets of the inner table. -/
def bInL : List ℚ := [(-6), (-5/2), (-35/2), (-17), (-13), (-33/2), (-9/2), (-23/2), (-7), (-11), (-31), (-26), (-61/2), (-31/2), (-10), (-19), (-24), (-18), (-43), (-97/2), (-61/2), (-24), (-35), (-41), (-34), (-64), (-141/2), (-99/2), (-42), (-50), (-42), (-49), (-62), (-107/2), (-59/2), (-37), (-72), (-63), (-71), (-86), (-153/2), (-99/2), (-58), (-98), (-88), (-97), (-173/2), (-207/2), (-147/2), (-83), (-72), (-117), (-114), (-81), (-100), (-88), (-197/2), (-297/2), (-136), (-147), (-111), (-98), (-119), (-261/2), (-117), (-172), (-184), (-145), (-131), (-154), (-333/2), (-152), (-212), (-225), (-183), (-168), (-184), (-337/2), (-182), (-207), (-191), (-146), (-160), (-225), (-417/2), (-223), (-250), (-233), (-185), (-200), (-270), (-505/2), (-268), (-250), (-279), (-228), (-244), (-451/2), (-601/2), (-317), (-298), (-591/2), (-483/2), (-545/2), (-253), (-270), (-350), (-330), (-695/2), (-581/2), (-270), (-303), (-321), (-300), (-385), (-807/2), (-687/2), (-322), (-357), (-376), (-354), (-444), (-927/2), (-801/2), (-378)]

/-- The grid of the inner table, as a function. -/
noncomputable def tIn (i : ℕ) : ℝ := ((tInL.getD i 0 : ℚ) : ℝ)

/-- The exponents of the inner table, as a function. -/
def kIn (i : ℕ) : ℤ := kInL.getD i 0

/-- The affine pieces of the inner table. -/
noncomputable def gIn (i : ℕ) (x : ℝ) : ℝ :=
  ((aInL.getD i 0 : ℚ) : ℝ) * x + ((bInL.getD i 0 : ℚ) : ℝ)

/-! ## Locating a point in a partition (`Apery/Growth/PieceIdx.lean`) -/

open Classical in
/-- The piece containing `x`. -/
noncomputable def pieceIdx (t : ℕ → ℝ) (m : ℕ) (x : ℝ) : ℕ := Nat.findGreatest (fun i => t i ≤ x) m

/-- The inner table as a function. -/
noncomputable def fIn (x : ℝ) : ℝ := gIn (pieceIdx tIn 125 x) x

/-! ## The outer table on `[20/37, 3]` (13 pieces, `Apery/Growth/OuterTable.lean`) -/

/-- The grid of the outer table. -/
def tOutL : List ℚ := [(20/37), (40/43), (1), (40/37), (3/2), (20/13), (60/37), (80/43), (2), (80/37), (5/2), (100/37), (120/43), (3)]

/-- The slopes of the outer table. -/
def aOutL : List ℚ := [(37/20), (37/20), (1), (42/5), (42/5), (97/10), (231/20), (51/10), (17/4), (429/40), (429/40), (503/40), (36/5)]

/-- The offsets of the outer table. -/
def bOutL : List ℚ := [(-1), (-1), (-2), (-10), (-10), (-12), (-15), (-3), (-5), (-19), (-19), (-24), (-9)]

/-- The grid of the outer table, as a function. -/
noncomputable def tOut (i : ℕ) : ℝ := ((tOutL.getD i 0 : ℚ) : ℝ)

/-- The affine pieces of the outer table. -/
noncomputable def gOut (i : ℕ) (x : ℝ) : ℝ :=
  ((aOutL.getD i 0 : ℚ) : ℝ) * x + ((bOutL.getD i 0 : ℚ) : ℝ)

end Apery


