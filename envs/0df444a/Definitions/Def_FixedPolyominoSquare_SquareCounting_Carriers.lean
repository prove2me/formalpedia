-- Prove2me | Definitions.Def_FixedPolyominoSquare_SquareCounting_Carriers
-- name    : FixedPolyominoSquare_SquareCounting_Carriers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:44.637767+00:00
-- url     : https://prove2.me/theorems/aafb0002-7e2a-4c63-9bb5-790fde78959e
-- title:
--   Tile-specific cavities and the actual geometric carriers
-- statement:
--   For a finite Wang inventory $W$ with $M_W$ tile types and colour counts $H_{\rm col},V_{\rm col}$, and a rectangle constant $R$, define
--
--   $$s_{\rm amp}=1024R^3,\quad K_s=4s_{\rm amp}\max(H_{\rm col},V_{\rm col}),\quad P_s=K_s+4M_W+64,\quad b_\star=P_s-8.$$
--
--   Tile types and colours use their fixed zero-based enumerations as the bijections $\jmath,\iota_H,\iota_V$. A carrier datum consists of four opening bits, a tile type and four labels in $\{0,\ldots,s_{\rm amp}-1\}$; the label is zero on a closed side. Its address is
--
--   $$A(a,b,\chi,\ell)=8+4(s_{\rm amp}\iota(\chi)+\ell)+2a+b.$$
--
--   The plug is $\{(0,1),(1,0),(1,1)\}$, and the cavity is its translate by $(16+4\jmath(u),16)$. The carrier starts with the $P_s$-square, removes this cavity and each active side's dent, and adds each active side's bump using exactly the four coordinates in the table on p. 17. West and south dents use the variable addresses; east and north dents use $b_\star$. The reciprocal bumps occupy $(-1,b_\star)$, $(P_s,A_H)$, $(b_\star,-1)$ and $(A_V,P_s)$.
--
--   The geometric family is the finite set of these unlabelled supports together with the plug, enumerated without duplicates. The quantity $J(n)$ is defined as the exact sum over nontrivial rectangular partitions of $s_{\rm amp}^{2n(n-1)-I(D)}\prod_{B\in D}a_{\rm rect}(w_B,h_B)$. No connectedness, bijection or error bound is a structure field or definition assumption. The intended specialization is $W=W_{\rm prod}$ and $R=R_{\rm rect}$; the construction layer remains parameterized until that specific Wang inventory is available.
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), pp. 16–18, Section 7; pp. 21–22, definition of J(n)

import Mathlib
import Definitions.Def_FixedPolyominoSquare_SquareCounting_WangModel
import Definitions.Def_FixedPolyominoSquare_SquareCounting_RectangularPartitions

namespace FixedPolyominoSquare.SquareCounting

noncomputable section
attribute [local instance] Classical.propDecidable

def sAmp (R : ℕ) : ℕ := 1024 * R ^ 3
def Ks (W : WangSystem) (R : ℕ) : ℕ := 4 * sAmp R * max W.horizontal W.vertical
def Ps (W : WangSystem) (R : ℕ) : ℕ := Ks W R + 4 * W.types + 64
def bStar (W : WangSystem) (R : ℕ) : ℕ := Ps W R - 8

/-- Directions 0,1,2,3 are west,east,south,north. Closed-side labels are zero. -/
abbrev CarrierData (W : WangSystem) (R : ℕ) :=
  {d : (Fin 4 → Bool) × Fin W.types × (Fin 4 → Fin (sAmp R)) //
    ∀ D, d.1 D = false → (d.2.2 D).val = 0}

instance carrierDataFinite (W : WangSystem) (R : ℕ) : Fintype (CarrierData W R) :=
  Fintype.ofFinite _

def opening {W : WangSystem} {R : ℕ} (d : CarrierData W R) : Fin 4 → Bool := d.val.1
def wangType {W : WangSystem} {R : ℕ} (d : CarrierData W R) : Fin W.types := d.val.2.1
def ampLabel {W : WangSystem} {R : ℕ} (d : CarrierData W R) : Fin 4 → Fin (sAmp R) := d.val.2.2

def address (R : ℕ) (a b : Bool) (colour label : ℕ) : ℕ :=
  8 + 4 * (sAmp R * colour + label) + 2 * (if a then 1 else 0) + (if b then 1 else 0)

def plug : Region := {(0, 1), (1, 0), (1, 1)}

def cavityOrigin {W : WangSystem} {R : ℕ} (d : CarrierData W R) : Cell :=
  ((16 + 4 * (wangType d).val : ℕ), 16)

def cavity {W : WangSystem} {R : ℕ} (d : CarrierData W R) : Region :=
  translate plug (cavityOrigin d)

def dent (W : WangSystem) (R : ℕ) (d : CarrierData W R) (D : Fin 4) : Cell :=
  let u := wangType d
  let η := opening d
  let l := ampLabel d
  let p : ℤ := Ps W R
  let b : ℤ := bStar W R
  if D = 0 then (0, (address R (η 2) (η 3) (W.west u).val (l 0).val : ℤ)) else
  if D = 1 then (p - 1, b) else
  if D = 2 then ((address R (η 0) (η 1) (W.south u).val (l 2).val : ℤ), 0) else
    (b, p - 1)

def bump (W : WangSystem) (R : ℕ) (d : CarrierData W R) (D : Fin 4) : Cell :=
  let u := wangType d
  let η := opening d
  let l := ampLabel d
  let p : ℤ := Ps W R
  let b : ℤ := bStar W R
  if D = 0 then (-1, b) else
  if D = 1 then (p, (address R (η 2) (η 3) (W.east u).val (l 1).val : ℤ)) else
  if D = 2 then (b, -1) else
    ((address R (η 0) (η 1) (W.north u).val (l 3).val : ℤ), p)

def carrier (W : WangSystem) (R : ℕ) (d : CarrierData W R) : Region :=
  let active := Finset.univ.filter fun D => opening d D = true
  (square (Ps W R) \ (cavity d ∪ active.image (dent W R d))) ∪ active.image (bump W R d)

/-- The family consists of geometric supports, with no invisible labels attached. -/
def starSupports (W : WangSystem) (R : ℕ) : Finset Region :=
  insert plug (Finset.univ.image (carrier W R))

def starFamily (W : WangSystem) (R : ℕ) : TileFamily where
  size := (starSupports W R).toList.length
  shape t := (starSupports W R).toList[t]

def macroEdges (n : ℕ) : ℕ := 2 * n * (n - 1)

def partitionTerm (W : WangSystem) (R n : ℕ) (D : Finset Region) : ℕ :=
  sAmp R ^ (macroEdges n - I n D) * ∏ B ∈ D, aRect W (width B) (height B)

/-- The exact nontrivial-partition sum, not a residual specified by an inequality. -/
def geometricJunk (W : WangSystem) (R n : ℕ) : ℕ :=
  ∑ D ∈ (Part n).filter (fun D => 2 ≤ D.card), partitionTerm W R n D

end
end FixedPolyominoSquare.SquareCounting


