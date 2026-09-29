-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_TMI
-- name    : CK_CKLaneM07_CE_TMI
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:59:30.555429+00:00
-- url     : https://prove2.me/theorems/da5af10b-c615-40b5-8387-a31dffd45e28
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.TMI` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.TMI` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.TMI` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.TMI (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/TMI.lean)

import Definitions.Def_CK_CKLaneD_LogCert

-- ===== source module CKLaneM07.CE.TMI =====
section

/-!
# Lane M07 / CE-stat: fixed-point bivariate Taylor models (computational kernel)

Fixed point: an `Int` `n` represents `n / 2^PB`.  A Taylor model `⟨p, r⟩` (`p` a list of rows of
`Int`s, row `i` = coefficients of `x^i y^j`; `r : ℕ`) encloses a real `v` at `(x, y)` with
`|x|, |y| ≤ 1` when `|v - p(x,y)/2^PB| ≤ r/2^PB`.  Products keep only total degree `≤ K` (exactly),
bound the dropped part by degree-aggregated absolute sums, and floor-rescale (error `< 1` unit per
coefficient).  `log` and reciprocal use the series of `log (1 + w)` / `1/(1 + w)` around the constant
coefficient, with rational tails and Lane D logarithm certificates for the centre.

This file is the executable part mirrored exactly by `M07/work/cestat/tmint.py`; soundness lemmas are
developed separately.
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open CKLaneD

def PB : ℕ := 80
def ONE : ℤ := 2 ^ PB
def ONEn : ℕ := 2 ^ PB

abbrev RowI := List ℤ
abbrev PolI := List RowI

def rowAdd : RowI → RowI → RowI
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: rowAdd p q

def pAdd : PolI → PolI → PolI
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => rowAdd a b :: pAdd p q

def pNeg (p : PolI) : PolI := p.map (List.map (fun a => -a))

def rowAbs (r : RowI) : ℕ := r.foldr (fun a s => a.natAbs + s) 0
def pAbs (p : PolI) : ℕ := p.foldr (fun r s => rowAbs r + s) 0
def pCount (p : PolI) : ℕ := p.foldr (fun r s => r.length + s) 0

def pC00 (p : PolI) : ℤ :=
  match p with
  | (a :: _) :: _ => a
  | _ => 0

/-- first `n` coefficients of the product of two rows -/
def rowMulT : ℕ → RowI → RowI → RowI
  | 0, _, _ => []
  | _, [], _ => []
  | n + 1, a :: r, s => rowAdd ((s.take (n + 1)).map (fun b => a * b)) (0 :: rowMulT n r s)

def rowsFrom (K i1 : ℕ) (r : RowI) : ℕ → PolI → PolI
  | _, [] => []
  | i2, s :: q =>
      if i1 + i2 ≤ K then rowMulT (K + 1 - (i1 + i2)) r s :: rowsFrom K i1 r (i2 + 1) q else []

/-- exact kept coefficients (total degree `≤ K`) of `p * q` (scale `2^(2 PB)`) -/
def pMulKept (K : ℕ) (q : PolI) : ℕ → PolI → PolI
  | _, [] => []
  | i1, r :: p => if i1 ≤ K then pAdd (rowsFrom K i1 r 0 q) ([] :: pMulKept K q (i1 + 1) p) else []

/-- degree-aggregated absolute values: entry `d` = `∑_{i+j=d} |c_ij|` -/
def natRowAdd : List ℕ → List ℕ → List ℕ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: natRowAdd p q

def degAbsAux : ℕ → PolI → List ℕ
  | _, [] => []
  | i, r :: p => natRowAdd (List.replicate i 0 ++ r.map Int.natAbs) (degAbsAux (i + 1) p)

def degAbs (p : PolI) : List ℕ := degAbsAux 0 p

/-- `∑_{d1 + d2 > K} a_{d1} b_{d2}` -/
def dropSum (K : ℕ) (a b : List ℕ) : ℕ :=
  let bt := b.foldr (· + ·) 0
  (a.zipIdx).foldr (fun x s =>
    let d1 := x.2
    let keep := ((b.take (K + 1 - d1)).foldr (· + ·) 0)
    s + x.1 * (if d1 ≤ K then bt - keep else bt)) 0

def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- bound on the part of `r * s` dropped by `rowMulT n r s` (same recursion) -/
def rowDropT : ℕ → RowI → RowI → ℕ
  | 0, r, s => rowAbs r * rowAbs s
  | _, [], _ => 0
  | n + 1, a :: r, s => a.natAbs * rowAbs (s.drop (n + 1)) + rowDropT n r s

def rowsDrop (K i1 : ℕ) (r : RowI) : ℕ → PolI → ℕ
  | _, [] => 0
  | i2, s :: q =>
      if i1 + i2 ≤ K then rowDropT (K + 1 - (i1 + i2)) r s + rowsDrop K i1 r (i2 + 1) q
      else rowAbs r * pAbs (s :: q)

/-- bound on the part of `p * q` dropped by `pMulKept K q i1 p` (same recursion) -/
def pDrop (K : ℕ) (q : PolI) : ℕ → PolI → ℕ
  | _, [] => 0
  | i1, r :: p =>
      if i1 ≤ K then rowsDrop K i1 r 0 q + pDrop K q (i1 + 1) p
      else pAbs (r :: p) * pAbs q

structure TMI where
  p : PolI
  r : ℕ
  deriving Repr

def TMI.const (c : ℤ) (r : ℕ := 0) : TMI := ⟨[[c]], r⟩
def TMI.add (s t : TMI) : TMI := ⟨pAdd s.p t.p, s.r + t.r⟩
def TMI.neg (s : TMI) : TMI := ⟨pNeg s.p, s.r⟩
def TMI.sub (s t : TMI) : TMI := s.add t.neg
def TMI.addC (c : ℤ) (s : TMI) : TMI := s.add (TMI.const c)

def TMI.mul (K : ℕ) (s t : TMI) : TMI :=
  let kept := pMulKept K t.p 0 s.p
  let rp := kept.map (List.map (fun a => a / ONE))
  let drop := pDrop K t.p 0 s.p
  let bs := pAbs s.p
  let bt := pAbs t.p
  ⟨rp, cdiv drop ONEn + pCount rp + cdiv (s.r * bt) ONEn + cdiv (t.r * bs) ONEn + cdiv (s.r * t.r) ONEn⟩

/-- multiply by the fixed-point constant `k / 2^PB` -/
def TMI.mulC (k : ℤ) (s : TMI) : TMI :=
  let rp := s.p.map (List.map (fun a => k * a / ONE))
  ⟨rp, cdiv (k.natAbs * s.r) ONEn + pCount rp⟩

def TMI.center (s : TMI) : TMI :=
  match s.p with
  | (_ :: r0) :: p => ⟨(0 :: r0) :: p, s.r⟩
  | _ => s

def TMI.lo (s : TMI) : ℤ := pC00 s.p - ((pAbs s.p : ℤ) - (pC00 s.p).natAbs) - s.r
def TMI.hi (s : TMI) : ℤ := pC00 s.p + ((pAbs s.p : ℤ) - (pC00 s.p).natAbs) + s.r

/-- `⌊q · 2^PB⌋` and `⌈q · 2^PB⌉` -/
def qfl (q : ℚ) : ℤ := ⌊q * (ONE : ℚ)⌋
def qcl (q : ℚ) : ℕ := (⌈q * (ONE : ℚ)⌉).toNat

/-- `w = (u - u0)/u0` with `u0` the constant coefficient; returns `(w, inv)` -/
def TMI.wOf (s : TMI) : TMI × ℤ :=
  let u0 := pC00 s.p
  let inv := (ONE * ONE) / u0
  let c := s.center
  let w := TMI.mulC inv c
  (⟨w.p, w.r + cdiv (pAbs c.p + c.r) ONEn + 1⟩, inv)

def rhoQ (w : TMI) : ℚ := ((pAbs w.p + w.r : ℕ) : ℚ) / (ONEn : ℚ)

/-- Horner for `∑_{k=1}^n (-1)^(k+1) w^k / k` (coefficient rounding tracked) -/
def logHorner (K : ℕ) (w : TMI) : ℕ → TMI → TMI
  | 0, acc => acc
  | k + 1, acc =>
      let t := (TMI.mul K acc w).addC (qfl (((-1 : ℚ) ^ (k + 2)) / ((k + 1 : ℕ) : ℚ)))
      logHorner K w k ⟨t.p, t.r + 1⟩

/-- `log u` given series length `n ≥ 1` and a certificate enclosure `[lo, hi]` of `log(u0/2^PB)`;
`none` if a side condition fails. -/
def TMI.log (K n : ℕ) (s : TMI) (lo hi : ℚ) : Option TMI :=
  let wi := s.wOf
  let w := wi.1
  let rho := rhoQ w
  if 0 < pC00 s.p ∧ rho < 1 ∧ 1 ≤ n then
    let top := TMI.const (qfl (((-1 : ℚ) ^ (n + 1)) / (n : ℚ))) 1
    let acc := TMI.mul K (logHorner K w (n - 1) top) w
    let tail := rho ^ (n + 1) / (1 - rho)
    let res := acc.addC (qfl ((lo + hi) / 2))
    some ⟨res.p, res.r + qcl tail + qcl ((hi - lo) / 2) + 1⟩
  else none

def recHorner (K : ℕ) (w : TMI) : ℕ → TMI → TMI
  | 0, acc => acc
  | k + 1, acc => recHorner K w k ((TMI.mul K acc w).addC ((-1) ^ k * ONE))

/-- `1/u` (positive centre) with series length `n` -/
def TMI.recip (K n : ℕ) (s : TMI) : Option TMI :=
  let wi := s.wOf
  let w := wi.1
  let inv := wi.2
  let rho := rhoQ w
  if 0 < pC00 s.p ∧ rho < 1 then
    let acc := recHorner K w n (TMI.const ((-1) ^ n * ONE))
    let tail := rho ^ (n + 1) / (1 - rho)
    let res := TMI.mulC inv acc
    some ⟨res.p, res.r + cdiv (pAbs acc.p + acc.r) ONEn + 1 + qcl (tail * (((inv + 1 : ℤ) : ℚ) / (ONE : ℚ)))⟩
  else none

end CKLaneM07.CE

end


