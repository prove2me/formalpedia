-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_Supplement_Multiscale
-- name    : PolynomialSampling137_OneThird_Supplement_Multiscale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:47:17.333195+00:00
-- url     : https://prove2.me/theorems/76c9b81e-31f7-467f-9bce-51ccead817cd
-- title:
--   Deterministic quadratic tower and multiscale target
-- statement:
--   The binary field tower starts with $\mathbb F_2$. At each doubling it adjoins a root of $Z^2+Z+a$, taking $a$ to be the first trace-one vector in the ordered binary basis. Coordinate multiplication, trace tests, powers and seed slicing have complete finite recursive bodies. With $c=N-k$ and $D=\min\{\lfloor\log_2k\rfloor,\lfloor\log_4c\rfloor\}$, the retained blocks are those with $b_i\ge1$, where
--
--   $$w_i=D^{-1}+(i+1)^{-2}+(D-i+1)^{-2},\quad b_i=\frac{w_i}{32}\min\{k,c/(2^i-1)\},\quad r_i=2^{\lfloor\log_2\lfloor b_i\rfloor\rfloor}.$$
--
--   The map concatenates $\Phi_i$ on consecutive independent $r_i$-bit blocks, the remaining $k-\sum_i r_i$ uniform bits and $c-\sum_i r_i(2^i-1)$ zero bits. Comparisons use exact rationals. When $H=\min\{k,\sqrt c\}<2$, no blocks occur; if $k=0$ or $c=0$, all blocks are omitted. The family is fixed independently of the competing source degree. The runtime and flatness properties are subsequent theorem conclusions, not assumptions or fields of this definition.
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §2.5 and §4.3 Eq. (24), printed pp. 9–10, 17–18; PDF pp. 11–12, 19–20

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources
import Definitions.Def_PolynomialSampling137_OneThird_Supplement_BitAlgorithms

namespace PolynomialSampling137.OneThird.Supplement

/-- All coordinate arithmetic in the deterministic quadratic tower is executable.
The identity vector in every tower basis is its first basis vector. -/
def BasisWord (r j : ℕ) : Word r := fun i => if i.val = j then 1 else 0

def RawPower {r : ℕ} (mul : Word r → Word r → Word r) (x : Word r) : ℕ → Word r
  | 0 => BasisWord r 0
  | n + 1 => mul (RawPower mul x n) x

def RawSquareIterate {r : ℕ} (mul : Word r → Word r → Word r) (x : Word r) (i : ℕ) : Word r :=
  (fun z => mul z z)^[i] x

def RawTrace {r : ℕ} (mul : Word r → Word r → Word r) (x : Word r) : Word r :=
  ((List.range r).map (RawSquareIterate mul x)).foldl (· + ·) 0

/-- First trace-one basis vector, as stipulated in §2.5; the fallback is used
only on invalid raw arithmetic, and the tower starts with the genuine F₂. -/
def TowerParameter {r : ℕ} (mul : Word r → Word r → Word r) : Word r :=
  BasisWord r (((List.range r).find? (fun j =>
    decide (RawTrace mul (BasisWord r j) = BasisWord r 0))).getD 0)

def TowerMul : (a : ℕ) → Word (2 ^ a) → Word (2 ^ a) → Word (2 ^ a)
  | 0, x, y => fun i => x i * y i
  | a + 1, x, y =>
    let r := 2 ^ a
    let get := fun (z : Word (2 ^ (a + 1))) (offset : ℕ) =>
      fun i : Fin r => if h : offset + i.val < 2 ^ (a + 1) then z ⟨offset + i.val,h⟩ else 0
    let u := get x 0
    let v := get x r
    let u' := get y 0
    let v' := get y r
    let m := TowerMul a
    let vv := m v v'
    let low := m u u' + m (TowerParameter m) vv
    let high := m u v' + m v u' + vv
    fun i => if h : i.val < r then low ⟨i.val,h⟩
      else if h' : i.val - r < r then high ⟨i.val-r,h'⟩ else 0

def Cutoff (N k : ℕ) : ℕ := min (Nat.log 2 k) (Nat.log 4 (N-k))

def Weight (D i : ℕ) : ℚ :=
  1 / (D : ℚ) + 1 / ((i + 1 : ℕ) : ℚ)^2 + 1 / ((D-i+1 : ℕ) : ℚ)^2

def BlockCap (N k i : ℕ) : ℚ :=
  (Weight (Cutoff N k) i / 32) * min (k : ℚ) ((N-k : ℕ) / ((2 : ℚ)^i-1))

def BlockDimension (N k i : ℕ) : ℕ :=
  if BlockCap N k i < 1 then 0 else 2 ^ Nat.log 2 ⌊BlockCap N k i⌋₊

def Blocks (N k : ℕ) : List (ℕ × ℕ) :=
  if k = 0 ∨ N-k = 0 then [] else
    (((List.range (Cutoff N k)).map (fun j => (j+1, BlockDimension N k (j+1)))).filter
      (fun p => decide (0 < p.2)))

def TotalSeed (bs : List (ℕ × ℕ)) : ℕ := (bs.map Prod.snd).sum
def TotalExcess (bs : List (ℕ × ℕ)) : ℕ := (bs.map (fun p => p.2 * (2^p.1-1))).sum

def RawBlock (i r : ℕ) (seed : List (ZMod 2)) : List (ZMod 2) :=
  let a := Nat.log 2 r
  let x : Word (2^a) := fun j => seed.getD j.val 0
  ((List.range (2^i)).map (fun j =>
    List.ofFn (RawPower (TowerMul a) x (2*j+1)))).flatten

def BlockOutputs : List (ℕ × ℕ) → List (ZMod 2) → List (ZMod 2)
  | [], _ => []
  | (i,r)::bs, x => RawBlock i r (x.take r) ++ BlockOutputs bs (x.drop r)

/-- The actual degree-independent map in (24), with deterministic tower bases. -/
def UniversalSampler (N k : ℕ) (x : Word k) : Word N :=
  let bs := Blocks N k
  let seed := List.ofFn x
  let bits := BlockOutputs bs seed ++ seed.drop (TotalSeed bs) ++
    List.replicate (N-k-TotalExcess bs) 0
  fun i => bits.getD i.val 0

noncomputable def UniversalLaw (N k : ℕ) : Word N → ℝ := samplerMass (UniversalSampler N k)

noncomputable def ScaleH (N k : ℕ) : ℝ := min (k : ℝ) (Real.sqrt (N-k : ℕ))
noncomputable def LogTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

end PolynomialSampling137.OneThird.Supplement


