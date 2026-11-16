-- Prove2me | Definitions.Def_QTolTest1673_Unified_Supplement_Rows
-- name    : QTolTest1673_Unified_Supplement_Rows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:18:55.217921+00:00
-- url     : https://prove2.me/theorems/90d3706e-b861-4ed5-9d98-b4b68e2285fa
-- title:
--   The explicit source tables and Boolean row functions
-- statement:
--   Fix $c=2^{17}$, $a=\lceil\log_2(ck)\rceil$, $K=k-a$, and $M=2^a$. A public encoding consists of one injection $\rho_z:[6]\hookrightarrow[K]$ per address $z\in\mathbb F_2^a$. The matrix $G$ has columns $e_1,e_2,e_3,e_1+e_2,e_1+e_3,e_2+e_3$. The YES table is $y_z=G(h|_{\rho_z})$ for a uniform hidden string; a uniform unrestricted table supplies the independent NO rows. Equation (10) explicitly computes $u_y(t)$, and the three kernel supports are those on page 32.
--
--   With sign data variables $X_{v,b}$, define the characters $A_{z,u}$ and $R_{z,j}$ from page 33 and compute
--   $$H(r)=1-\frac{(1-r_1)(1-r_2)(1-r_3)}4,\quad F_{z,y}(X)=A_{z,u_y(b_z)}(X)H(R_{z,1},R_{z,2},R_{z,3}),\quad f_y(z,X)=F_{z,y_z}(X).$$
--   The bit of $f_y$ is true exactly when this real sign expression is $-1$. No Fourier expansion is used to define the function. The input coordinates are ordered as $a$ address bits followed by $K$ pairs of data bits. Balanced shifts mean every three-bit vector occurs exactly $M/8$ times. Small-row matching means equality of every marginal assignment probability under the YES and NO source tables.
--
--   These are the concrete instances needed for Lemmas 8.1–8.3. In all asymptotic uses, $a\le k$ and $K\ge6$ are ensured, so natural subtraction and the injection space have the intended meanings.
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, §8.1–8.2 pp.31–34; §8.4 pp.37–39

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

noncomputable section
open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum

namespace QTolTest1673.Unified.Supplement

/-- Section 8.1 p.32: fixed c, address length, hidden length. -/
def c8 : ℕ := 2^17
def a8 (k : ℕ) : ℕ := ⌈Real.logb 2 ((c8*k : ℕ) : ℝ)⌉₊
def K8 (k : ℕ) : ℕ := k-a8 k
def n8 (k : ℕ) : ℕ := a8 k+2*K8 k
abbrev Encoding (a K : ℕ) := V a → (Fin 6 ↪ Fin K)
abbrev Table (a : ℕ) := V a → V 3

/-- The matrix G of §8.1, p.31 (one-based columns become zero-based). -/
def localG : Matrix (Fin 3) (Fin 6) (ZMod 2) :=
  ![![1,0,0,1,1,0], ![0,1,0,1,0,1], ![0,0,1,0,1,1]]

/-- Equation (10), p.32. -/
def localU (y t : V 3) : V 6 :=
  ![y 0+t 0+t 1, y 1+t 0+t 2, y 2+t 1+t 2, t 0, t 1, t 2]

/-- The three kernel-basis supports from p.32. -/
def kernelSupport (j : Fin 3) : Finset (Fin 6) :=
  ![{0,1,3}, {0,2,4}, {1,2,5}] j

/-- YES source table from the actual hidden string, not from a Fourier expansion. -/
def yesTable {a K : ℕ} (ρ : Encoding a K) (h : V K) : Table a :=
  fun z => localG.mulVec (fun r => h (ρ z r))

/-- Bit-to-sign conversion for a data coordinate. -/
def signBit (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

/-- Address coordinates first, followed by the K data pairs: a relabelling of n₀=2K+a. -/
def address {a K : ℕ} (x : V (a+2*K)) : V a := fun j => x ⟨j.val,by omega⟩
def dataSign {a K : ℕ} (x : V (a+2*K)) (v : Fin K) (b : ZMod 2) : ℝ :=
  signBit (x ⟨a+2*v.val+b.val,by have := b.val_lt; omega⟩)

/-- A_{i,u}, R_{i,j}, H, and (11), p.33–34. -/
def rowCharacter {a K : ℕ} (ρ : Encoding a K) (i : V a) (u : V 6)
    (x : V (a+2*K)) : ℝ := ∏ r, dataSign x (ρ i r) (u r)
def rowR {a K : ℕ} (ρ : Encoding a K) (i : V a) (j : Fin 3)
    (x : V (a+2*K)) : ℝ :=
  ∏ r ∈ kernelSupport j, dataSign x (ρ i r) 0 * dataSign x (ρ i r) 1
def rowH (r : Fin 3 → ℝ) : ℝ := 1-(1-r 0)*(1-r 1)*(1-r 2)/4

def rowValue {a K : ℕ} (ρ : Encoding a K) (shifts : V a → V 3)
    (y : Table a) (x : V (a+2*K)) : ℝ :=
  let i := address x
  rowCharacter ρ i (localU (y i) (shifts i)) x * rowH (fun j => rowR ρ i j x)

/-- Equation (13), p.34. Each factor in (11) is a sign; the bit is true exactly at -1. -/
def rowFn {a K : ℕ} (ρ : Encoding a K) (shifts : V a → V 3)
    (y : Table a) : BoolFn (a+2*K) := fun x => decide (rowValue ρ shifts y x = -1)

/-- Every three-bit shift occurs equally often, as required in Lemma 8.2. -/
def Balanced {a : ℕ} (shifts : V a → V 3) : Prop :=
  ∀ b, (Finset.univ.filter fun z => shifts z = b).card = 2^a/8

/-- Small-row marginal equality under uniform h and independent uniform NO rows. -/
def Matching {a K : ℕ} (ρ : Encoding a K) (δ : ℝ) : Prop :=
  ∀ I : Finset (V a), (I.card : ℝ) < δ*K → ∀ v : I → V 3,
    frac (fun h : V K => ∀ i : I, yesTable ρ h i = v i) =
      frac (fun y : Table a => ∀ i : I, y i = v i)

end QTolTest1673.Unified.Supplement


