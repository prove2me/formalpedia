-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Residue
-- name    : ChvatalOneHard398_SAT_Residue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:10.624914+00:00
-- url     : https://prove2.me/theorems/d3712601-76d3-4b72-824e-d1ccd61cdf7c
-- title:
--   The residue system and the formulas F(p,h,H,D,t)
-- statement:
--   Let $m,m'\ge1$, $D\ge2$, and $h\ge1$. Let $p_1,\ldots,p_s\ge2$ be pairwise coprime, with product $\Pi\ge2^h$. Let $H$ be an $m'\times m$ integer matrix with entries in $[0,D-1]$, and $t\in\mathbb Z^m$. CRT coefficients $\iota_j$ are the residues of $(\Pi/p_j)$ times its inverse modulo $p_j$, reduced modulo $\Pi$; extended gcd computes them. Put $d=Ht\bmod D$.
--
--   The system $X(p,h,H,D,t)$ has one multiple-choice group for each coordinate and modulus. The binary residue template first recovers each coordinate modulo $\Pi$, fixing digits above $h-1$ to zero, then checks $Hc=d\bmod D$ with another set of templates and digit fixings. It records $c$, $V$, and the quotient coefficient lists. The formula construction is exactly
--
--   $$F(p,h,H,D,t)=\operatorname{exactToSAT}\bigl(X(p,h,H,D,t+(2^{h-1}-1)\mathbf1)\bigr).$$
--
--   Thinness is the strict condition $\lambda_1(\Lambda_D^\perp(H))>m^{3/2}p_{\max}(2^h-1)/2$. A thin query is a formula from valid parameters satisfying this condition. The constructed-query predicate omits thinness. These predicates never include a rank or satisfiability guarantee as a field.
--
--   Explicit bookkeeping bounds are $C=6m(\sum_jp_j)(\lfloor\log_2\Pi\rfloor+2)+6m'mh(\lfloor\log_2D\rfloor+2)$ gates and $2m\sum_jp_j+66C$ formula variables. Candidate vector sets use precisely the asymmetric integer box of Proposition 16.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.22, §5.3, construction pp.22–23; p.25, proof of Proposition 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Functional

namespace ChvatalOneHard398.SAT
open scoped BigOperators

structure Params where
  m : ℕ
  r : ℕ
  p : List ℕ
  h : ℕ
  D : ℕ
  H : Matrix (Fin r) (Fin m) ℤ
  t : Fin m → ℤ

def Params.prod (a : Params) : ℕ := a.p.prod
def Params.pmax (a : Params) : ℕ := a.p.foldl max 0

def Params.Valid (a : Params) : Prop :=
  0 < a.m ∧ 0 < a.r ∧ 1 ≤ a.h ∧ 2 ≤ a.D ∧
  (∀ q ∈ a.p, 2 ≤ q) ∧ a.p.Pairwise Nat.Coprime ∧ 2 ^ a.h ≤ a.prod ∧
  (∀ i j, 0 ≤ a.H i j ∧ a.H i j < (a.D : ℤ))

/-- CRT coefficient in [0,Π), obtained by extended gcd, not by scanning [0,Π). -/
def Params.iota (a : Params) (j : ℕ) : ℕ :=
  let q := a.p[j]!
  let b := a.prod / q
  (((b : ℤ) * Nat.gcdA b q) % (a.prod : ℤ)).toNat

def Params.d (a : Params) (i : Fin a.r) : ℤ :=
  (∑ j, a.H i j * a.t j) % (a.D : ℤ)

def Params.freePerCoordinate (a : Params) : ℕ := a.p.sum

def Params.freeID (a : Params) (i j v : ℕ) : ℕ :=
  i * a.p.sum + (a.p.take j).sum + v

def Params.freeInputs (a : Params) (i : ℕ) : List ℕ :=
  (List.range a.p.length).flatMap fun j =>
    (List.range a.p[j]!).map (a.freeID i j)

def Params.freeWeights (a : Params) : List ℕ :=
  (List.range a.p.length).flatMap fun j =>
    (List.range a.p[j]!).map (fun v => a.iota j * v)

structure ResidueSystem where
  model : Functional
  rho : List (List ℕ)
  kappa : List IntLinear

/-- Parts one and two of §5.3; the high digits are fixed to zero. -/
def residueStageTwo (a : Params) : ResidueSystem := Id.run do
  let choices := (List.range a.m).flatMap fun i =>
    (List.range a.p.length).map fun j =>
      ((List.range a.p[j]!).map (a.freeID i j)).toFinset
  let mut X : Functional := ⟨a.m * a.p.sum,choices,[],[]⟩
  let mut rho := []
  let mut kappa := []
  for i in List.range a.m do
    let z := extendResidue X (a.freeInputs i) a.freeWeights a.prod
    X := z.model
    for u in z.digits.drop a.h do
      X := fixOutput X u false
    rho := rho ++ [z.digits]
    kappa := kappa ++ [z.quotient]
  return ⟨X,rho,kappa⟩

/-- All three parts of X(p,h,H,D,t), including the congruence-check fixings. -/
def residueSystem (a : Params) : ResidueSystem := Id.run do
  let z := residueStageTwo a
  let mut X := z.model
  let ins := (List.range a.m).flatMap fun i =>
    (List.range a.h).map fun l => (z.rho[i]!).getD l 0
  for r in List.finRange a.r do
    let weights := (List.finRange a.m).flatMap fun i =>
      (List.range a.h).map fun l => (((2 : ℤ)^l * a.H r i) % (a.D : ℤ)).toNat
    let w := extendResidue X ins weights a.D
    X := w.model
    for l in List.range w.digits.length do
      X := fixOutput X w.digits[l]! (Nat.testBit (a.d r).toNat l)
  return ⟨X,z.rho,z.kappa⟩

noncomputable def residuePoly (a : Params) := functionalPoly (residueSystem a).model

noncomputable def residueC (a : Params)
    (x : Fin (residueSystem a).model.dim → ℝ) (i : Fin a.m) : ℝ :=
  ((List.range a.h).map fun l => (2 : ℝ)^l * coord x (((residueSystem a).rho[i.val]!).getD l 0)).sum

noncomputable def residueV (a : Params)
    (x : Fin (residueSystem a).model.dim → ℝ) (i : Fin a.m) : ℝ :=
  ((List.range a.p.length).map fun j =>
    ((List.range a.p[j]!).map fun v => (a.iota j * v : ℕ) * coord x (a.freeID i j v)).sum).sum

/-- The actual formula used by Proposition 16, including its asymmetric-box shift. -/
def latticeFormula (a : Params) : Formula :=
  let shifted := {a with t := fun i => a.t i + ((2 : ℤ)^(a.h-1)-1)}
  exactToSAT (functionalExact (residueSystem shifted).model)

noncomputable def IsThin (a : Params) : Prop :=
  (a.m : ℝ) ^ (3 / 2 : ℝ) * a.pmax * ((2 : ℝ)^a.h-1) / 2 <
    RegevLWE.SmoothingLB.lambda1 (congruenceLattice a.D a.H)

noncomputable def ThinQuery (F : Formula) : Prop :=
  ∃ a : Params, a.Valid ∧ F = latticeFormula a ∧ IsThin a

def ConstructedQuery (F : Formula) : Prop :=
  ∃ a : Params, a.Valid ∧ F = latticeFormula a

/-- Explicit constants read from pp.22,24,26. -/
def gateBound (a : Params) : ℕ :=
  6*a.m*a.p.sum*(Nat.log 2 a.prod+2) + 6*a.r*a.m*a.h*(Nat.log 2 a.D+2)

def formulaBound (a : Params) : ℕ := 2*a.m*a.p.sum + 66*gateBound a

noncomputable def candidateVectors (a : Params) :=
  {y : Fin a.m → ℤ // y ∈ congruenceKernel a.D a.H ∧
    ∀ i, -((2 : ℤ)^(a.h-1)-1) ≤ a.t i-y i ∧ a.t i-y i ≤ (2 : ℤ)^(a.h-1)}

noncomputable def residueCandidates (a : Params) :=
  {c : Fin a.m → ℤ // (fun i => c i-a.t i) ∈ congruenceKernel a.D a.H ∧
    ∀ i, 0 ≤ c i ∧ c i ≤ (2 : ℤ)^a.h-1}

end ChvatalOneHard398.SAT


