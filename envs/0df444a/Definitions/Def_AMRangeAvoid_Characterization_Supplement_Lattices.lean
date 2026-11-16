-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Supplement_Lattices
-- name    : AMRangeAvoid_Characterization_Supplement_Lattices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:23:26.959476+00:00
-- url     : https://prove2.me/theorems/9da3b72d-8715-4b9e-b4cd-b5fb28bc596d
-- title:
--   Rational lattice instances, gap promises and the approximation factor
-- statement:
--   A lattice instance consists of a positive dimension $n$, a nonsingular rational matrix $B\in\mathbb Q^{n\times n}$ and a positive rational threshold $d$. Signed binary integer and reduced rational codes impose no coefficient bound. The lattice is $L(B)=\{Bz:z\in\mathbb Z^n\}$, with the Euclidean norm.
--
--   $$\overline{\mathrm{GapSVP}}_\gamma:\quad \mathrm{YES}:\lambda_1(L(B))>\gamma(n)d,\qquad\mathrm{NO}:\lambda_1(L(B))\le d.$$
--
--   The short side asserts existence of a nonzero short lattice vector; the long side quantifies over all nonzero coefficient vectors. Thus no default-valued infimum is used. GapSVP exchanges these promised sides. The source approximation factor is $\gamma(n)=400\lceil\sqrt{n/\log_2 n}\rceil$ for $n\ge2$, with $\gamma(1)=400$ to retain one-dimensional instances. The generic promise interface clamps supplied factors below one; the paper's factor is unchanged. Theta growth means fixed positive upper and lower constants and one uniform dimension threshold. Invalid lattice codes are unpromised.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), §2.4, Definitions 2.12–2.13, Theorem 4.6 and Corollary 5.3, printed pp.12,21–25 (PDF pp.14,23–27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Complexity

namespace AMRangeAvoid.Characterization.Supplement

/-- Signed magnitude, with a canonical binary magnitude; zero has positive sign. -/
def intCode (z : ℤ) : Bits := [decide (z < 0)] ++ natCode z.natAbs

def readInt (b : Bits) : Option (ℤ × Bits) := do
  let sign ← b.head?
  let (n, rest) ← readNat b.tail
  if sign && decide (n = 0) then none
  else pure ((if sign then -(n : ℤ) else (n : ℤ)), rest)

def ratCode (q : ℚ) : Bits := intCode q.num ++ natCode q.den

def readRat (b : Bits) : Option (ℚ × Bits) := do
  let (a, rest) ← readInt b
  let (d, rest) ← readNat rest
  if d = 0 then none else
    let q : ℚ := a / d
    if q.num = a ∧ q.den = d then pure (q, rest) else none

def readRats : ℕ → Bits → Option (List ℚ × Bits)
  | 0, b => some ([], b)
  | n + 1, b => do
    let (a, rest) ← readRat b
    let (as, tail) ← readRats n rest
    pure (a :: as, tail)

/-- Arbitrary rational bases, with no coefficient bound. Positive dimension,
full rank and a positive rational threshold are validity conditions on inputs. -/
structure LatticeInstance where
  n : ℕ
  basis : Matrix (Fin n) (Fin n) ℚ
  threshold : ℚ

def LatticeInstance.valid (I : LatticeInstance) : Prop :=
  0 < I.n ∧ I.basis.det ≠ 0 ∧ 0 < I.threshold

instance latticeInstanceValidDecidable (I : LatticeInstance) : Decidable I.valid := inferInstanceAs
  (Decidable (0 < I.n ∧ I.basis.det ≠ 0 ∧ 0 < I.threshold))

def LatticeInstance.code (I : LatticeInstance) : Bits :=
  natCode I.n ++ (List.ofFn (fun i => List.ofFn (fun j => ratCode (I.basis i j)))).flatten.flatten ++
    ratCode I.threshold

def readLattice (b : Bits) : Option LatticeInstance := do
  let (n, rest) ← readNat b
  let (entries, rest) ← readRats (n * n) rest
  let (d, rest) ← readRat rest
  let I : LatticeInstance := ⟨n, fun i j => entries.getD (i.val * n + j.val) 0, d⟩
  if rest = [] then pure I else none

def decodeLattice (b : Bits) : Option LatticeInstance :=
  match readLattice b with
  | none => none
  | some I => if I.valid then some I else none

/-- The Euclidean lattice vector, NOT the sup norm on the function space. -/
def latticeVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (z : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => ∑ j, (B i j : ℝ) * (z j : ℝ))

def rationalLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) :
    Set (EuclideanSpace ℝ (Fin n)) := Set.range (latticeVector B)

/-- No default-valued infimum: λ₁≤d is existence of a nonzero short vector,
and λ₁>γd is that every nonzero lattice vector is strictly longer. For a valid
positive-dimensional full-rank lattice these are exactly the source minima. -/
def Short (I : LatticeInstance) : Prop :=
  ∃ z : Fin I.n → ℤ, z ≠ 0 ∧ ‖latticeVector I.basis z‖ ≤ (I.threshold : ℝ)

def Long (γ : ℕ → ℝ) (I : LatticeInstance) : Prop :=
  ∀ z : Fin I.n → ℤ, z ≠ 0 →
    γ I.n * (I.threshold : ℝ) < ‖latticeVector I.basis z‖

/-- Exact source choice, with the source's undefined log₂1 quotient completed
at dimension one. Dimension-one inputs are retained. -/
noncomputable def gamma (n : ℕ) : ℝ :=
  if n ≤ 1 then 400 else 400 * max 1 (⌈Real.sqrt ((n : ℝ) / Real.logb 2 n)⌉₊ : ℝ)

/-- A genuine Θ assertion: fixed positive constants and a dimension threshold. -/
def SqrtTheta (g : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
    c * Real.sqrt ((n : ℝ) / Real.logb 2 n) ≤ g n ∧
      g n ≤ C * Real.sqrt ((n : ℝ) / Real.logb 2 n)

/-- General approximation factors are clamped at one solely to give a disjoint
promise for arbitrary parameters. Every factor γ≥1, including the source's
factor, is unchanged. -/
def GapYes (g : ℕ → ℝ) : Set Bits := {b | ∃ I,
  decodeLattice b = some I ∧ Long (fun n => max 1 (g n)) I}

def GapNo : Set Bits := {b | ∃ I, decodeLattice b = some I ∧ Short I}

noncomputable def CoGapSVP (g : ℕ → ℝ) : PromiseProblem where
  yes := GapYes g
  no := GapNo
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨I, hi, hl⟩ ⟨J, hj, z, hz, hs⟩
    have e : I = J := Option.some.inj (hi.symm.trans hj)
    subst J
    have hd : (0 : ℝ) < I.threshold := by
      have hv : I.valid := by
        unfold decodeLattice at hi
        split at hi
        next => simp at hi
        next J _ =>
          split at hi
          next hvalid =>
            have he := Option.some.inj hi
            subst I
            exact hvalid
          next => simp at hi
      exact_mod_cast hv.2.2
    have hb : (I.threshold : ℝ) ≤ max 1 (g I.n) * (I.threshold : ℝ) := by
      nlinarith [le_max_left (1 : ℝ) (g I.n)]
    exact (not_lt_of_ge (hs.trans hb)) (hl z hz)

noncomputable def GapSVP (g : ℕ → ℝ) : PromiseProblem := complement (CoGapSVP g)

end AMRangeAvoid.Characterization.Supplement


