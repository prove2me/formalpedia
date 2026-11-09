-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_Boosting
-- name    : CommutativeRankNC_Approximation_Boosting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:02.301011+00:00
-- url     : https://prove2.me/theorems/ecbe04a5-bb74-49e5-a194-d893fdb717ff
-- title:
--   Universal directions and the actual rank-boosting sequence
-- statement:
--   Enumerate every subset sum of $k$ signs from $H_{m+1}$ and map $\widetilde b=(b_0,\ldots,b_m)$ to $(b_i/b_0)_{i\ge1}$ when $b_0\ne0$, and to $(b_i)_{i\ge1}$ otherwise. This gives exactly $D_{k,m}$. Put
--
--   $$\beta_k=(3/50)^k,\quad\rho_k=1-\frac{k+1}{k}\beta_k,\quad\Delta_k(A)=kc-(k+1)\operatorname{rank}A.$$
--
--   The deficit is an integer. Start with the first maximum-rank sign evaluation; at each update take the first maximum-rank matrix among $A+\lambda B(b)$ for all listed $b$ and $0\le\lambda\le n$. Rank selection is specified by exhaustive finite minor tests, not a primitive circuit gate or a witness from the whole span. The fixed schedule is $T_k(n)=2\cdot50^k(\lfloor\log_2(kn+1)\rfloor+1)$, independent of the unknown optimum. Complexity of realizing this semantic sequence by circuits remains theorem work.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), §§5.1–5.2, pp.21–27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Schur
import Definitions.Def_CommutativeRankNC_Approximation_Signs
import Definitions.Def_CommutativeRankNC_Approximation_BooleanNC

noncomputable section

namespace CommutativeRankNC.Approximation

/-- A tuple of k sign seeds is enumerated in base q⁴, and the subset S⊆[k]
is enumerated by k bits. Repetitions are retained in the list. -/
def subsetSignSum (k s tuple subset : ℕ) (i : Fin s) : ℤ :=
  ∑ j ∈ Finset.range k, if subset.testBit j then
    (if signSeed s 4 ((tuple / seedCard s 4 ^ j) % seedCard s 4) i then -1 else 1)
    else 0

def directionFromSum {m : ℕ} (b : Fin (m+1) → ℤ) : Fin m → ℚ :=
  fun i => if b 0 = 0 then (b i.succ : ℚ) else (b i.succ : ℚ) / (b 0 : ℚ)

/-- Exactly the dehomogenized image of Z_{k,m+1}, including the b₀=0 branch. -/
def directionList (k m : ℕ) : List (Fin m → ℚ) :=
  (List.range (seedCard (m+1) 4 ^ k)).flatMap fun tuple =>
    (List.range (2 ^ k)).map fun subset =>
      directionFromSum (subsetSignSum k (m+1) tuple subset)

def directionFamily (k m : ℕ) : Finset (Fin m → ℚ) := (directionList k m).toFinset

def beta (k : ℕ) : ℝ := (3 / 50 : ℝ) ^ k
def rho (k : ℕ) : ℝ := 1 - ((k+1 : ℕ) : ℝ) / (k : ℝ) * beta k

def deficit {n m : ℕ} (k : ℕ) (B : Fin m → QMatrix n) (A : QMatrix n) : ℤ :=
  (k : ℤ) * (commutativeRank B : ℤ) - ((k : ℤ)+1) * (A.rank : ℤ)

/-- Concrete rank computation by testing finite square minors; this semantic
definition claims no time bound. The circuit theorem must establish Boolean
parallel bounds rather than charge this whole function as a primitive gate. -/
def minorRank {n : ℕ} (A : QMatrix n) : ℕ :=
  ((List.range (n+1)).filter fun d => decide (∃ (rows cols : Fin d → Fin n),
    Function.Injective rows ∧ Function.Injective cols ∧
      (A.submatrix rows cols).det ≠ 0)).foldl max 0

/-- First maximum in a specified finite list; no maximum-rank matrix in the
whole span is used as advice or chosen as the algorithm's output. -/
def firstMaxRank {n : ℕ} (candidates : List (QMatrix n)) : QMatrix n :=
  match candidates with
  | [] => 0
  | A :: tail => tail.foldl (fun best candidate =>
      if minorRank best < minorRank candidate then candidate else best) A

def initialMatrix {n m : ℕ} (B : Fin m → QMatrix n) : QMatrix n :=
  firstMaxRank ((signList m 4).map fun e => pencilEval B (fun i => signValue (e i)))

def updateMatrix {n m : ℕ} (k : ℕ) (B : Fin m → QMatrix n) (A : QMatrix n) : QMatrix n :=
  firstMaxRank ((directionList k m).flatMap fun b =>
    (List.range (n+1)).map fun l => A + (l : ℚ) • pencilEval B b)

def iterateMatrix {n m : ℕ} (k : ℕ) (B : Fin m → QMatrix n) : ℕ → QMatrix n
  | 0 => initialMatrix B
  | j+1 => updateMatrix k B (iterateMatrix k B j)

/-- Predetermined logarithmic schedule, using no commutative-rank advice.
The deliberately generous constant is uniform over n and all inputs. -/
def roundSchedule (k n : ℕ) : ℕ := 2 * 50 ^ k * (Nat.log2 (k*n+1) + 1)

end CommutativeRankNC.Approximation


