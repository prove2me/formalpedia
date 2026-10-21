-- Prove2me | Definitions.Def_RankOneBimatrix_BinSearch_Algorithm
-- name    : RankOneBimatrix_BinSearch_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:05.217803+00:00
-- url     : https://prove2.me/theorems/bf8871d7-281d-4cf9-92ba-b5afb7ef4034
-- title:
--   Figure 2, p. 20 — BINSEARCH
-- statement:
--   The state contains the lower and upper parameter bounds and the latest primal point. The algorithm uses their midpoint, solves the LPs named in Figure 2, updates one bound, and stops when its latest point lies on the hyperplane.
--
--   $$\lambda=(\underline\lambda+\overline\lambda)/2,\qquad x^{*\top}a=\lambda^*.$$
--
--   An oracle chooses optimal extreme LP solutions whenever such a solution exists. A separate condition records that every LP actually called received a genuine answer. This prevents an unconstrained answer on an unbounded LP from trivializing the goal.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, pp. 18–20, (39), Figure 2

import Definitions.Def_RankOneBimatrix_BinSearch_Setting

namespace RankOneBimatrix.BinSearch

open Matrix

variable {m n : ℕ}

/-- An optimal extreme solution of `Pλ`. -/
def PExtreme (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (lam : ℝ) : Set (PPoint m n) :=
  POpt A b lam ∩ Set.extremePoints ℝ (PFeas A b lam)

/-- An optimal extreme solution of `Dλ`. -/
def DExtreme (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (lam : ℝ) : Set (DPoint n) :=
  Yopt A b lam ∩ Set.extremePoints ℝ (DSet A)

/-- An optimal extreme solution of `Pmax`. -/
def PmaxExtreme (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ)
    (b : Fin n → ℝ) (M : Finset (Fin m)) (N : Finset (Fin n))
    (lam : ℝ) : Set (PolyPoint m n) :=
  PmaxOpt A a b M N lam ∩ Set.extremePoints ℝ (PmaxFeas A a b M N lam)

/-- An optimal extreme solution of `Pmin`. -/
def PminExtreme (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ)
    (b : Fin n → ℝ) (M : Finset (Fin m)) (N : Finset (Fin n))
    (lam : ℝ) : Set (PolyPoint m n) :=
  PminOpt A a b M N lam ∩ Set.extremePoints ℝ (PminFeas A a b M N lam)

/-- An optimal extreme solution of `BRmax`. -/
def BRmaxExtreme (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) : Set (PolyPoint m n) :=
  BRmaxOpt A b M N ∩ Set.extremePoints ℝ (PFace A b M N)

/-- An optimal extreme solution of `BRmin`. -/
def BRminExtreme (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) : Set (PolyPoint m n) :=
  BRminOpt A b M N ∩ Set.extremePoints ℝ (PFace A b M N)

/-- Selection functions for the LPs appearing in Figure 2, including its output LP. -/
structure Oracle (m n : ℕ) where
  primal : ℝ → PPoint m n
  dual : ℝ → DPoint n
  pmax : Finset (Fin m) → Finset (Fin n) → ℝ → PolyPoint m n
  pmin : Finset (Fin m) → Finset (Fin n) → ℝ → PolyPoint m n
  brmax : Finset (Fin m) → Finset (Fin n) → PolyPoint m n
  brmin : Finset (Fin m) → Finset (Fin n) → PolyPoint m n

/-- The oracle must return an optimal extreme solution whenever one exists. It may
return anything if the LP has no such solution; `callsGenuine` closes that gap. -/
def Admissible (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ)
    (b : Fin n → ℝ) (O : Oracle m n) : Prop :=
  (∀ lam, (PExtreme A b lam).Nonempty → O.primal lam ∈ PExtreme A b lam) ∧
  (∀ lam, (DExtreme A b lam).Nonempty → O.dual lam ∈ DExtreme A b lam) ∧
  (∀ M N lam, (PmaxExtreme A a b M N lam).Nonempty →
    O.pmax M N lam ∈ PmaxExtreme A a b M N lam) ∧
  (∀ M N lam, (PminExtreme A a b M N lam).Nonempty →
    O.pmin M N lam ∈ PminExtreme A a b M N lam) ∧
  (∀ M N, (BRmaxExtreme A b M N).Nonempty →
    O.brmax M N ∈ BRmaxExtreme A b M N) ∧
  (∀ M N, (BRminExtreme A b M N).Nonempty →
    O.brmin M N ∈ BRminExtreme A b M N)

/-- The bracket and the solution returned by the current loop iteration. -/
structure RunState (m n : ℕ) where
  lo : ℝ
  hi : ℝ
  sol : PolyPoint m n

/-- Figure 2, lines 5–17, including both strict-inequality BR replacements. -/
noncomputable def step (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (O : Oracle m n)
    (s : RunState m n) : RunState m n := by
  classical
  let lam := (s.lo + s.hi) / 2
  let p := O.primal lam
  let M := Mset A b lam
  let N := Nset A b lam
  if lam ≤ p.1 ⬝ᵥ a then
    let z := O.pmax M N lam
    let z' := if z.1 < z.2.1 ⬝ᵥ a then O.brmax M N else z
    exact ⟨z'.1, s.hi, z'⟩
  else
    let z := O.pmin M N lam
    let z' := if z.2.1 ⬝ᵥ a < z.1 then O.brmin M N else z
    exact ⟨s.lo, z'.1, z'⟩

/-- Figure 2, line 3. The empty strategy type is excluded by every theorem about the run. -/
noncomputable def initialState (a : Fin m → ℝ) : RunState m n :=
  ⟨sInf (Set.range a), sSup (Set.range a), (0, (fun _ => 0), 0, (fun _ => 0))⟩

/-- `run k` is the state before iteration `k`, with `k` counted from zero. -/
noncomputable def run (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (O : Oracle m n) : ℕ → RunState m n
  | 0 => initialState a
  | k + 1 => step A a b O (run A a b O k)

/-- The parameter passed to `Pλ` in line 6 of iteration `k`. -/
noncomputable def midpoint (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (O : Oracle m n) (k : ℕ) : ℝ :=
  ((run A a b O k).lo + (run A a b O k).hi) / 2

/-- Figure 2, line 18, evaluated after iteration `k`. -/
noncomputable def stop (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (O : Oracle m n) (k : ℕ) : Prop :=
  let z := (run A a b O (k + 1)).sol
  z.2.1 ⬝ᵥ a = z.1

/-- The λ* returned by iteration `k`. -/
noncomputable def lamStar (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (O : Oracle m n) (k : ℕ) : ℝ :=
  (run A a b O (k + 1)).sol.1

/-- The x* returned by iteration `k`. -/
noncomputable def xStar (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (O : Oracle m n) (k : ℕ) : Fin m → ℝ :=
  (run A a b O (k + 1)).sol.2.1

/-- Every LP actually called in iteration `k` has returned an optimal extreme
solution. In particular this prevents an unbounded BR LP from supplying junk. -/
noncomputable def callsGenuine (A : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (O : Oracle m n) (k : ℕ) : Prop :=
  let lam := midpoint A a b O k
  let M := Mset A b lam
  let N := Nset A b lam
  O.primal lam ∈ PExtreme A b lam ∧
  (if lam ≤ (O.primal lam).1 ⬝ᵥ a then
    O.pmax M N lam ∈ PmaxExtreme A a b M N lam ∧
      ((O.pmax M N lam).1 < (O.pmax M N lam).2.1 ⬝ᵥ a →
        O.brmax M N ∈ BRmaxExtreme A b M N)
  else
    O.pmin M N lam ∈ PminExtreme A a b M N lam ∧
      ((O.pmin M N lam).2.1 ⬝ᵥ a < (O.pmin M N lam).1 →
        O.brmin M N ∈ BRminExtreme A b M N))

end RankOneBimatrix.BinSearch


