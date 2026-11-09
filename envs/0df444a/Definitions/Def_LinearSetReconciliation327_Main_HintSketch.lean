-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintSketch
-- name    : LinearSetReconciliation327_Main_HintSketch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:32.501944+00:00
-- url     : https://prove2.me/theorems/a45b4162-40b0-4eee-891c-9b64adb08b63
-- title:
--   §§3.3, 5.2–5.3 — HintSketch parameters, stopping rules, worker, capacities, tree
-- statement:
--   For constants $A,C$, universe $n$ and $\lambda$: $\eta=\log^{-A}n$, $\lambda_*=\lambda+C\lceil\log\log(n+2)\rceil+C$, and at a node $(N,X,Y)$: $D=\min\{N,X+Y\}$, $m=\max\{Y,\lceil X/\log^3n\rceil\}$, $t=\min(N,\lceil2\eta(D+1)\rceil)$, with first applicable rule cheap ($D\le N/\log^{10}n$), small ($D\le C^3\lambda_*\log^6n/\eta^2$), recursive ($m=Y$), direct. $N_{\max},B_X,B_Y,\ell$ are equation (16), and $c=2\lceil\log(N/Y)\rceil+C$ at a recursive node, $0$ at a direct one. The row code is $B_{j,s}(C)=\sum_{v\in C}\beta_{j,v,s}$ with uniform bits. `workerPredict` is Algorithm 3: abstain if $|J_j|>B_X$; otherwise test $r=0,1,\dots,\min\{B_Y,N_j-|J_j|\}$, eligible only when $a\ge\sigma_{j,r}+c$, and predict from the member of the first singleton family $C^{(a)}_{j,r}$. `workerFinal` returns the unique member of the union of the families, or $\emptyset$. The reference placement of Definition 5.5 gives $\sigma_j^*$ and $Q_s=\sum_j\mathbb E[G_{s-1}(\sigma_j^*+c)]$, and equation (19) gives $X_s,Y_s$. `tree` builds the recursion from these rules, with fuel since termination is only known from Lemma 5.10.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), §3.3 and §5.2–5.3, PDF p.14–15, 20–22 (printed p.13–14, 19–21)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Framework

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! The HintSketch construction: §3.3 (PDF pp.14–15) with the parameters of §§5.2–5.3 (PDF pp.20–22). -/

/-- Global parameters: the absolute constants `A, C`, the original universe `n`, and `λ`. -/
structure HintParams where
  A : ℕ
  C : ℕ
  n : ℕ
  lam : ℕ

namespace HintParams

variable (P : HintParams)

/-- `log n`. -/
def lgn : ℝ := lg P.n
/-- `η = log^{-A} n`. -/
def eta : ℝ := (P.lgn ^ P.A)⁻¹
/-- `λ_* = λ + C⌈log log(n+2)⌉ + C`. -/
def lamStar : ℕ := P.lam + P.C * ⌈lg (lg ((P.n : ℝ) + 2))⌉₊ + P.C

/-- `D = min{N, X+Y}`. -/
def D (N X Y : ℕ) : ℕ := min N (X + Y)
/-- `m = max{Y, ⌈X / log³ n⌉}`. -/
def rows (X Y : ℕ) : ℕ := max Y ⌈(X : ℝ) / P.lgn ^ 3⌉₊
/-- `t = min(N, ⌈2η(D+1)⌉)`. -/
def resid (N X Y : ℕ) : ℕ := min N ⌈2 * P.eta * ((D N X Y : ℝ) + 1)⌉₊

/-- The four rules of §5.2. -/
inductive Rule where
  | cheap | small | recursive | direct
  deriving DecidableEq

open Classical in
/-- The first applicable rule of §5.2. -/
def rule (N X Y : ℕ) : Rule :=
  if (D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10 then .cheap
  else if (D N X Y : ℝ) ≤ (P.C : ℝ) ^ 3 * P.lamStar * P.lgn ^ 6 / P.eta ^ 2 then .small
  else if P.rows X Y = Y then .recursive
  else .direct

/-- `N_max = ⌈N/m⌉`. -/
def Nmax (N X Y : ℕ) : ℕ := ⌈(N : ℝ) / (P.rows X Y : ℝ)⌉₊
/-- `B_X = min{N_max, ⌈log³ n + C log² n⌉}`, equation (16). -/
def BX (N X Y : ℕ) : ℕ := min (P.Nmax N X Y) ⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊
/-- `B_Y = min{N_max, ⌈C log(log n + 2)⌉ + 4}`, equation (16). -/
def BY (N X Y : ℕ) : ℕ := min (P.Nmax N X Y) (⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ + 4)
/-- `ℓ = B_X + B_Y⌈log(eN_max)⌉ + B_Y + ⌈log(16/η²)⌉ + 10`, equation (16). -/
def ell (N X Y : ℕ) : ℕ :=
  P.BX N X Y + P.BY N X Y * ⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ + P.BY N X Y +
    ⌈lg (16 / P.eta ^ 2)⌉₊ + 10

open Classical in
/-- `c = 2⌈log(N/Y)⌉ + C` at a recursive node, `c = 0` at a direct node. -/
def c (N X Y : ℕ) : ℕ :=
  if P.rule N X Y = .recursive then 2 * ⌈lg ((N : ℝ) / (Y : ℝ))⌉₊ + P.C else 0

/-- `B_{j,s}(C) = ∑_{v∈C} β_{j,v,s}`, equation (6), for one row's coins. Indices are 0-based; a row
never has an index at or above `N_max`. -/
def rowBit {ℓ K : ℕ} (β : Fin ℓ → Fin K → ZMod 2) (C : Finset ℕ) (s : Fin ℓ) : ZMod 2 :=
  ∑ v ∈ C, if h : v < K then β s ⟨v, h⟩ else 0

/-- `σ_{j,r} = ⌈log(2^{|J_j|} ∑_{h=0}^r binom(N_j-|J_j|, h))⌉`, equation (7). -/
def sigma (jCard Nj r : ℕ) : ℕ :=
  ⌈lg (((2 ^ jCard * ∑ h ∈ range (r + 1), (Nj - jCard).choose h : ℕ)) : ℝ)⌉₊

open Classical in
/-- The family `C^{(a)}_{j,r}` for the prefix `z` of length `a`: the sets `Z ∪ A` with `Z ⊆ J_j`,
`A ⊆ [N_j] \ J_j`, `|A| = r`, whose first `a` bits are `z`. -/
def family {ℓ K : ℕ} (Nj : ℕ) (β : Fin ℓ → Fin K → ZMod 2) (Jj : Finset ℕ) (r : ℕ)
    (z : List (ZMod 2)) : Finset (Finset ℕ) :=
  (range Nj).powerset.filter fun C =>
    (C \ Jj).card = r ∧ ((List.finRange ℓ).take z.length).map (rowBit β C) = z

open Classical in
/-- Algorithm 3, one prediction: abstain when `|J_j| > B_X`; otherwise test `r = 0, 1, …` up to
`min{B_Y, N_j - |J_j|}`, only when `a ≥ σ_{j,r} + c`, and predict from the member of the first singleton
family; abstain if none qualifies. -/
def workerPredict (N m ℓ K : ℕ) (BX BY c : ℕ) (j : Fin m) (β : Fin ℓ → Fin K → ZMod 2)
    (Jj : Finset ℕ) (z : List (ZMod 2)) : Option (ZMod 2) :=
  let Nj := rowLen N m j.val
  if BX < Jj.card then none else
  match (List.range (min BY (Nj - Jj.card) + 1)).find? (fun r =>
      decide (sigma Jj.card Nj r + c ≤ z.length ∧ (family Nj β Jj r z).card = 1)) with
  | none => none
  | some r =>
      if h : z.length < ℓ then
        ((family Nj β Jj r z).toList.head?).map fun C => rowBit β C ⟨z.length, h⟩
      else none

open Classical in
/-- Algorithm 3, final recovery: the unique member of the union of the families on the full transcript
(with no waiting restriction), and `∅` if it is not unique or `|J_j| > B_X`. -/
def workerFinal (N m ℓ K : ℕ) (BX BY : ℕ) (j : Fin m) (β : Fin ℓ → Fin K → ZMod 2)
    (Jj : Finset ℕ) (z : List (ZMod 2)) : Finset ℕ :=
  let Nj := rowLen N m j.val
  if BX < Jj.card then ∅ else
  let U := (range (min BY (Nj - Jj.card) + 1)).biUnion fun r => family Nj β Jj r z
  if U.card = 1 then (U.toList.head?).getD ∅ else ∅

/-- The row scheme of a HintSketch node `(N, X, Y)`. -/
def scheme (N X Y : ℕ) : RowScheme where
  N := N
  m := P.rows X Y
  ℓ := P.ell N X Y
  Rand := Fin (P.ell N X Y) → Fin (P.Nmax N X Y) → ZMod 2
  code := fun _ r C s => rowBit r C s
  code_linear := fun _ _ C C' _ =>
    sum_symmDiff_char_two (fun a : ZMod 2 => CharTwo.add_self_eq_zero a) C C' _
  predict := fun j β Jj z =>
    workerPredict N (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y)
      (P.BX N X Y) (P.BY N X Y) (P.c N X Y) j β Jj z
  final := fun j β Jj z =>
    workerFinal N (P.rows X Y) (P.ell N X Y) (P.Nmax N X Y) (P.BX N X Y) (P.BY N X Y) j β Jj z

open Classical in
/-- Definition 5.5: the hint labels are the first `D - Y` coordinates and the outside labels the next
`Y`; a uniform permutation places them uniformly at distinct positions. -/
def refHintLabels (N X Y : ℕ) : Finset ℕ := (range N).filter (· < D N X Y - Y)

open Classical in
/-- The `Y` outside-hint nonzero labels of Definition 5.5. -/
def refOutLabels (N X Y : ℕ) : Finset ℕ :=
  (range N).filter fun i => D N X Y - Y ≤ i ∧ i < D N X Y

/-- `σ_j^*` of the reference placement `π`, Definition 5.5. -/
def sigmaStar (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (j : ℕ) : ℕ :=
  let m := P.rows X Y
  sigma (rowImage N m π j (refHintLabels N X Y)).card (rowLen N m j)
    (rowImage N m π j (refOutLabels N X Y)).card

/-- `Q_s = ∑_j E[G_{s-1}(σ_j^* + c)]`, with the source's `s` written as `s + 1`. -/
def Q (N X Y s : ℕ) : ℝ :=
  expU fun π : Equiv.Perm (Fin N) =>
    ∑ j ∈ range (P.rows X Y), G s ((P.sigmaStar N X Y π j : ℝ) + (P.c N X Y : ℝ))

/-- `X_s = min{Y, ⌈Q_s + 2η(D+1)⌉}`, equation (19). -/
def capX (N X Y s : ℕ) : ℕ :=
  min Y ⌈P.Q N X Y s + 2 * P.eta * ((D N X Y : ℝ) + 1)⌉₊

/-- `Y_s = min{Y, ⌈2^{-c} Q_s + 2η(D+1)⌉}`, equation (19). -/
def capY (N X Y s : ℕ) : ℕ :=
  min Y ⌈((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s + 2 * P.eta * ((D N X Y : ℝ) + 1)⌉₊

open Classical in
/-- All children built, or none. -/
def allSome {α : Type 1} {k : ℕ} (f : Fin k → Option α) : Option (Fin k → α) :=
  if h : ∀ s, (f s).isSome then some fun s => (f s).get (h s) else none

/-- The recursion tree of §5, from the parameter rules. The recursion is not known in advance to be
well founded, so it is run with a fuel; Lemma 5.10 states that a small fuel suffices. -/
def tree : ℕ → ℕ → ℕ → ℕ → Option Node
  | 0, _, _, _ => none
  | fuel + 1, N, X, Y =>
      match P.rule N X Y with
      | .cheap => some (.cr N (D N X Y))
      | .small => some (.cr N (D N X Y))
      | .direct => some (.direct (P.scheme N X Y) (P.resid N X Y))
      | .recursive =>
          (allSome fun s : Fin (P.ell N X Y) =>
              tree fuel Y (P.capX N X Y s.val) (P.capY N X Y s.val)).map fun child =>
            .recursive (P.scheme N X Y) (P.resid N X Y)
              (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child

/-- Standing assumptions on a hinted node (§2.1, Problem 3.1). -/
def NodeArgs (N X Y : ℕ) : Prop :=
  2 ≤ P.n ∧ 1 ≤ P.lam ∧ 1 ≤ N ∧ N ≤ P.n ∧ X ≤ N ∧ Y ≤ N

/-- The two non-leaf rules (the last two cases of §5.2). -/
def NonLeaf (N X Y : ℕ) : Prop := P.rule N X Y = .recursive ∨ P.rule N X Y = .direct

/-- Row `j` is overloaded: `|J_j| > B_X` or `y_j > B_Y`. -/
def Overloaded (N X Y : ℕ) (Jj Sj : Finset ℕ) : Prop :=
  P.BX N X Y < Jj.card ∨ P.BY N X Y < (Sj \ Jj).card

open Classical in
/-- Number of coordinates of `J ∪ supp(x)` in overloaded rows, for the permutation `π`. -/
def overloadedMass (N X Y : ℕ) (π : Equiv.Perm (Fin N)) (x J : Finset ℕ) : ℕ :=
  let m := P.rows X Y
  ∑ j ∈ range m,
    if P.Overloaded N X Y (rowImage N m π j J) (rowImage N m π j x)
    then (rowImage N m π j (J ∪ x)).card else 0

end HintParams

end LinearSetReconciliation327.Main


