-- Prove2me | Definitions.Def_SingleMachinePrec_VariableCost_Supplement_LexSum
-- name    : SingleMachinePrec_VariableCost_Supplement_LexSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:47:05.683858+00:00
-- url     : https://prove2.me/theorems/bca319e0-616e-4599-aa64-0998948680ba
-- title:
--   Efficiently samplable realizers and lexicographic sums of posets
-- statement:
--   A poset is given to an algorithm by its number of elements $m$ (in unary) and its $m\times m$ relation matrix.
--
--   **Efficiently samplable realizers** (§5, p. 658). A poset admits an efficiently samplable $k:t$-realizer if a randomized algorithm, in time polynomial in the size of the poset, returns each member of a $k$-fold realizer $\mathcal F=\{L_1,\dots,L_t\}$ with probability $1/t$. For a class $\mathcal C$ of posets this is formalized as a **family**: functions $t,k$ and a finite multiset of members, together with one polynomial-time randomized sampler for all posets in the class. A machine computes a positive seed range $N$; another machine maps a uniform seed to an extension. The output distribution is exactly uniform over multiset occurrences: the probability of a distinct extension is its multiplicity divided by $t$. Neither $t$ nor an indexed member must be computable. For every poset in the class the multiset is a positive-multiplicity $k$-fold realizer, and its members are permutations giving linear extensions. The ratio of $Q$ is $t(Q)/k(Q)$.
--
--   **Lexicographic sums** (§6.4, p. 661). For a poset $(N,P)$ and posets $(Y_x,Q_x)$, $x\in N$, the lexicographic sum is the poset $(Z,R)$ with $Z=\{(x,y):x\in N,\ y\in Y_x\}$ and $(x_1,y_1)\le(x_2,y_2)$ in $R$ iff either $x_1<x_2$ in $P$, or $x_1=x_2$ and $y_1\le y_2$ in $Q_{x_1}$. Its **components** are $\mathcal P=\{P\}\cup\{Q_x\}$. The input of Theorem 6.5 consists of $(N,P)$, the modules $(Y_x,Q_x)$ and integer processing times and weights of the jobs $(x,y)$; the jobs are numbered block by block, and for a family as above
--   $$\frac tk=\max_{i\in\mathcal P}\frac{t_i}{k_i}.$$
--
--   These are the hypotheses and the ratio of Theorem 6.5.
--
--   **Formalization Note** The two cases (i), (ii) of the printed definition are alternatives (Mathlib's `Sigma.Lex`), as "one of the following two statements holds" says. Members of a realizer are processing orders whose order relation is the published `LinearExtension`; repetitions are allowed. The input code is the code of the flattened scheduling instance, then the outer poset, then every module.
--
--   A sum is trivial if the outer poset has one point or every module has one point, as on p. 661.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 658, §5 (efficiently samplable k:t-realizer); p. 661, §6.4 (lexicographic sum, components 𝓟, Theorem 6.5's t/k)

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_Supplement_OrderClasses

set_option autoImplicit false

namespace SingleMachinePrec.VariableCost.Supplement

open QAlgorithms.Complexity

/-! ### Posets as inputs -/

/-- A finite relation as an algorithm receives it: `m` elements and the `m × m` Boolean
matrix of the relation. -/
structure PosetCode where
  m : ℕ
  rel : Fin m → Fin m → Bool

namespace PosetCode

/-- The relation, as a proposition. -/
def Rel (Q : PosetCode) (i j : Fin Q.m) : Prop := Q.rel i j = true

/-- Code: `m` in unary, then the matrix row by row. -/
def enc (Q : PosetCode) : Str :=
  encNat Q.m ++ (List.finRange Q.m).flatMap (fun i => (List.finRange Q.m).map (fun j => Q.rel i j))

end PosetCode

/-! ### Efficiently samplable realizers (§5, p. 658) -/

/-- A family of efficiently samplable realizers for a class `Cls` of posets: for every poset `Q`
of the class, a size `t Q`, a multiplicity `k Q`, and the members `ext Q s` (`s < t Q`) of a
multiset of linear extensions, each given as a processing order. -/
structure SamplableRealizers where
  Cls : PosetCode → Prop
  t : PosetCode → ℕ
  k : PosetCode → ℕ
  ext : (Q : PosetCode) → ℕ → List (Fin Q.m)

open Classical in
/-- Uniform sampling from the multiset in polynomial time. `R` computes a seed range `N`,
not the realizer size `t`. `A` returns a member for every seed. The counting identity says
that each distinct output has probability equal to its multiplicity divided by `t`.
There is no requirement to enumerate the realizer or compute its size. -/
def SamplableRealizers.Valid (F : SamplableRealizers) : Prop :=
  (∃ R A : Str → Str, PolyTimeComputable R ∧ PolyTimeComputable A ∧
    ∀ Q, F.Cls Q → ∃ N : ℕ, 0 < N ∧ R Q.enc = encBin N ∧
      (∀ s < N, ∃ i < F.t Q, A (Q.enc ++ encBin s) = encSchedule (F.ext Q i)) ∧
      ∀ i < F.t Q,
        ((Finset.range N).filter
          (fun s => A (Q.enc ++ encBin s) = encSchedule (F.ext Q i))).card * F.t Q =
        N * ((Finset.range (F.t Q)).filter (fun j => F.ext Q j = F.ext Q i)).card) ∧
  ∀ Q, F.Cls Q → IsPartialOrder (Fin Q.m) Q.Rel ∧ 0 < F.k Q ∧
    (∀ s < F.t Q, IsPerm (F.ext Q s)) ∧
    ∃ L : Fin (F.t Q) → SingleMachinePrec.Framework.LinearExtension Q.Rel,
      SingleMachinePrec.Framework.IsKFoldRealizer Q.Rel (F.k Q) (F.t Q) L ∧
      ∀ s : Fin (F.t Q), (L s).le = listLe (F.ext Q s.val)

/-- The ratio `t/k` of the family's realizer of `Q`. -/
noncomputable def SamplableRealizers.ratio (F : SamplableRealizers) (Q : PosetCode) : ℝ :=
  (F.t Q : ℝ) / (F.k Q : ℝ)

/-! ### Lexicographic sums (§6.4, p. 661) -/

/-- Input of Theorem 6.5: an outer poset `(N, P)` on `Fin outer.m`, a module `(Y_x, Q_x)` for
every `x`, and integer processing times and weights of the jobs `(x, y)`, `y ∈ Y_x`. -/
structure LexSumInput where
  outer : PosetCode
  comp : Fin outer.m → PosetCode
  p : (Σ x : Fin outer.m, Fin (comp x).m) → ℕ
  w : (Σ x : Fin outer.m, Fin (comp x).m) → ℕ

namespace LexSumInput

/-- The lexicographic sum order on `Z = {(x, y) : x ∈ N, y ∈ Y_x}` (p. 661):
`(x₁, y₁) ≤ (x₂, y₂)` iff `x₁ < x₂` in `P`, or `x₁ = x₂` and `y₁ ≤ y₂` in `Q_{x₁}`. -/
def lexRel (L : LexSumInput) : (Σ x : Fin L.outer.m, Fin (L.comp x).m) →
    (Σ x : Fin L.outer.m, Fin (L.comp x).m) → Prop :=
  Sigma.Lex (fun x₁ x₂ => L.outer.Rel x₁ x₂ ∧ x₁ ≠ x₂) (fun x => (L.comp x).Rel)

/-- The jobs `(x, y)`, numbered block by block (`finSigmaFinEquiv`). -/
abbrev numJobs (L : LexSumInput) : ℕ := ∑ x : Fin L.outer.m, (L.comp x).m

open Classical in
/-- The scheduling instance of the lexicographic sum, with job `(x, y)` numbered
`finSigmaFinEquiv (x, y)`. -/
noncomputable def toSched (L : LexSumInput) : SchedInput where
  n := L.numJobs
  p := fun j => L.p (finSigmaFinEquiv.symm j)
  w := fun j => L.w (finSigmaFinEquiv.symm j)
  prec := fun i j => decide (L.lexRel (finSigmaFinEquiv.symm i) (finSigmaFinEquiv.symm j))

/-- The components `𝓟 = {P} ∪ S` of the sum: the outer poset and every module. -/
def components (L : LexSumInput) : List PosetCode :=
  L.outer :: (List.finRange L.outer.m).map L.comp

/-- A trivial sum (§6.4): the outer poset has one element, or every module has one element. -/
def IsTrivial (L : LexSumInput) : Prop :=
  L.outer.m = 1 ∨ ∀ x, (L.comp x).m = 1

/-- Input code: the scheduling instance, then the outer poset, then every module. -/
noncomputable def enc (L : LexSumInput) : Str :=
  L.toSched.enc ++ L.outer.enc ++ (List.finRange L.outer.m).flatMap (fun x => (L.comp x).enc)

/-- `t/k = max_{i ∈ 𝓟} t_i / k_i` (Theorem 6.5, p. 661), over the outer poset and all modules. -/
noncomputable def maxRatio (F : SamplableRealizers) (L : LexSumInput) : ℝ :=
  (L.components.map F.ratio).foldr max (F.ratio L.outer)

end LexSumInput

end SingleMachinePrec.VariableCost.Supplement


