-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_TopLevel
-- name    : LinearSetReconciliation327_Main_TopLevel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:26.387913+00:00
-- url     : https://prove2.me/theorems/a5b65823-25eb-4358-8b9b-daadbd08ff10
-- title:
--   §§3.2, 6.2 — top-layer parameters, Pinsketch row code, Algorithm 2, capacities
-- statement:
--   For $n,d$ and constants $A,C'$: $N=\lceil n/d\rceil$, $w=\lceil\log(N+1)\rceil$, $B=\min\{N,\lceil C'\log(\log n+2)\rceil\}$, $\ell=Bw$, $\eta=\log^{-A}n$, $\lambda_*=\lambda+C'\lceil\log\log(n+2)\rceil+C'$. The row-column regime excludes $d\ge n/2$ and $d\le(C')^3\lambda_*\log^6n/\eta^2$. Reference loads place $d$ labels at distinct positions and give $q_a=\sum_j\Pr[T_j\ge a]$; $p_k=2^{w-k}/(2^w-1)$; equation (28) gives $X_{a,k},Y_{a,k}$ and (31) gives $t$. The row code is bit $k$ of $\alpha_{j,a}P_{2a-1}(S)$ in a fixed basis with independent uniform nonzero scalars. `cand` removes the scalars from the first words and finds a set in the actual row of size at most the number of words with these odd power sums, or none. `predictTop` is Algorithm 2 with the first-mismatch abort, retried at each word boundary, and the final estimate is the candidate of all $B$ words, or $\emptyset$.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), §3.2 and §6.2, PDF p.13–14, 28–30 (printed p.12–13, 27–29)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Framework

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! The top layer: §3.2 (PDF pp.13–14) with the parameters of §6.2 (PDF pp.28–30). -/

/-- Global parameters: the constants `A, C'`, the universe `n`, the sparsity `d`, and `λ`. -/
structure TopParams where
  A : ℕ
  C' : ℕ
  n : ℕ
  d : ℕ
  lam : ℕ

namespace TopParams

variable (P : TopParams)

/-- `log n`. -/
def lgn : ℝ := lg P.n
/-- `η = log^{-A} n`. -/
def eta : ℝ := (P.lgn ^ P.A)⁻¹
/-- `λ_* = λ + C'⌈log log(n+2)⌉ + C'`. -/
def lamStar : ℕ := P.lam + P.C' * ⌈lg (lg ((P.n : ℝ) + 2))⌉₊ + P.C'
/-- `N = ⌈n/d⌉`. -/
def N : ℕ := ⌈(P.n : ℝ) / (P.d : ℝ)⌉₊
/-- `w = ⌈log(N+1)⌉`. -/
def w : ℕ := ⌈lg ((P.N : ℝ) + 1)⌉₊
/-- `B = min{N, ⌈C' log(log n + 2)⌉}`. -/
def B : ℕ := min P.N ⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊
/-- `ℓ = Bw`. -/
def ell : ℕ := P.B * P.w

/-- The row-column regime of §6.2: neither `d ≥ n/2` nor `d ≤ (C')³λ_* log⁶ n / η²`. -/
def RowColumnRegime : Prop :=
  (P.d : ℝ) < (P.n : ℝ) / 2 ∧
    (P.C' : ℝ) ^ 3 * P.lamStar * P.lgn ^ 6 / P.eta ^ 2 < (P.d : ℝ)

/-- Standing assumptions of §2.1, with `λ ≥ 1`. -/
def Args : Prop := 2 ≤ P.d ∧ P.d ≤ P.n ∧ 1 ≤ P.lam

/-- `T_j`: labels `0, …, d-1` placed at distinct positions by `π`, counted in row `j`. -/
def refLoad (π : Equiv.Perm (Fin P.n)) (j : ℕ) : ℕ :=
  (rowImage P.n P.d π j (range P.d)).card

/-- `q_a = ∑_j Pr[T_j ≥ a]`, Lemma 6.1. -/
def q (a : ℕ) : ℝ :=
  ∑ j ∈ range P.d, prU fun π : Equiv.Perm (Fin P.n) => a ≤ P.refLoad π j

/-- `p_k = 2^{w-k}/(2^w-1)`, equation (27), with the source's `k` written as `k + 1`, `k < w`. -/
def p (k : ℕ) : ℝ := (2 : ℝ) ^ (P.w - (k + 1)) / ((2 : ℝ) ^ P.w - 1)

/-- `X_{a,k} = min{d, ⌈q_a + η(d+1)⌉}`, equation (28). Source indices are `a + 1`, `k + 1`. -/
def capX (a : ℕ) : ℕ := min P.d ⌈P.q (a + 1) + P.eta * ((P.d : ℝ) + 1)⌉₊

/-- `Y_{a,k} = min{d, ⌈q_a p_k + η(d+1)⌉}`, equation (28). Source indices are `a + 1`, `k + 1`. -/
def capY (a k : ℕ) : ℕ := min P.d ⌈P.q (a + 1) * P.p k + P.eta * ((P.d : ℝ) + 1)⌉₊

/-- `t = min{n, d(B+1), ⌈2η(d+1)⌉}`, equation (31). -/
def resid : ℕ := min P.n (min (P.d * (P.B + 1)) ⌈2 * P.eta * ((P.d : ℝ) + 1)⌉₊)

variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- `ι : [N] ↪ F*`: an injection of the row addresses into the nonzero field elements. -/
def IsAddress (ι : ℕ → F) : Prop :=
  (∀ v < P.N, ι v ≠ 0) ∧ Set.InjOn ι (Set.Iio P.N)

/-- `P_a(S) = ∑_{v∈S} ι(v)^a`. -/
def power (ι : ℕ → F) (a : ℕ) (S : Finset ℕ) : F := ∑ v ∈ S, ι v ^ a

/-- A column `s` of the source is word `s / w`. -/
def wordIdx (s : Fin P.ell) : Fin P.B :=
  ⟨s.val / P.w, Nat.div_lt_of_lt_mul (by
    have := s.isLt; unfold ell at this; rw [Nat.mul_comm]; exact this)⟩

/-- A column `s` of the source is bit `s % w` of its word. -/
def bitIdx (s : Fin P.ell) : Fin P.w :=
  ⟨s.val % P.w, Nat.mod_lt _ (by
    have := s.isLt; unfold ell at this
    exact Nat.pos_of_ne_zero fun h => by simp [h] at this)⟩

/-- The word of a row prefix `z`: bits `aw, …, aw + w - 1` read in the fixed basis `b`. -/
def wordOf (b : Module.Basis (Fin P.w) (ZMod 2) F) (z : List (ZMod 2)) (a : ℕ) : F :=
  ∑ k : Fin P.w, (z.getD (a * P.w + k.val) 0) • b k

open Classical in
/-- `Cand_j(i)`: removes the public scalars from the first `i` recovered words and looks for a set in
the actual row `[N_j]` of size at most `i` with these odd power sums. By the Pinsketch property it is
unique when it exists. `Cand_j(0) = ∅`. -/
def cand (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (j : ℕ) (α : Fin P.B → Fˣ)
    (z : List (ZMod 2)) (i : ℕ) : Option (Finset ℕ) :=
  (((range (rowLen P.n P.d j)).powerset.filter fun S =>
      S.card ≤ i ∧ ∀ a : Fin P.B, a.val < i →
        power ι (2 * a.val + 1) S = ((α a)⁻¹ : Fˣ) * wordOf P b z a.val).toList).head?

open Classical in
/-- Algorithm 2, one prediction at prefix length `|z| = aw + k`: use the candidate of the first `a`
words; abstain if there is none, or if an earlier bit of this word disagreed with the recovered bit
(first-mismatch abort, retried at the next word boundary). -/
def predictTop (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (j : ℕ) (α : Fin P.B → Fˣ)
    (z : List (ZMod 2)) : Option (ZMod 2) :=
  if h : z.length < P.ell then
    let s : Fin P.ell := ⟨z.length, h⟩
    let a := P.wordIdx s
    let k := P.bitIdx s
    (P.cand b ι j α z a.val).bind fun C =>
      let bits := b.repr ((α a : F) * power ι (2 * a.val + 1) C)
      if ∀ k' : Fin P.w, k'.val < k.val → bits k' = z.getD (a.val * P.w + k'.val) 0
      then some (bits k) else none
  else none

open Classical in
/-- The row scheme of the top layer: `Rand` holds the scalars `α_{j,a}` of a row. The row code
is bit `k` of `α_{j,a} P_{2a-1}(S)`, with the source's `a` written as `a + 1`. -/
def scheme (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) : RowScheme where
  N := P.n
  m := P.d
  ℓ := P.ell
  Rand := Fin P.B → Fˣ
  code := fun _ α S s =>
    b.repr ((α (P.wordIdx s) : F) * power ι (2 * (P.wordIdx s).val + 1) S) (P.bitIdx s)
  code_linear := fun _ α C C' s => by
    have h2 : ∀ a : F, a + a = 0 := fun a => by
      have h : (2 : F) = 0 := by
        have e : algebraMap (ZMod 2) F 2 = (2 : F) := map_ofNat _ 2
        rw [← e, show (2 : ZMod 2) = 0 from rfl, map_zero]
      rw [← two_mul, h, zero_mul]
    have : power ι (2 * (P.wordIdx s).val + 1) (symmDiff C C') =
        power ι (2 * (P.wordIdx s).val + 1) C + power ι (2 * (P.wordIdx s).val + 1) C' :=
      sum_symmDiff_char_two h2 C C' _
    rw [this, mul_add, map_add]
    rfl
  predict := fun j α _ z => P.predictTop b ι j.val α z
  final := fun j α _ z => (P.cand b ι j.val α z P.B).getD ∅

end TopParams

end LinearSetReconciliation327.Main


