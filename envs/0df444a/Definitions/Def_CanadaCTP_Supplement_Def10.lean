-- Prove2me | Definitions.Def_CanadaCTP_Supplement_Def10
-- name    : CanadaCTP_Supplement_Def10
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:36:13.703436+00:00
-- url     : https://prove2.me/theorems/474db381-5b4b-41f2-9dde-c843091fc0d3
-- title:
--   Definition 10 instances and the simple policies of Definition 11
-- statement:
--   **Definition 10.** Given $n\ge1$ integers $u_1,\dots,u_n$ and an integer $R$ with $4\le u_i\le R+1$, let $\delta=\frac1{2R^2}$. For each $i\in[n]$, path $i$ has a first edge of constant weight $c_i=\frac{u_i-1}{u_i+1}$ and a second edge of weight
--   $$X_i=\begin{cases}0&\text{w.p. }1-\frac1{u_i},\\ m_i&\text{w.p. }\frac1{u_i}-\frac1{u_i^2},\\ 3&\text{w.p. }\frac1{u_i^2},\end{cases}\qquad m_i=c_i+1+\delta(u_i+1).$$
--   The **safe path** $0$ has first edge $c_0=\frac32+\delta$ and second edge $X_0=0$. (Lemma 11, $0<m_i<3$, is proved inside the definition, as the support needs three distinct points.)
--
--   **Definition 11.** A **simple policy** fixes a visiting order $\sigma$ of $\{0\}\cup[n]$ and a partition $(S,T)$ of $[n]$. It enters the paths in the order $\sigma$; on path $i$ it walks to the middle vertex and sees $X_i$; it traverses the second edge if $X_i=0$, or if $X_i=m_i$ and $i\in T$, or if $i$ is the safe path; otherwise it walks back to $s$ (paying $c_i$ again) and enters the next path of $\sigma$.
--
--   In $\sigma$, **$S$ precedes $T$** if no path of $T$ is visited before a path of $S$, and **the safe path comes last** if it is $\sigma$'s last path. Finally $\gamma=\prod_{i\in[n]}u_i$ and $\gamma_T=\prod_{i\in T}u_i$.
--
--   These are the instances of the NP-hardness reduction (Theorems 4–6).
--
--   **Formalization Note** The paper's path $i\in[n]$ is `j.succ : Fin (n+1)` for `j : Fin n` (paper index $j+1$); the safe path is `0`. A visiting order is a permutation of `Fin (n+1)` mapping position to path; $S$ is a `Finset (Fin n)` and $T$ its complement. The simple policy is deterministic; its memory is the current position in $\sigma$.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Definition 10, p.21; Lemma 11, p.21 (proof p.40); Definition 11, p.21; Theorems 4 and 5, pp.24–25

import Mathlib
import Definitions.Def_CanadaCTP_Model

namespace CanadaCTP.Supplement

open CanadaCTP

/-! # The instances of Definition 10 and the simple policies of Definition 11

Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Definition 10, p.21; Definition 11, p.21; the visiting-order conditions of Theorems 4 and 5,
pp.24–25; `γ`, `γ_T` of Theorem 5, p.25.

**Formalization Note.** The paper's non-safe paths `i ∈ [n]` are `j : Fin n` (paper index
`j + 1`); in the instance, path `0 : Fin (n + 1)` is the safe path and path `j.succ` is the
paper's path `j + 1`. Every path has two edges, `0` (first) and `1` (second). The integers
`u_i ≥ 4` and `R ≥ u_i − 1 ≥ 3` are natural numbers. -/

/-- The data of Definition 10: `n ≥ 1` integers `u_1, …, u_n` and an integer `R` with
`4 ≤ u_i ≤ R + 1`. -/
structure Def10 where
  n : ℕ
  u : Fin n → ℕ
  R : ℕ
  hn : 1 ≤ n
  hu : ∀ i, 4 ≤ u i ∧ u i ≤ R + 1

namespace Def10

variable (D : Def10)

/-- `δ = 1/(2R²)`. -/
noncomputable def delta : ℝ := 1 / (2 * (D.R : ℝ) ^ 2)

/-- `c_i = (u_i − 1)/(u_i + 1)`, the constant first-edge weight of path `i ∈ [n]`. -/
noncomputable def cval (j : Fin D.n) : ℝ := ((D.u j : ℝ) - 1) / ((D.u j : ℝ) + 1)

/-- `m_i = c_i + 1 + δ·(u_i + 1)`, the medium realization of `X_i`. -/
noncomputable def mval (j : Fin D.n) : ℝ := D.cval j + 1 + D.delta * ((D.u j : ℝ) + 1)

/-- `c_0 = 3/2 + δ`, the first-edge weight of the safe path. -/
noncomputable def c0 : ℝ := 3 / 2 + D.delta

lemma three_le_R : (3 : ℝ) ≤ D.R := by
  have h := D.hu ⟨0, D.hn⟩
  have : 3 ≤ D.R := by omega
  exact_mod_cast this

lemma four_le_u (j : Fin D.n) : (4 : ℝ) ≤ D.u j := by exact_mod_cast (D.hu j).1

lemma delta_nonneg : 0 ≤ D.delta := by unfold delta; positivity

lemma cval_pos (j : Fin D.n) : 0 < D.cval j := by
  have := D.four_le_u j
  unfold cval; apply div_pos <;> linarith

lemma mval_pos (j : Fin D.n) : 0 < D.mval j := by
  have := D.cval_pos j; have := D.delta_nonneg; have := D.four_le_u j
  unfold mval; positivity

/-- Lemma 11 (p.21): `m_i < 3`; needed for the support `{0, m_i, 3}` to have three points. -/
lemma mval_lt_three (j : Fin D.n) : D.mval j < 3 := by
  have hu := D.four_le_u j
  have hR := D.three_le_R
  have hRu : (D.u j : ℝ) ≤ D.R + 1 := by exact_mod_cast (D.hu j).2
  have hc : D.cval j < 1 := by
    unfold cval; rw [div_lt_one (by linarith)]; linarith
  have hd : D.delta * ((D.u j : ℝ) + 1) < 1 := by
    unfold delta
    rw [one_div, inv_mul_lt_iff₀ (by positivity)]
    nlinarith
  unfold mval; linarith

/-- A constant (one-point) edge weight. -/
def constDist (x : ℝ) (hx : 0 ≤ x) : EdgeDist where
  pts := [(x, 1)]
  nodup := by simp
  val_nonneg := by simp [hx]
  prob_pos := by simp
  sum_one := by simp

/-- `X_i`: `0` w.p. `1 − 1/u_i`, `m_i` w.p. `1/u_i − 1/u_i²`, `3` w.p. `1/u_i²`. -/
noncomputable def threePt (j : Fin D.n) : EdgeDist where
  pts := [(0, 1 - 1 / (D.u j : ℝ)), (D.mval j, 1 / (D.u j : ℝ) - 1 / (D.u j : ℝ) ^ 2),
    (3, 1 / (D.u j : ℝ) ^ 2)]
  nodup := by
    have h1 := D.mval_pos j; have h2 := D.mval_lt_three j
    have hne1 : (0 : ℝ) ≠ D.mval j := ne_of_lt h1
    have hne2 : D.mval j ≠ 3 := ne_of_lt h2
    simp [hne1, hne2]
  val_nonneg := by
    have h1 := D.mval_pos j
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp
    linarith
  prob_pos := by
    have hu := D.four_le_u j
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · simp only; rw [sub_pos, div_lt_one (by linarith)]; linarith
    · simp only
      have : 1 / (D.u j : ℝ) - 1 / (D.u j : ℝ) ^ 2 = ((D.u j : ℝ) - 1) / (D.u j : ℝ) ^ 2 := by
        field_simp
      rw [this]; apply div_pos <;> nlinarith
    · simp only; positivity
  sum_one := by simp

/-- The weight distribution of edge `e` of path `i` of the Definition 10 instance. -/
noncomputable def edgeDist (i : Fin (D.n + 1)) (e : Fin 2) : EdgeDist :=
  if h : i = 0 then
    (if e = 0 then constDist D.c0 (by have := D.delta_nonneg; unfold c0; linarith)
     else constDist 0 le_rfl)
  else
    (if e = 0 then constDist (D.cval (i.pred h)) (D.cval_pos _).le else D.threePt (i.pred h))

/-- The instance of Definition 10: `n + 1` paths of two edges; path `0` is the safe path
(`c_0`, then `X_0 = 0`), path `j.succ` is the paper's path `j + 1` (`c_{j+1}`, then `X_{j+1}`). -/
noncomputable def inst : Inst where
  k := D.n + 1
  m := fun _ => 2
  X := fun i e => D.edgeDist i e

/-- Whether a simple policy with non-traversal set `S` traverses the second edge of path `i`
when it sees the realization `x` there (Definition 11): always on the safe path; on path
`j + 1` iff `x = 0`, or `x = m_{j+1}` and `j ∉ S` (i.e. `j ∈ T`). So `3` is never traversed. -/
def Traverses (S : Finset (Fin D.n)) (i : Fin (D.n + 1)) (x : Option ℝ) : Prop :=
  if h : i = 0 then True else
    match x with
    | some x => x = 0 ∨ (x = D.mval (i.pred h) ∧ i.pred h ∉ S)
    | none => True

open Classical in
/-- The move of the simple policy `(σ, S)` (Definition 11). The memory `p` is the position in the
visiting order `σ` (position `p` ↦ path `σ p`) of the path being explored. At `s` it enters path
`σ p`; at the middle vertex of path `i` it sees `X_i` and either traverses the second edge (to
`t`) or walks back to `s` (paying `c_i` again) and moves on to position `p + 1`. -/
noncomputable def simpleMove (σ : Equiv.Perm (Fin (D.n + 1))) (S : Finset (Fin D.n)) (p : ℕ)
    (o : Obs D.inst) : Move D.inst × ℕ :=
  match o.pos with
  | Pos.s => if h : p < D.n + 1 then (Move.fwd (σ ⟨p, h⟩), p) else (Move.stop, p)
  | Pos.t => (Move.wait, p)
  | Pos.mid i _ =>
      if D.Traverses S i (o.rev i ⟨1, by show 1 < 2; decide⟩) then (Move.fwd i, p)
      else (Move.bwd, p + 1)

/-- The **simple policy** with visiting order `σ` and partition `(S, T)`, `T = [n] \ S`
(Definition 11, p.21): a deterministic policy (point-mass steps). It never re-enters a path, always
traverses a `0`, never a `3`, and traverses `m_i` exactly for `i ∈ T`. -/
noncomputable def simplePolicy (σ : Equiv.Perm (Fin (D.n + 1))) (S : Finset (Fin D.n)) :
    Policy D.inst ℕ where
  init := 0
  step p o := PMF.pure (D.simpleMove σ S p o)

/-- Path `i` of the instance is a path of `S`. -/
def InS (S : Finset (Fin D.n)) (i : Fin (D.n + 1)) : Prop := ∃ j : Fin D.n, i = j.succ ∧ j ∈ S

/-- Path `i` of the instance is a path of `T = [n] \ S`. -/
def InT (S : Finset (Fin D.n)) (i : Fin (D.n + 1)) : Prop := ∃ j : Fin D.n, i = j.succ ∧ j ∉ S

/-- "`S` precedes `T`" in the visiting order `σ` (pp.24–25): no path of `T` is visited before a
path of `S`. -/
def SPrecedesT (σ : Equiv.Perm (Fin (D.n + 1))) (S : Finset (Fin D.n)) : Prop :=
  ∀ p q : Fin (D.n + 1), D.InT S (σ p) → D.InS S (σ q) → q < p

/-- "The safe path comes last" in `σ`. -/
def SafeLast (σ : Equiv.Perm (Fin (D.n + 1))) : Prop := σ (Fin.last D.n) = 0

/-- `γ = ∏_{i ∈ [n]} u_i` (Theorem 5). -/
noncomputable def gamma : ℝ := ∏ j, (D.u j : ℝ)

/-- `γ_T = ∏_{i ∈ T} u_i`, `T = [n] \ S` (Theorem 5; empty product `1`). -/
noncomputable def gammaT (S : Finset (Fin D.n)) : ℝ := ∏ j ∈ Sᶜ, (D.u j : ℝ)

end Def10

end CanadaCTP.Supplement


