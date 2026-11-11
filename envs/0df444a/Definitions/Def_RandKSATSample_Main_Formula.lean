-- Prove2me | Definitions.Def_RandKSATSample_Main_Formula
-- name    : RandKSATSample_Main_Formula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:58:27.436692+00:00
-- url     : https://prove2.me/theorems/8844e4a4-26ea-4fce-9e9b-4a74f947923d
-- title:
--   Random k-SAT formulas in the occurrence model, satisfaction, the uniform law µ_Φ on solutions, vbl, deg, I(U) and the primal graph
-- statement:
--   A **$k$-SAT formula** $\Phi$ on the variables $V=\{v_1,\dots,v_n\}$ with $m$ labelled clauses lists, for every clause label $a$ and position $i\in[k]$, a literal $\ell_{a,i}$, i.e. a variable $\mathrm{var}(\ell_{a,i})$ and a sign. In the **occurrence model** $\Phi(k,n,m)$ the $km$ literals are independent and uniform on $\{v_1,\dots,v_n,\neg v_1,\dots,\neg v_n\}$, so all $(2n)^{km}$ formulas are equally likely; repeated variables, tautological clauses and identical clauses under different labels are allowed. For a property $E$ of formulas,
--   $$\Pr_{\Phi\sim\Phi(k,n,m)}[E]=\frac{\#\{\Phi: E(\Phi)\}}{(2n)^{km}}.$$
--   An assignment $\sigma\in\{0,1\}^V$ satisfies clause $a$ if some literal $\ell_{a,i}$ is true at $\sigma$, and satisfies $\Phi$ if it satisfies every clause; $\mu_\Phi$ is the uniform law on the satisfying assignments.
--
--   The structural quantities use syntactic occurrences: $\mathrm{vbl}(a)=\{\mathrm{var}(\ell_{a,i}):i\in[k]\}$, $\mathrm{vbl}(S)=\bigcup_{a\in S}\mathrm{vbl}(a)$, $\deg(v)$ is the number of clause labels containing $v$, $I(U)=|\{a:\mathrm{vbl}(a)\cap U\neq\emptyset\}|$ (2.2), and the primal graph $G_\Phi$ on $V$ joins two distinct variables occurring in a common clause. A variable set $U$ is connected when $G_\Phi[U]$ is connected (in particular nonempty).
--
--   **Formalization Note.** A formula is `Fin m → Fin k → Fin n × Bool` (sign `true` = positive literal); variables are `Fin n`, labels `Fin m`, positions `Fin k`. `muPhi` is the zero function for an unsatisfiable formula. `probF n m k E` is the counting probability above; it is `0/0 = 0` only when the formula space is empty ($n=0<m$, $k\ge1$).
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 5 (§1.1), p. 8 (§2.2), (2.2)

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace RandKSATSample.Main

noncomputable section

open Classical

/-!
# Random k-SAT formulas in the occurrence model

He, Li, Yang, *Fast Almost-Uniform Sampling of Random k-SAT Solutions*, arXiv:2610.10474
(version not printed; file sha256 563a4d84…), p. 5 (§1.1) and p. 8 (§2.2).

A formula with `n` variables, `m` labelled clauses and width `k` lists, for every clause label
`a` and position `i`, the variable and the sign of the literal `ℓ_{a,i}`. Repeated variables,
tautological clauses and identical clauses under different labels are all allowed. The random
formula `Φ(k, n, m)` is the uniform law on this finite type: every one of the `(2n)^{km}` formulas
has the same probability, i.e. the `km` literals are independent and uniform.
-/

/-- A `k`-SAT formula on the variables `Fin n` with `m` labelled clauses (occurrence model): the
literal at position `i` of clause `a` is `Φ a i = (variable, sign)`, where sign `true` is the
positive literal `v` and `false` the negative literal `¬v`. -/
abbrev Formula (n m k : ℕ) : Type := Fin m → Fin k → Fin n × Bool

/-- A truth assignment to the variables `Fin n`. -/
abbrev Assignment (n : ℕ) : Type := Fin n → Bool

variable {n m k : ℕ}

/-- The assignment `σ` satisfies clause `a`: some literal of `a` is true at `σ`. -/
def ClauseSat (Φ : Formula n m k) (σ : Assignment n) (a : Fin m) : Prop :=
  ∃ i : Fin k, σ (Φ a i).1 = (Φ a i).2

/-- The assignment `σ` satisfies the formula `Φ`: it satisfies every clause. -/
def Sat (Φ : Formula n m k) (σ : Assignment n) : Prop := ∀ a : Fin m, ClauseSat Φ σ a

/-- The satisfying assignments of `Φ`. -/
def solutions (Φ : Formula n m k) : Finset (Assignment n) := Finset.univ.filter (Sat Φ)

/-- The uniform law `µ_Φ` on the satisfying assignments of `Φ` (the zero function when `Φ` is
unsatisfiable). -/
def muPhi (Φ : Formula n m k) (σ : Assignment n) : ℝ :=
  if Sat Φ σ then 1 / ((solutions Φ).card : ℝ) else 0

/-- The probability of a property of formulas under the random formula `Φ(k, n, m)`: the
fraction of the `(2n)^{km}` formulas that have it. -/
def probF (n m k : ℕ) (E : Formula n m k → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card (Formula n m k) : ℝ)

/-- The variable set `vbl(a)` of clause `a`: the variables occurring in it, regardless of sign. -/
def vbl (Φ : Formula n m k) (a : Fin m) : Finset (Fin n) :=
  Finset.univ.image fun i : Fin k => (Φ a i).1

/-- `vbl(S) = ⋃_{a ∈ S} vbl(a)` for a set `S` of clause labels. -/
def vblSet (Φ : Formula n m k) (S : Finset (Fin m)) : Finset (Fin n) := S.biUnion (vbl Φ)

/-- The degree `deg(v)`: the number of clause labels containing `v`. -/
def deg (Φ : Formula n m k) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun a : Fin m => v ∈ vbl Φ a).card

/-- `I(U)`, the number of clause labels meeting the variable set `U` (2.2). -/
def incident (Φ : Formula n m k) (U : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun a : Fin m => (vbl Φ a ∩ U).Nonempty).card

/-- The primal graph `G_Φ`: two distinct variables are adjacent when they occur in a common
clause. -/
def primalGraph (Φ : Formula n m k) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ a : Fin m, u ∈ vbl Φ a ∧ v ∈ vbl Φ a

/-- A vertex set `U` of a graph `G` is connected: the induced graph `G[U]` is connected (in
particular `U` is nonempty). -/
def IsConnectedSet {V : Type} (G : SimpleGraph V) (U : Finset V) : Prop :=
  (G.induce (U : Set V)).Connected

end

end RandKSATSample.Main


