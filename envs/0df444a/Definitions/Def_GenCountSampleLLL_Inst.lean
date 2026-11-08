-- Prove2me | Definitions.Def_GenCountSampleLLL_Inst
-- name    : GenCountSampleLLL_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:39:32.396555+00:00
-- url     : https://prove2.me/theorems/51e82a77-428a-4d0f-a1ba-c486068e9efe
-- title:
--   CSP in the variable setting: $\nu$, $\mathrm{Good}(\mathcal D)$, $Z_{\mathcal D}$, $\mu_{\mathcal D}$, $p_a$, $r_{\mathcal D,a}$, $G$, $N^2_G(a)$, condition (1.1)
-- statement:
--   Let $(X_v)_{v\in V}$ be a finite family of independent random variables, where $X_v$ has law $\nu_v$ with finite support $\Omega_v$; write $\Omega=\prod_v\Omega_v$ and $\nu=\bigotimes_v\nu_v$. A finite family $\mathcal C$ of constraints is given; constraint $a$ has a variable set $\mathrm{vbl}(a)\subseteq V$ and a set of forbidden assignments to those variables. $B_a$ is the event that $a$ is violated and $p_a=\nu(B_a)$.
--
--   For $\mathcal D\subseteq\mathcal C$, $\mathrm{Good}(\mathcal D)$ is the set of assignments satisfying every constraint of $\mathcal D$, $Z_{\mathcal D}=\nu(\mathrm{Good}(\mathcal D))$, $\mu_{\mathcal D}=\nu(\cdot\mid\mathrm{Good}(\mathcal D))$, and for $a\in\mathcal D$, $r_{\mathcal D,a}=\mu_{\mathcal D^-}(B_a)$ with $\mathcal D^-=\mathcal D\setminus\{a\}$.
--
--   The dependency graph $G$ on $\mathcal C$ joins two distinct constraints sharing a variable; $N^2_G(a)$ is the set of constraints $b\neq a$ at distance one or two from $a$, and $N^2_G[t]=\{t\}\cup N^2_G(t)$. Condition (1.1) with constant $c$ and witness $x$ is
--   $$
--   p_a\le c\,x_a\prod_{b\in N^2_G(a)}(1-x_b)\qquad(a\in\mathcal C).
--   $$
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Variables are `Fin n`, constraints `Fin m` (their order is the fixed ordering $a_1,\dots,a_m$ of p.7), and $\Omega_v$ is relabelled $\{0,\dots,q_v-1\}$ with every value of positive mass, since $\Omega_v$ is the support of $\nu_v$. The laws are arbitrary real probability vectors. Any variable sets and forbidden sets are allowed. $\mu_{\mathcal D}$ is $\nu(\sigma)/Z_{\mathcal D}$ on $\mathrm{Good}(\mathcal D)$ and $0$ elsewhere; the range $x\in(0,1)^{\mathcal C}$ is stated separately wherever (1.1) is assumed. The module also contains the product of finitely many laws (`piLaw`), used for the experiments of the paper.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), §1, p.1; §1.1, p.2; §2, p.7

import Mathlib

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

noncomputable section

open Classical

/-- The product of finitely many probability mass functions on finite types: the law of an
independent family `(f i)_i` with `f i ∼ μ i`. -/
def piLaw {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)] (μ : ∀ i, PMF (κ i)) :
    PMF (∀ i, κ i) :=
  PMF.ofFintype (fun f => ∏ i, μ i (f i)) (by
    have h : ∀ i, ∑ j, μ i j = 1 := fun i => by
      rw [← (μ i).tsum_coe, tsum_fintype]
    rw [← Fintype.prod_sum]
    simp [h])

/-- A constraint satisfaction problem in the variable setting (Jain, Mizgerd, Pham, *A general
counting and sampling Lovász local lemma*, arXiv:2609.23671, held file sha256 cd449f83…, §1, p.1).

There are `n` independent variables `X_v` (`v : Fin n`); `X_v` has law `ν v` on its finite
support `Ω_v = Fin (q v)`. There are `m` constraints (`a : Fin m`); constraint `a` has the
variable set `vbl a` and the set `forb a` of forbidden assignments to those variables.

**Formalization Note.** `Ω_v` is the support of `ν_v` (p.1: "`X_v` has law `ν_v` with finite
support `Ω_v`"), so every value of `Fin (q v)` has positive mass (`ν_pos`); the values of `Ω_v`
are relabelled `0, …, q v − 1`. The laws are arbitrary real probability vectors. Any
variable sets (empty ones included) and any forbidden sets (empty or full) are allowed. The
ordering `a₁, …, a_m` of p.7 is the order of `Fin m`. -/
structure Inst where
  /-- The number of variables. -/
  n : ℕ
  /-- The number of constraints, `m = |C|`. -/
  m : ℕ
  /-- The domain size `|Ω_v|`. -/
  q : Fin n → ℕ
  /-- The coordinate law `ν_v` on `Ω_v = Fin (q v)`. -/
  ν : (v : Fin n) → PMF (Fin (q v))
  /-- `Ω_v` is the support of `ν_v`. -/
  ν_pos : ∀ v x, ν v x ≠ 0
  /-- The variable set `vbl(a) ⊆ V`. -/
  vbl : Fin m → Finset (Fin n)
  /-- The forbidden assignments of constraint `a` to its variables. -/
  forb : (a : Fin m) → Set ((v : {v // v ∈ vbl a}) → Fin (q v.1))

namespace Inst

variable (I : Inst)

/-- Every domain is nonempty (a law on `Fin (q v)` exists). -/
theorem q_pos (v : Fin I.n) : 0 < I.q v := (I.ν v).support_nonempty.choose.pos

/-- An assignment `σ ∈ Ω = ∏_v Ω_v`. -/
abbrev Assign : Type := (v : Fin I.n) → Fin (I.q v)

/-- `σ ∈ B_a`: the bad event that constraint `a` is violated, i.e. the restriction of `σ` to
`vbl(a)` is forbidden. -/
def bad (a : Fin I.m) (σ : I.Assign) : Prop :=
  (fun v : {v // v ∈ I.vbl a} => σ v.1) ∈ I.forb a

/-- `ν(σ) = ∏_v ν_v(σ_v)`, the product law `ν = ⊗_v ν_v` at an assignment, as a real. -/
def nuA (σ : I.Assign) : ℝ := ∏ v, (I.ν v (σ v)).toReal

/-- `ν_U(z) = ∏_{v ∈ U} ν_v(z_v)`, the law `ν_U = ⊗_{v∈U} ν_v` at the restriction of `z` to
`U` (p.1). -/
def nuU (U : Finset (Fin I.n)) (z : I.Assign) : ℝ := ∏ v ∈ U, (I.ν v (z v)).toReal

/-- The product law `ν` on `Ω`, as a probability mass function. -/
def prodLaw : PMF I.Assign := piLaw I.ν

/-- The restriction of `σ` to `U`, normalized to the value `0` outside `U`: the representation
of an element of `Ω_U` used throughout. -/
def restr (U : Finset (Fin I.n)) (σ : I.Assign) : I.Assign :=
  fun v => if v ∈ U then σ v else ⟨0, I.q_pos v⟩

/-- The assignment equal to `τ` on `U` and to `σ` outside `U`: `(y, u)` with `u = τ|_U` and
`y = σ|_{V∖U}`. -/
def merge (U : Finset (Fin I.n)) (τ σ : I.Assign) : I.Assign :=
  fun v => if v ∈ U then τ v else σ v

/-- `Good(D)`, the assignments satisfying every constraint in `D` (p.2). -/
def Good (D : Finset (Fin I.m)) : Finset I.Assign :=
  Finset.univ.filter fun σ => ∀ a ∈ D, ¬ I.bad a σ

/-- `Z_D = ν(Good(D))` (p.2). -/
def Z (D : Finset (Fin I.m)) : ℝ := ∑ σ ∈ I.Good D, I.nuA σ

/-- `µ_D = ν(· | Good(D))` as a function on `Ω` (p.2): `ν(σ)/Z_D` on `Good(D)` and `0`
elsewhere. Every statement using it has or proves `Z_D > 0`. -/
def mu (D : Finset (Fin I.m)) (σ : I.Assign) : ℝ :=
  if σ ∈ I.Good D then I.nuA σ / I.Z D else 0

/-- `p_a = ν(B_a)` (p.1). -/
def p (a : Fin I.m) : ℝ := ∑ σ ∈ Finset.univ.filter (I.bad a), I.nuA σ

/-- `r_{D,a} = µ_{D⁻}(B_a)`, with `D⁻ = D ∖ {a}` (§2, p.7). -/
def r (D : Finset (Fin I.m)) (a : Fin I.m) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (I.bad a), I.mu (D.erase a) σ

/-- The dependency graph `G` on `C`: distinct constraints are adjacent iff they share a
variable (p.1). -/
def G : SimpleGraph (Fin I.m) where
  Adj a b := a ≠ b ∧ (I.vbl a ∩ I.vbl b).Nonempty
  symm := { symm := fun a b h => ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩ }
  loopless := { irrefl := fun a h => h.1 rfl }

/-- `N²_G(a)`, the neighbours of `a` in `G²` (p.2): the constraints `b ≠ a` at distance one or
two from `a` in `G`. This neighbourhood is open (`a ∉ N²_G(a)`). -/
def N2G (a : Fin I.m) : Finset (Fin I.m) :=
  Finset.univ.filter fun b => b ≠ a ∧ (I.G.Adj a b ∨ ∃ c, I.G.Adj a c ∧ I.G.Adj c b)

/-- `N²_G[t] = {t} ∪ N²_G(t)`, the closed distance-two neighbourhood in `G` (p.13). -/
def N2Gc (t : Fin I.m) : Finset (Fin I.m) := insert t (I.N2G t)

/-- Condition (1.1) with constant `c` and witness `x` (Theorem 1.1, p.2):
`p_a ≤ c x_a ∏_{b ∈ N²_G(a)} (1 − x_b)` for every `a ∈ C`. The range `x ∈ (0,1)^C` is stated
separately wherever the condition is assumed. -/
def LLLCond (c : ℝ) (x : Fin I.m → ℝ) : Prop :=
  ∀ a, I.p a ≤ c * x a * ∏ b ∈ I.N2G a, (1 - x b)

end Inst

end

end GenCountSampleLLL


