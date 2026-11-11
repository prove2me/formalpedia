-- Prove2me | Definitions.Def_RandKSATSample_Main_Structure
-- name    : RandKSATSample_Main_Structure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:59:08.949218+00:00
-- url     : https://prove2.me/theorems/e913864f-8a7a-4ff0-bb37-807ffa5bd5e1
-- title:
--   Parameters (3.1) and §3.4, the high-degree core V_bad, components B_i, the good formula Ψ, ν_good, Z_F, µ_F, q_S, CS_Ψ(a), the events of Lemmas 3.1–3.3 and nice formulas (Condition 3.12)
-- statement:
--   **Parameters** (3.1) and §3.4, as functions of $(n,m,k)$: $\lambda=1+m/n$, $\Delta=6k^7\lambda$, $C_{\mathrm{INC}}=100k^2\lambda$, $D=\lceil 6k^8\lambda\rceil+1$, $n_0=e^{k-3}\lambda(k-4)^4$, $q_0=(4n_0)^{-1/3}$, $r=\lfloor q_0 n\rfloor$, $p_*=2^{-k+12}$, $C_*=10^4$, $\tau=\ln\frac1{C_*p_*D}$, $x=e\,p_*$, $\rho=\frac4{C_*D}$.
--
--   **The core.** $V_{\mathrm{high}}=\{v:\deg(v)\ge\Delta\}$. $\mathrm{Core}(S)$ starts from $S$ and repeatedly adds all variables of a clause containing more than $8$ distinct variables of the current set; $V_{\mathrm{bad}}=\mathrm{Core}(V_{\mathrm{high}})$, $V_{\mathrm{good}}=V\setminus V_{\mathrm{bad}}$, and $B_1,\dots,B_s$ are the vertex sets of the connected components of $G_\Phi[V_{\mathrm{bad}}]$. A clause is a **core clause** if $\mathrm{vbl}(a)\subseteq V_{\mathrm{bad}}$; $\mathcal C^{\mathrm{good}}$ is the set of the other labels. $\Omega_i$ is the set of assignments of $B_i$ satisfying all core clauses meeting $B_i$; $\Omega$ is the set of assignments of $V_{\mathrm{bad}}$ satisfying all core clauses; $D_\sigma$ is the set of good labels whose bad-variable literals are all false at $\sigma$.
--
--   **The good formula.** $C^{\mathrm{good}}_a$ is the disjunction of the literals of $C_a$ on good variables, $\Psi[F]=\bigwedge_{a\in F}C_a^{\mathrm{good}}$, $E_a$ the event that $C^{\mathrm{good}}_a$ is violated, $\mathrm{Good}(F)$ the event that every $C_a^{\mathrm{good}}$, $a\in F$, holds. Under the uniform measure $\nu_{\mathrm{good}}$ on $\{0,1\}^{V_{\mathrm{good}}}$:
--   $$Z_F=\nu_{\mathrm{good}}(\mathrm{Good}(F)),\qquad \mu_F(A)=\frac{\nu_{\mathrm{good}}(A\cap\mathrm{Good}(F))}{Z_F},\qquad q_S=\nu_{\mathrm{good}}\Big(\bigcap_{a\in S}E_a\Big).$$
--   $H_\Psi$ is the graph on $\mathcal C^{\mathrm{good}}$ joining two distinct labels that share a good variable, $N_{H_\Psi}[a]$ its closed neighbourhood, and $\mathsf{CS}_\Psi(a)$ the nonempty connected vertex sets of $H_\Psi$ containing $a$. The **polymer-root estimate** is $\sum_{S\in\mathsf{CS}_\Psi(a)}q_Se^{(1+\tau)|S|}\le\rho$ for every $a\in\mathcal C^{\mathrm{good}}$.
--
--   **Events.** Lemma 3.1: every set $S$ of at most $r$ clauses has $|\mathrm{vbl}(S)|\ge(k-4)|S|$. Lemma 3.2: every connected $U$ has $I(U)<C_{\mathrm{INC}}|U|+4\ln n$. Lemma 3.3: $|V_{\mathrm{high}}|\le r$. Their conjunction is the **joint event of Lemmas 3.1 to 3.3**. A formula is **nice** (Condition 3.12) if $k\ge2^{20}$, $m/n\le 2^k/k^{16}$, $r\ge\max\{1,\lceil\log_2n\rceil\}$, the joint event holds and the polymer-root estimate holds.
--
--   **Formalization Note.** $\mathrm{Core}(S)$ is defined as the least superset of $S$ closed under the rule; the repeated-addition process is monotone, so it produces exactly this set in any order. Components are the reachability classes of $G_\Phi$ restricted to edges inside $V_{\mathrm{bad}}$. Assignments to a variable set $U$ are functions on the subtype of $U$; `glue σ τ` is the full assignment equal to $\sigma$ on $V_{\mathrm{bad}}$ and $\tau$ on $V_{\mathrm{good}}$. $\mu_F$ divides by $Z_F$ and is used only where $Z_F>0$. $\ln$ is `Real.log`, $\log_2$ is `Real.logb 2`; $r$, $D$ and $\lceil\log_2 n\rceil$ are natural numbers.
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), pp. 10–20: (3.1), §3.3, §3.4, Lemmas 3.1–3.3, Condition 3.12

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula

set_option autoImplicit false

open scoped BigOperators

namespace RandKSATSample.Main

noncomputable section

open Classical

/-!
# Parameters, the high-degree core, the good formula and nice formulas

He, Li, Yang, *Fast Almost-Uniform Sampling of Random k-SAT Solutions*, arXiv:2610.10474
(version not printed; file sha256 563a4d84…): the parameters (3.1) (p. 10) and of §3.4 (pp. 18–19),
the core construction and the good formula of §3.3 (pp. 13–14, 16, 18), the events of
Lemmas 3.1–3.3 (pp. 11–14), the polymer-root estimate and Condition 3.12 (p. 20).

All parameters are functions of `(n, m, k)`; `log`/`ln` is the natural logarithm and `log₂` is
`Real.logb 2`. Variables are `Fin n`, clause labels `Fin m`, literal positions `Fin k`.
Assignments to a variable set `U` are functions on the subtype `{v // v ∈ U}`.
-/

/-! ## The parameters (3.1) and §3.4 -/

/-- `λ = 1 + m/n`. -/
def lam (n m : ℕ) : ℝ := 1 + (m : ℝ) / n

/-- The high-degree cutoff `∆ = 6 k^7 λ`. -/
def Delta (n m k : ℕ) : ℝ := 6 * (k : ℝ) ^ 7 * lam n m

/-- `C_INC = 100 k² λ`. -/
def CINC (n m k : ℕ) : ℝ := 100 * (k : ℝ) ^ 2 * lam n m

/-- `D = ⌈6 k^8 λ⌉ + 1`. -/
def Dpar (n m k : ℕ) : ℕ := ⌈6 * (k : ℝ) ^ 8 * lam n m⌉₊ + 1

/-- `n0 = e^{k−3} λ (k − 4)^4`. -/
def n0 (n m k : ℕ) : ℝ := Real.exp ((k : ℝ) - 3) * lam n m * ((k : ℝ) - 4) ^ 4

/-- `q0 = (4 n0)^{−1/3}`. -/
def q0 (n m k : ℕ) : ℝ := (4 * n0 n m k) ^ (-(1 : ℝ) / 3)

/-- The integer cutoff `r = ⌊q0 n⌋`. -/
def rpar (n m k : ℕ) : ℕ := ⌊q0 n m k * n⌋₊

/-- `p∗ = 2^{−k+12}`. -/
def pStar (k : ℕ) : ℝ := (2 : ℝ) ^ ((12 : ℤ) - k)

/-- `C∗ = 10^4`. -/
def CStar : ℝ := 10 ^ 4

/-- `τ = ln(1/(C∗ p∗ D))` (§3.4). -/
def tau (n m k : ℕ) : ℝ := Real.log (1 / (CStar * pStar k * Dpar n m k))

/-- `x = e·p∗` (§3.4). -/
def xpar (k : ℕ) : ℝ := Real.exp 1 * pStar k

/-- `ρ = 4/(C∗·D)` (§3.4). -/
def rho (n m k : ℕ) : ℝ := 4 / (CStar * Dpar n m k)

variable {n m k : ℕ}

/-! ## The high-degree core -/

/-- The variables of high degree, `V_high = {v : deg(v) ≥ ∆}`. -/
def Vhigh (Φ : Formula n m k) : Finset (Fin n) :=
  Finset.univ.filter fun v => Delta n m k ≤ (deg Φ v : ℝ)

/-- A variable set `T` is closed under the core rule: every clause containing more than `8`
distinct variables of `T` has all its variables in `T`. -/
def CoreClosed (Φ : Formula n m k) (T : Finset (Fin n)) : Prop :=
  ∀ a : Fin m, 8 < (vbl Φ a ∩ T).card → vbl Φ a ⊆ T

/-- `Core(S)`: the result of starting from `S` and repeatedly adding all variables of a clause
that contains more than `8` distinct variables of the current set. This is the least superset
of `S` closed under the rule (the process is monotone, so the result does not depend on the
order of the additions). -/
def Core (Φ : Formula n m k) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∀ T : Finset (Fin n), S ⊆ T → CoreClosed Φ T → v ∈ T

/-- The core `V_bad = Core(V_high)`. -/
def Vbad (Φ : Formula n m k) : Finset (Fin n) := Core Φ (Vhigh Φ)

/-- The good variables `V_good = V ∖ V_bad`. -/
def Vgood (Φ : Formula n m k) : Finset (Fin n) := Finset.univ \ Vbad Φ

/-- The primal graph restricted to the core: `G_Φ[V_bad]`, as a graph on all variables whose
edges join two core variables. -/
def badGraph (Φ : Formula n m k) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => (primalGraph Φ).Adj u v ∧ u ∈ Vbad Φ ∧ v ∈ Vbad Φ

/-- The components `B_1, …, B_s`: the vertex sets of the connected components of `G_Φ[V_bad]`. -/
def blocks (Φ : Formula n m k) : Finset (Finset (Fin n)) :=
  (Vbad Φ).image fun v => Finset.univ.filter fun u => (badGraph Φ).Reachable v u

/-- Clause `a` is a core clause: `vbl(a) ⊆ V_bad`. -/
def IsCore (Φ : Formula n m k) (a : Fin m) : Prop := vbl Φ a ⊆ Vbad Φ

/-- `C_good`, the non-core clause labels: `vbl(a) ∩ V_good ≠ ∅`. -/
def Cgood (Φ : Formula n m k) : Finset (Fin m) :=
  Finset.univ.filter fun a => (vbl Φ a ∩ Vgood Φ).Nonempty

/-! ## Assignments to a part of the variables -/

/-- An assignment to the variables of `U`. -/
abbrev PartAssign (n : ℕ) (U : Finset (Fin n)) : Type := {v // v ∈ U} → Bool

/-- The partial assignment `τ` on `U` satisfies clause `a` through one of its literals on `U`. -/
def SatOn (Φ : Formula n m k) (U : Finset (Fin n)) (τ : PartAssign n U) (a : Fin m) : Prop :=
  ∃ i : Fin k, ∃ h : (Φ a i).1 ∈ U, τ ⟨(Φ a i).1, h⟩ = (Φ a i).2

/-- The restriction of an assignment on `U` to `B` (variables of `B` outside `U` get `false`;
only used for `B ⊆ U`). -/
def restrictTo {U : Finset (Fin n)} (σ : PartAssign n U) (B : Finset (Fin n)) : PartAssign n B :=
  fun v => if h : v.1 ∈ U then σ ⟨v.1, h⟩ else false

/-- `Ω_i` for the component `B`: the assignments to `B` satisfying every core clause meeting `B`. -/
def OmegaBlock (Φ : Formula n m k) (B : Finset (Fin n)) : Finset (PartAssign n B) :=
  Finset.univ.filter fun τ => ∀ a : Fin m, IsCore Φ a → (vbl Φ a ∩ B).Nonempty → SatOn Φ B τ a

/-- The feasible set of the core formula: assignments to `V_bad` satisfying every core clause. -/
def Omega (Φ : Formula n m k) : Finset (PartAssign n (Vbad Φ)) :=
  Finset.univ.filter fun σ => ∀ a : Fin m, IsCore Φ a → SatOn Φ (Vbad Φ) σ a

/-- The full assignment that agrees with `σ` on `V_bad` and with `τ` on `V_good`. -/
def glue (Φ : Formula n m k) (σ : PartAssign n (Vbad Φ)) (τ : PartAssign n (Vgood Φ)) :
    Assignment n :=
  fun v => if h : v ∈ Vbad Φ then σ ⟨v, h⟩ else τ ⟨v, by simp [Vgood, h]⟩

/-- `D_σ`: the good clause labels whose bad-variable literals are all false at `σ` (a clause
without bad-variable literals belongs to `D_σ`). -/
def Dsig (Φ : Formula n m k) (σ : PartAssign n (Vbad Φ)) : Finset (Fin m) :=
  (Cgood Φ).filter fun a => ∀ i : Fin k, ∀ h : (Φ a i).1 ∈ Vbad Φ, σ ⟨(Φ a i).1, h⟩ ≠ (Φ a i).2

/-! ## The good formula `Ψ`, its dependency graph and the measures `ν_good`, `µ_F` -/

/-- `E_a`: the residual clause `C_a^good` (the literals of `C_a` on good variables) is violated
by the good assignment `τ`. -/
def Viol (Φ : Formula n m k) (a : Fin m) (τ : PartAssign n (Vgood Φ)) : Prop :=
  ∀ i : Fin k, ∀ h : (Φ a i).1 ∈ Vgood Φ, τ ⟨(Φ a i).1, h⟩ ≠ (Φ a i).2

/-- `Good(F)`: every residual clause `C_a^good`, `a ∈ F`, is satisfied, i.e. `τ` satisfies the
deletion subformula `Ψ[F] = ⋀_{a ∈ F} C_a^good`. -/
def GoodEv (Φ : Formula n m k) (F : Finset (Fin m)) (τ : PartAssign n (Vgood Φ)) : Prop :=
  ∀ a ∈ F, ¬ Viol Φ a τ

/-- `ν_good(A)`: the probability of the event `A` under the uniform product measure on
`{0,1}^{V_good}`. -/
def nuGood (Φ : Formula n m k) (A : PartAssign n (Vgood Φ) → Prop) : ℝ :=
  ((Finset.univ.filter A).card : ℝ) / (Fintype.card (PartAssign n (Vgood Φ)) : ℝ)

/-- `Z_F = ν_good(Good(F))`. -/
def Zf (Φ : Formula n m k) (F : Finset (Fin m)) : ℝ := nuGood Φ (GoodEv Φ F)

/-- `µ_F(A) = ν_good(A | Good(F))` (used when `Z_F > 0`). -/
def muF (Φ : Formula n m k) (F : Finset (Fin m)) (A : PartAssign n (Vgood Φ) → Prop) : ℝ :=
  nuGood Φ (fun τ => A τ ∧ GoodEv Φ F τ) / Zf Φ F

/-- `q_S = ν_good(E_S)`, `E_S = ⋂_{a ∈ S} E_a`. -/
def qS (Φ : Formula n m k) (S : Finset (Fin m)) : ℝ := nuGood Φ fun τ => ∀ a ∈ S, Viol Φ a τ

/-- The dependency graph `H_Ψ` of the good formula on clause labels: two distinct good clauses
are adjacent when they share a good variable. -/
def HPsi (Φ : Formula n m k) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun a b =>
    a ∈ Cgood Φ ∧ b ∈ Cgood Φ ∧ (vbl Φ a ∩ vbl Φ b ∩ Vgood Φ).Nonempty

/-- `CS_Ψ(a)`: the nonempty connected sets of good clauses in `H_Ψ` containing `a`. -/
def CSPsi (Φ : Formula n m k) (a : Fin m) : Finset (Finset (Fin m)) :=
  (Cgood Φ).powerset.filter fun S => a ∈ S ∧ IsConnectedSet (HPsi Φ) S

/-- The closed neighbourhood `N_{H_Ψ}[a]` of a good clause. -/
def closedNbhd (Φ : Formula n m k) (a : Fin m) : Finset (Fin m) :=
  insert a ((Cgood Φ).filter fun b => (HPsi Φ).Adj a b)

/-- The polymer-root estimate: `Σ_{S ∈ CS_Ψ(a)} q_S e^{(1+τ)|S|} ≤ ρ` for every `a ∈ C_good`. -/
def PolyRoot (Φ : Formula n m k) : Prop :=
  ∀ a ∈ Cgood Φ, ∑ S ∈ CSPsi Φ a, qS Φ S * Real.exp ((1 + tau n m k) * S.card) ≤ rho n m k

/-! ## The events of Lemmas 3.1–3.3 and nice formulas -/

/-- The event of Lemma 3.1: every set `S` of at most `r` clauses has `|vbl(S)| ≥ (k − 4)|S|`. -/
def Expansion (Φ : Formula n m k) : Prop :=
  ∀ S : Finset (Fin m), S.card ≤ rpar n m k → ((k : ℝ) - 4) * S.card ≤ ((vblSet Φ S).card : ℝ)

/-- The event of Lemma 3.2: every connected variable set `U` has `I(U) < C_INC |U| + 4 ln n`. -/
def Incidence (Φ : Formula n m k) : Prop :=
  ∀ U : Finset (Fin n), IsConnectedSet (primalGraph Φ) U →
    (incident Φ U : ℝ) < CINC n m k * U.card + 4 * Real.log n

/-- The event of Lemma 3.3: `|V_high| ≤ r`. -/
def FewHigh (Φ : Formula n m k) : Prop := (Vhigh Φ).card ≤ rpar n m k

/-- The joint event of Lemmas 3.1 to 3.3. -/
def JointEvent (Φ : Formula n m k) : Prop := Expansion Φ ∧ Incidence Φ ∧ FewHigh Φ

/-- Condition 3.12 (nice formula): the parameter conditions `k ≥ 2^20`, `m/n ≤ 2^k/k^16`,
`r ≥ max{1, ⌈log₂ n⌉}`, the structural conditions (Lemmas 3.1–3.3) and the polymer-root
estimate. -/
def Nice (Φ : Formula n m k) : Prop :=
  2 ^ 20 ≤ k ∧ (m : ℝ) / n ≤ (2 : ℝ) ^ k / (k : ℝ) ^ 16 ∧
    max 1 ⌈Real.logb 2 n⌉₊ ≤ rpar n m k ∧ JointEvent Φ ∧ PolyRoot Φ

end

end RandKSATSample.Main


