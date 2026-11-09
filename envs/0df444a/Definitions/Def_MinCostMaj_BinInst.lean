-- Prove2me | Definitions.Def_MinCostMaj_BinInst
-- name    : MinCostMaj_BinInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:05:00.592335+00:00
-- url     : https://prove2.me/theorems/24752cbb-c5ec-451c-8435-1b5de1f58814
-- title:
--   Instances with binary constraints and potatoes; arc consistency; subinstances
-- statement:
--   An **instance** $I$ (Section 3 of the paper) has a set $V$ of variables and, for each ordered pair $u,v\in V$, a set $\mathcal R_{uv}$ of binary relations, the constraints; by convention $\mathcal R_{vu}$ consists of the opposite readings $R^{-1}=\{(b,a):(a,b)\in R\}$ of the relations of $\mathcal R_{uv}$. Each variable $u$ carries a specified set $A^I_u$, its **potato**.
--
--   1. $I$ is **binary** (Appendix A) if every $R\in\mathcal R_{uv}$ is contained in $A^I_u\times A^I_v$.
--   2. A **solution** is an $\alpha:V\to A$ with $\alpha(u)\in A^I_u$ and $(\alpha(u),\alpha(v))\in R$ for all $u,v$ and $R\in\mathcal R_{uv}$.
--   3. $I$ is **arc-consistent** if all potatoes are nonempty and every $R\in\mathcal R_{uv}$ has $\mathrm{proj}_1(R)=A^I_u$ and $\mathrm{proj}_2(R)=A^I_v$.
--   4. $I\le J$ ($I$ is a **subinstance** of $J$) if $A^I_u\subseteq A^J_u$ for all $u$ and $\mathcal R^I_{uv}=\{R\cap(A^I_u\times A^I_v):R\in\mathcal R^J_{uv}\}$.
--   5. $I$ has a **proper arc-consistent subinstance** if some arc-consistent $I'\le I$ has $A^{I'}_u\subsetneq A^I_u$ for some $u$.
--
--   These are the instances on which the combinatorial dividing line of the dichotomy is drawn.
--
--   **Formalization Note** The opposite-readings convention is the predicate `IsSymm`, assumed in every statement. For arc-consistent instances a solution in the potato sense is the same as an assignment satisfying all constraints.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §3, p.6; Appendix A, pp.12–13 (PDF pp.7, 13–14)

import Mathlib

namespace MinCostMaj

/-- **Instance of CSP(A) with binary constraints and specified potatoes** (Section 3).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, §3, p.6: "An instance I of CSP(A) has a variable set V, and, for
each ordered pair u, v ∈ V, a set Ruv of binary relations called constraints. We assume that Ruv
and Rvu contain opposite readings of the same relations. … Let I and J be instances on the same
variable set V with specified potatoes."

`pot u` is the potato `A^I_u ⊆ D` of `u`; `rels u v` is the set `R_uv` of binary relations on `D`.

**Formalization Note.** The opposite-readings convention is the separate predicate `IsSymm`; every
statement about instances assumes it, as the paper does. Variable sets are finite types in the
statements (instances are finite inputs). -/
structure BinInst (V D : Type*) where
  /-- the potatoes `A^I_u` -/
  pot : V → Set D
  /-- the constraint sets `R_uv` -/
  rels : V → V → Set (Set (D × D))

namespace BinInst

variable {V D : Type*}

/-- "`R_uv` and `R_vu` contain opposite readings of the same relations" (§3, p.6):
`R_vu = {R⁻¹ : R ∈ R_uv}` with `R⁻¹ = {(b, a) : (a, b) ∈ R}`. -/
def IsSymm (I : BinInst V D) : Prop :=
  ∀ u v, I.rels v u = (fun R => Prod.swap ⁻¹' R) '' I.rels u v

/-- **Binary instance** in the sense of Appendix A (Definition A.2, p.13, where `fₓ : A²ₓ → Aₓ`):
every constraint of `R_xy` is a relation between the potatoes, `R ⊆ Aₓ × A_y`. Arc-consistent
instances satisfy it automatically. -/
def IsBinary (I : BinInst V D) : Prop :=
  ∀ u v, ∀ R ∈ I.rels u v, R ⊆ I.pot u ×ˢ I.pot v

/-- **Solution** of an instance with potatoes: `α(u) ∈ A_u` for every `u` and
`(α(u), α(v)) ∈ R` for every `R ∈ R_uv`.

**Formalization Note.** For arc-consistent instances the potato condition is implied by the
constraints for constrained variables, and potatoes are nonempty for the others, so solvability
is the same as for the reading without potatoes. -/
def IsSolution (I : BinInst V D) (α : V → D) : Prop :=
  (∀ u, α u ∈ I.pot u) ∧ ∀ u v, ∀ R ∈ I.rels u v, (α u, α v) ∈ R

/-- **Arc consistency** (§3, p.6): "I is arc-consistent if there exist nonempty sets {A^I_u}u∈V
such that, for every pair of variables u, v and every R ∈ Ruv, one has proj1(R) = A^I_u and
proj2(R) = A^I_v."

**Formalization Note.** The witnessing sets are the instance's specified potatoes `pot`. -/
def IsArcConsistent (I : BinInst V D) : Prop :=
  (∀ u, (I.pot u).Nonempty) ∧
    ∀ u v, ∀ R ∈ I.rels u v, Prod.fst '' R = I.pot u ∧ Prod.snd '' R = I.pot v

/-- **Subinstance** `I ≤ J` (§3, p.6): "for every u ∈ V, A^I_u ⊆ A^J_u, and, for all u, v ∈ V,
R^I_uv = {R ∩ (A^I_u × A^I_v) : R ∈ R^J_uv}." -/
def Le (I J : BinInst V D) : Prop :=
  (∀ u, I.pot u ⊆ J.pot u) ∧
    ∀ u v, I.rels u v = (fun R => R ∩ (I.pot u ×ˢ I.pot v)) '' J.rels u v

/-- **`I` has a proper arc-consistent subinstance** (Theorem 4.1 Item 1, p.8): there is an
arc-consistent `I′ ≤ I` with `A^{I′}_u ⊊ A^I_u` for at least one `u`. -/
def HasProperACSub (I : BinInst V D) : Prop :=
  ∃ I' : BinInst V D, Le I' I ∧ IsArcConsistent I' ∧ ∃ u, I'.pot u ⊂ I.pot u

end BinInst

end MinCostMaj


