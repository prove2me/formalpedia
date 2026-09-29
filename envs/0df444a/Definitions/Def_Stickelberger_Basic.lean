-- Prove2me | Definitions.Def_Stickelberger_Basic
-- name    : Stickelberger_Basic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/36a11e82-5bcd-55b9-b254-40c48822ab89
-- title:
--   Stickelberger element acting on a mod-p Δ-module
-- statement:
--   Fix a natural number $p$, an additive commutative group $A$ carrying a $\mathbb{Z}/p$-module structure, and regard an action of $\Delta=(\mathbb{Z}/p)^\times$ on $A$ as a monoid homomorphism $\rho\colon(\mathbb{Z}/p)^\times\to\operatorname{End}_{\mathbb{Z}/p}(A)$ rather than as a group-action instance. The indexing set `exponentSet p` is the finite set of natural numbers $c<p$ with $0<c$ and $2c<p$, i.e. the integers in the lower half interval $0<c<p/2$; the accompanying membership lemma records that $c$ lies in it exactly when $0<c$ and $2c<p$, the bound $c<p$ being automatic. The natural number `eigenvalueScalar p` is the sum $\sum_{0<c<p/2}c$ of the elements of that set. For $c:\mathbb{N}$, `expUnit p c` is the unit of $\mathbb{Z}/p$ determined by $c$ when $c$ is coprime to $p$ (via Mathlib's `ZMod.unitOfCoprime`) and is $1$ otherwise, so it is a total function on $\mathbb{N}$ by a case split rather than a partially defined one.
--
--   Given $\rho$, the endomorphism `stickelbergerEnd` is $\eta=\sum_{c\in\mathtt{exponentSet}\,p}\rho\bigl((\mathtt{expUnit}\,p\,c)^{-1}\bigr)$, the sum taken in the $\mathbb{Z}/p$-linear endomorphism ring; this is the integral half-interval Stickelberger operator $\sum_{0<c<p/2}\sigma_c^{-1}$ acting through $\rho$. The predicate `StickelbergerAnnihilates` asserts that $\eta a=0$ for every $a\in A$, stated pointwise rather than as the equation $\eta=0$ in the endomorphism ring. The predicate `IsOmegaEigenvector` takes an exponent $i:\mathbb{N}$ and an element $a\in A$, and asserts that $\rho(d)\,a=\bigl(\bar d^{\,i}\bigr)\cdot a$ for every unit $d$ of $\mathbb{Z}/p$, where $\bar d\in\mathbb{Z}/p$ is the underlying residue: thus $a$ lies in the $\omega^i$-eigenspace for the given action, with $\omega$ the inclusion of $\Delta$ into $(\mathbb{Z}/p)^\times$.
--
--   **Relation to Mathlib.** Mathlib has no Stickelberger element or eigenspace-decomposition API; these notions are the project's own, built from Mathlib's `ZMod`, its unit `ZMod.unitOfCoprime`, and `Module.End`.
--
--   **Where it is used.** These definitions are the carriers for the Stickelberger annihilation and $\omega^i$-eigenspace statements used in the cyclotomic input to the theory of rational torsion on elliptic curves, which enters the irreducibility and level-lowering side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Stickelberger_Basic.lean

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Stickelberger

def exponentSet (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun c => 0 < c ∧ 2 * c < p

@[simp] lemma mem_exponentSet {p c : ℕ} :
    c ∈ exponentSet p ↔ 0 < c ∧ 2 * c < p := by
  simp only [exponentSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

def eigenvalueScalar (p : ℕ) : ℕ := ∑ c ∈ exponentSet p, c

noncomputable def expUnit (p : ℕ) (c : ℕ) : (ZMod p)ˣ :=
  if h : Nat.Coprime c p then ZMod.unitOfCoprime c h else 1

variable {p : ℕ} {A : Type*} [AddCommGroup A] [Module (ZMod p) A]

noncomputable def stickelbergerEnd (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) :
    Module.End (ZMod p) A :=
  ∑ c ∈ exponentSet p, ρ (expUnit p c)⁻¹

def StickelbergerAnnihilates (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) : Prop :=
  ∀ a : A, stickelbergerEnd ρ a = 0

def IsOmegaEigenvector (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ) (a : A) : Prop :=
  ∀ d : (ZMod p)ˣ, ρ d a = ((d : ZMod p) ^ i) • a

end Stickelberger


