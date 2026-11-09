-- Prove2me | Definitions.Def_MinCostMaj_SimpInst
-- name    : MinCostMaj_SimpInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:10:07.362129+00:00
-- url     : https://prove2.me/theorems/95e3d675-93a8-4d69-86b9-586c9b3afeaf
-- title:
--   Simplified instances, (2,3)-consistency and the BLP relaxation
-- statement:
--   A **simplified instance** (§5) has, for every ordered pair of variables $(x,y)$, a single relation $R_{xy}$, with $R_{yx}=R_{xy}^{-1}$ and $R_{xx}\subseteq\{(a,a)\}$; the potato of $x$ is $A_x=\{a:(a,a)\in R_{xx}\}$.
--
--   1. It is **(2,3)-consistent** if for all $x,y,z$ and $(a,b)\in R_{xy}$ there is $c$ with $(a,c)\in R_{xz}$ and $(b,c)\in R_{yz}$.
--   2. The **(2,3)-consistency preprocessing** deletes tuples until this holds; its result is the largest (2,3)-consistent family $R'$ with $R'_{xy}\subseteq R_{xy}$ for all $x,y$.
--   3. A **feasible solution of the basic LP relaxation (BLP)** (Figure 3) consists of numbers $\lambda_x(a)\ge0$ and $\lambda_{xy}(a,b)\ge0$ with
--   $$\sum_a\lambda_x(a)=1,\quad\sum_{(a,b)\in R_{xy}}\lambda_{xy}(a,b)=1,\quad\sum_{b:(a,b)\in R_{xy}}\lambda_{xy}(a,b)=\lambda_x(a),\quad\sum_{a:(a,b)\in R_{xy}}\lambda_{xy}(a,b)=\lambda_y(b)$$
--   for all $x,y\in V$ and $a,b\in A$.
--
--   These are the inputs of the rounding algorithm of §5.
--
--   **Formalization Note** A union of (2,3)-consistent families is (2,3)-consistent and the deletion procedure never removes a tuple of a (2,3)-consistent subfamily, so the procedure ends at the largest one whatever the order of deletions. A simplified instance is viewed as an instance of §3 with one constraint per ordered pair.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §5, p.10; Figure 3, p.20 (PDF pp.11, 21)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst

namespace MinCostMaj

/-- **Simplified instance** (§5, p.10): one relation `R_xy` for every ordered pair, with
`R_yx = −R_xy` and `R_xx ⊆ {(a, a)}`.

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, §5, p.10: "throughout this section, for every ordered pair of
variables (x, y) there is a single binary relation Rxy. We can further assume that Ryx = −Rxy (where
−R is the opposite reading of R). For Rxx … we obtain Rxx = {(a, a) : a ∈ A^I_x} for suitably chosen
A^I_x." -/
def IsSimplified {V D : Type*} (R : V → V → Set (D × D)) : Prop :=
  (∀ x y, R y x = Prod.swap ⁻¹' R x y) ∧ ∀ x (a b : D), (a, b) ∈ R x x → a = b

/-- **(2,3)-consistency** (§5, p.10): "for every triple of variables x, y, z and every
(a, b) ∈ Rxy, there is c ∈ Az such that (a, c) ∈ Rxz and (b, c) ∈ Ryz." -/
def Is23Consistent {V D : Type*} (R : V → V → Set (D × D)) : Prop :=
  ∀ x y z, ∀ ab ∈ R x y, ∃ c, (ab.1, c) ∈ R x z ∧ (ab.2, c) ∈ R y z

/-- **The output of the (2,3)-consistency preprocessing** (§5, p.10: "we repeatedly delete tuples
until" the (2,3)-condition holds): the largest (2,3)-consistent subfamily of `R`, the union of all
(2,3)-consistent families `R′` with `R′_xy ⊆ R_xy`.

**Formalization Note.** A union of (2,3)-consistent families is (2,3)-consistent, and a deleted
tuple lies in no (2,3)-consistent subfamily, so the deletion procedure ends at this family whatever
the order of deletions. -/
def greatest23 {V D : Type*} (R : V → V → Set (D × D)) : V → V → Set (D × D) :=
  fun x y => {ab | ∃ R' : V → V → Set (D × D),
    (∀ u v, R' u v ⊆ R u v) ∧ Is23Consistent R' ∧ ab ∈ R' x y}

/-- The potatoes of a simplified instance, read from its diagonal: `Aₓ = {a : (a, a) ∈ R_xx}`. -/
def simpPot {V D : Type*} (R : V → V → Set (D × D)) (x : V) : Set D :=
  {a | (a, a) ∈ R x x}

open Classical in
/-- The potato `Aₓ` as a finite set. -/
noncomputable def simpPotF {V D : Type*} [Fintype D] (R : V → V → Set (D × D)) (x : V) :
    Finset D :=
  Finset.univ.filter (fun a => (a, a) ∈ R x x)

/-- A simplified instance as an instance of §3: potatoes `simpPot R`, and `R_xy = {R x y}`. -/
def simpToBin {V D : Type*} (R : V → V → Set (D × D)) : BinInst V D where
  pot := simpPot R
  rels := fun x y => {R x y}

open Classical in
/-- **Feasible solution of the BLP relaxation** (Figure 3, p.20): `λₓ(a) ≥ 0`, `λ_xy(a, b) ≥ 0`,
`Σ_a λₓ(a) = 1`, `Σ_{(a,b)∈R_xy} λ_xy(a, b) = 1`, `Σ_{b:(a,b)∈R_xy} λ_xy(a, b) = λₓ(a)` and
`Σ_{a:(a,b)∈R_xy} λ_xy(a, b) = λ_y(b)` for all `x, y ∈ V` and `a, b ∈ A`. -/
def IsBLPFeasible {V D : Type*} [Fintype D] (R : V → V → Set (D × D)) (lam₁ : V → D → ℝ)
    (lam₂ : V → V → D × D → ℝ) : Prop :=
  (∀ x a, 0 ≤ lam₁ x a) ∧ (∀ x y ab, 0 ≤ lam₂ x y ab) ∧
  (∀ x, ∑ a, lam₁ x a = 1) ∧
  (∀ x y, ∑ ab ∈ Finset.univ.filter (· ∈ R x y), lam₂ x y ab = 1) ∧
  (∀ x y a, ∑ b ∈ Finset.univ.filter (fun b => (a, b) ∈ R x y), lam₂ x y (a, b) = lam₁ x a) ∧
  (∀ x y b, ∑ a ∈ Finset.univ.filter (fun a => (a, b) ∈ R x y), lam₂ x y (a, b) = lam₁ y b)

end MinCostMaj


