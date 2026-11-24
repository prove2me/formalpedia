-- Prove2me | Definitions.Def_JointMixND_QuadOT_Supplement_Dependence
-- name    : JointMixND_QuadOT_Supplement_Dependence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:09:29.905802+00:00
-- url     : https://prove2.me/theorems/2d30e3d7-a58f-4692-9049-fdbbcaff0f4f
-- title:
--   Defs. 1(ii)–(iv), 2, pp. 3–4, 8 — heterogeneous marginals, the independent copy X⊥, NUOD/NLOD/NOD, NSD, NA, strict NCD, binary multinomial vectors
-- statement:
--   Let $\mathbf X=(X_1,\dots,X_n)$ be a random vector, represented by its law $P$ on $\mathbb R^n$. Write $[n]=\{1,\dots,n\}$, $\mathbf X_A=(X_k)_{k\in A}$ and $S_A=\sum_{i\in A}X_i$ for $A\subseteq[n]$.
--
--   1. **Marginals.** $P$ has marginals $(F_1,\dots,F_n)$ if $P$ is a probability law with $X_i\sim F_i$ for each $i$. A tuple $(F_1,\dots,F_n)$ *supports a joint mix* if some $P$ with these marginals is a joint mix (Definition 2).
--   2. **Independent copy.** $\mathbf X^\perp$ has independent components with $X^\perp_i\overset d=X_i$; its law is the product $P_1\otimes\cdots\otimes P_n$ of the marginals of $P$.
--   3. **NUOD / NLOD / NOD.** $\mathbf X$ is NUOD if $\mathbb P(\mathbf X>\mathbf t)\le\mathbb P(\mathbf X^\perp>\mathbf t)$ for all $\mathbf t\in\mathbb R^n$ (componentwise strict inequality), NLOD if $\mathbb P(\mathbf X\le\mathbf t)\le\mathbb P(\mathbf X^\perp\le\mathbf t)$ for all $\mathbf t$, and NOD if both.
--   4. **NSD.** $\mathbf X$ is NSD if $\mathbb E[\varphi(\mathbf X)]\le\mathbb E[\varphi(\mathbf X^\perp)]$ for every supermodular $\varphi:\mathbb R^n\to\mathbb R$ ($\varphi(x\wedge y)+\varphi(x\vee y)\ge\varphi(x)+\varphi(y)$) for which both expectations exist.
--   5. **NA.** $\mathbf X$ is NA if
--   $$\operatorname{Cov}\big(f(\mathbf X_A),g(\mathbf X_B)\big)\le0$$
--   for all disjoint $A,B\subseteq[n]$ and all coordinatewise increasing $f:\mathbb R^A\to\mathbb R$, $g:\mathbb R^B\to\mathbb R$ such that $f(\mathbf X_A)$ and $g(\mathbf X_B)$ have finite second moments.
--   6. **Strict NCD.** Every $X_i$ has a finite second moment and $\operatorname{Cov}(X_i,X_j)\le0$ for $i\ne j$.
--   7. **Binary multinomial vector.** A random vector $\mathbf Y$ on a probability space $(\Omega,\mu)$ with values in $\{0,1\}^n$ and $\sum_iY_i=1$, i.e. exactly one coordinate equals $1$.
--
--   These notions are the negative-dependence concepts of Section 2 of the paper, used by Theorems 1–3 and 6. The joint-mix and NCD predicates are the published ones of the base mission.
--
--   **Formalization Note** Coordinates are 0-based (`Fin n`). Random vectors are represented by their laws, except binary multinomial vectors, which are random vectors on a given space because Theorem 3 represents a given random vector. The independent copy is `Measure.pi` of the marginals (defined as $0$ for an infinite measure, which never occurs). NSD reuses the platform's supermodular order `StochasticOrders.PositiveDependence.SupermodularOrder`, in which "the expectations exist" means $\varphi$ is integrable under both laws. In NA, "finite second moment" is `MemLp … 2`, which includes almost-everywhere measurability of $f(\mathbf X_A)$; no further measurability of $f,g$ is imposed. A binary multinomial vector is measurable and satisfies its constraints almost surely. Strict NCD adds square integrability to the published `IsNCD`, because Definition 1(i) presupposes that the covariances exist.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, pp. 3–4, Definitions 1(ii)–(iv) and 2; p. 8, binary multinomial random vector

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_StochasticOrders_PositiveDependence_Orders

namespace JointMixND.QuadOT.Supplement

open MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-- Definition 2, p. 4 (heterogeneous marginals): `P` is the law of a random vector
`(X_1, …, X_n)` with `X_i ∼ F_i` for every `i` (0-based: the paper's `X_i` is `x (i-1)`).
"`(F_1, …, F_n)` supports a joint mix" is `∃ P, HasMarginals F P ∧ IsJointMix P`. -/
def HasMarginals (F : Fin n → Measure ℝ) (P : Measure (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ ∀ i : Fin n, P.map (fun x => x i) = F i

/-- p. 3: the law of `X^⊥`, a random vector with independent components and `X^⊥_i =d X_i`:
the product of the marginals of `P`. (Junk value `0` for an infinite measure, never used.) -/
noncomputable def indepCopy (P : Measure (Fin n → ℝ)) : Measure (Fin n → ℝ) := by
  classical
  exact if h : IsFiniteMeasure P then
    haveI := h
    Measure.pi (fun i : Fin n => P.map (fun x => x i))
  else 0

/-- Definition 1(ii), p. 4: NUOD, `P(X > t) ≤ P(X^⊥ > t)` for all `t ∈ ℝⁿ` (componentwise `>`). -/
def IsNUOD (P : Measure (Fin n → ℝ)) : Prop :=
  ∀ t : Fin n → ℝ, P {x | ∀ i, t i < x i} ≤ indepCopy P {x | ∀ i, t i < x i}

/-- Definition 1(ii), p. 4: NLOD, `P(X ≤ t) ≤ P(X^⊥ ≤ t)` for all `t ∈ ℝⁿ`. -/
def IsNLOD (P : Measure (Fin n → ℝ)) : Prop :=
  ∀ t : Fin n → ℝ, P {x | ∀ i, x i ≤ t i} ≤ indepCopy P {x | ∀ i, x i ≤ t i}

/-- Definition 1(ii), p. 4: NOD = NLOD and NUOD. -/
def IsNOD (P : Measure (Fin n → ℝ)) : Prop := IsNLOD P ∧ IsNUOD P

/-- Definition 1(iii), p. 4: NSD, `E[φ(X)] ≤ E[φ(X^⊥)]` for every supermodular `φ : ℝⁿ → ℝ`
for which both expectations exist (the platform's supermodular order, `X ≤_sm X^⊥`). -/
def IsNSD (P : Measure (Fin n → ℝ)) : Prop :=
  StochasticOrders.PositiveDependence.SupermodularOrder P (indepCopy P)

/-- `X_A = (X_k)_{k ∈ A}` (p. 3). -/
def restrictTo (A : Finset (Fin n)) (x : Fin n → ℝ) : A → ℝ := fun i => x i

/-- `S_A = ∑_{i ∈ A} X_i` (Theorem 1, p. 5). -/
def sumOver (A : Finset (Fin n)) (x : Fin n → ℝ) : ℝ := ∑ i ∈ A, x i

theorem measurable_restrictTo (A : Finset (Fin n)) : Measurable (restrictTo A) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (i : Fin n))

theorem measurable_sumOver (A : Finset (Fin n)) : Measurable (sumOver A) :=
  Finset.measurable_sum A (fun i _ => measurable_pi_apply i)

/-- Definition 1(iv), p. 4: NA, `Cov(f(X_A), g(X_B)) ≤ 0` for all disjoint `A, B ⊆ [n]` and all
coordinatewise increasing `f : ℝ^A → ℝ`, `g : ℝ^B → ℝ` such that `f(X_A)` and `g(X_B)` have finite
second moments. -/
def IsNA (P : Measure (Fin n → ℝ)) : Prop :=
  ∀ A B : Finset (Fin n), Disjoint A B →
    ∀ (f : (A → ℝ) → ℝ) (g : (B → ℝ) → ℝ), Monotone f → Monotone g →
      MemLp (fun x => f (restrictTo A x)) 2 P → MemLp (fun x => g (restrictTo B x)) 2 P →
      covariance (fun x => f (restrictTo A x)) (fun x => g (restrictTo B x)) P ≤ 0

/-- Finite-second-moment refinement of Definition 1(i), p. 4, used for the corrected Theorem 6:
every coordinate is square integrable and `Cov(X_i, X_j) ≤ 0` for `i ≠ j` (the published `IsNCD`). -/
def IsStrictNCD (P : Measure (Fin n → ℝ)) : Prop :=
  (∀ i : Fin n, MemLp (fun x => x i) 2 P) ∧ IsNCD P

/-- p. 8: `Y` is a binary multinomial random vector on `(Ω, μ)`: a random vector taking values in
`{0,1}ⁿ` with `∑ Y_i = 1` (almost surely). -/
def IsBinaryMultinomial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → Fin n → ℝ) :
    Prop :=
  Measurable Y ∧ ∀ᵐ ω ∂μ, (∀ i, Y ω i = 0 ∨ Y ω i = 1) ∧ ∑ i, Y ω i = 1

end JointMixND.QuadOT.Supplement


