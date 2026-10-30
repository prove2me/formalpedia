-- Prove2me | Definitions.Def_ComputationalOTAudit_EntropicDuality_support_interface
-- name    : ComputationalOTAudit_EntropicDuality_support_interface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:32:01.179876+00:00
-- url     : https://prove2.me/theorems/438e0666-ed2c-4675-ade0-af5eb41d497d
-- title:
--   Support dual, independent values, and nonnegative scaling interface
-- statement:
--   Let $a\in\mathbb R^n$ and $b\in\mathbb R^m$ be histograms, $C\in\mathbb R^{n\times m}$ a real matrix, and $\varepsilon>0$. Reuse the published coupling set $U(a,b)$, primal objective $F(P)=\langle C,P\rangle-\varepsilon H(P)$, Gibbs kernel $K_{ij}=e^{-C_{ij}/\varepsilon}$, and full real dual objective $Q(f,g)$ without changing them. Define their independent value sets by
--
--   $$\mathcal V_P=\{F(P):P\in U(a,b)\},\qquad L=\inf\mathcal V_P,\qquad \mathcal V_D=\{Q(f,g):f\in\mathbb R^n,g\in\mathbb R^m\}.$$
--
--   The positive supports are $I=\{i:a_i>0\}$ and $J=\{j:b_j>0\}$. Full support means every coordinate is positive. For support potentials, define
--
--   $$Q_{I,J}(f,g)=\sum_{i\in I}f_i a_i+\sum_{j\in J}g_j b_j-\varepsilon\sum_{i\in I,j\in J}e^{f_i/\varepsilon}K_{ij}e^{g_j/\varepsilon}.$$
--
--   A maximizer of either dual objective dominates every potential pair in that objective's domain. Full exponentials and logarithms are $e^{f_i/\varepsilon}$ and $\varepsilon\log u_i$. Support exponentiation uses the same formula on $I$ and extends by zero at every other original coordinate; support logarithms are defined only on the support subtype. The corresponding definitions apply to $b$.
--
--   The scaled matrix is $P(u,v)_{ij}=u_iK_{ij}v_j$. A representation of $P$ requires only $u,v\ge0$ and $P=P(u,v)$. A feasible scaling requires only nonnegativity and $P(u,v)\in U(a,b)$; neither predicate assumes optimality or duality. These interfaces express the corrected boundary form of Proposition 4.4 while preserving all original rows and columns.
--
--   **Formalization Note** Indices use `Fin n` and `Fin m`, and the support subtypes have their usual finite enumerations. The real infimum defaults to zero on the empty set or on an unbounded-below set; the theorem establishes nonemptiness, boundedness, and attainment rather than taking them as hypotheses. All formulas are total outside their intended domain; division at zero uses Lean's default, and logarithms at nonpositive inputs have no inverse meaning. The goal requires positive epsilon and asserts positivity of the relevant scaling coordinates. Entropy and the full dual formula are imported, not redefined here.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport, Foundations and Trends in Machine Learning 11(5–6), 2019, DOI 10.1561/2200000073, §2.1, (2.10), (4.1)–(4.2), Gibbs kernel, (4.12), Proposition 4.4 (4.30)–(4.31); printed pp. 363, 370, 425–426, 428, 432, 448–449 / PDF pp. 13, 20, 75–76, 78, 82, 98–99; continuous zero reading supported by Example 8.1 (8.4), printed p. 495 / PDF p. 145. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs
import Definitions.Def_CompOT_EntropicLimit_Defs
import Definitions.Def_CompOT_EntropicDual_Defs

open scoped Classical
noncomputable section

namespace ComputationalOTAudit.EntropicDuality

/-- Positive bins of a histogram. No bins are removed from the original data. -/
def PositiveSupport {n : ℕ} (a : Fin n → ℝ) := {i : Fin n // 0 < a i}

instance positiveSupportFintype {n : ℕ} (a : Fin n → ℝ) : Fintype (PositiveSupport a) :=
  inferInstanceAs (Fintype {i : Fin n // 0 < a i})

def FullSupport {n : ℕ} (a : Fin n → ℝ) : Prop := ∀ i, 0 < a i

/-- Values of the published primal objective over every feasible matrix. -/
def PrimalValues {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) : Set ℝ :=
  Set.range (fun P : CompOT.Assignment.couplings a b =>
    CompOT.EntropicLimit.entObjective C ε P.val)

/-- Its mathematical use requires nonemptiness and a lower bound, both goal conclusions. -/
def PrimalValue {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) : ℝ :=
  sInf (PrimalValues C a b ε)

/-- Independently computed from all finite real potentials, including zero-bin coordinates. -/
def FullDualValues {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) : Set ℝ :=
  Set.range (fun fg : (Fin n → ℝ) × (Fin m → ℝ) =>
    CompOT.EntropicDual.dualObjEnt C a b ε fg.1 fg.2)

def IsFullDualMaximizer {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) : Prop :=
  ∀ f' g', CompOT.EntropicDual.dualObjEnt C a b ε f' g' ≤
    CompOT.EntropicDual.dualObjEnt C a b ε f g

/-- The same objective on the two positive-support subtypes; no reference to a primal value. -/
def SupportDualObjective {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ) : ℝ :=
  (∑ i : PositiveSupport a, f i * a i.val) +
    (∑ j : PositiveSupport b, g j * b j.val) -
    ε * ∑ i : PositiveSupport a, ∑ j : PositiveSupport b,
      Real.exp (f i / ε) * CompOT.EntropicDual.gibbs C ε i.val j.val *
        Real.exp (g j / ε)

def IsSupportDualMaximizer {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ) : Prop :=
  ∀ f' g', SupportDualObjective C a b ε f' g' ≤ SupportDualObjective C a b ε f g

def FullExp {n : ℕ} (ε : ℝ) (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (f i / ε)

/-- Used only when all scaling coordinates have been asserted positive. -/
def FullLog {n : ℕ} (ε : ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  ε * Real.log (u i)

/-- Exponentiate on the support and extend by zero at every other original index. -/
def SupportExp {n : ℕ} (a : Fin n → ℝ) (ε : ℝ)
    (f : PositiveSupport a → ℝ) (i : Fin n) : ℝ :=
  if hi : 0 < a i then Real.exp (f ⟨i, hi⟩ / ε) else 0

/-- The theorem asserts positivity on the support before giving the inverse relation. -/
def SupportLog {n : ℕ} (a : Fin n → ℝ) (ε : ℝ)
    (u : Fin n → ℝ) (i : PositiveSupport a) : ℝ :=
  ε * Real.log (u i.val)

def ScaledCoupling {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ)
    (u : Fin n → ℝ) (v : Fin m → ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => u i * CompOT.EntropicDual.gibbs C ε i j * v j

/-- Nonnegative factorization alone: no optimality or dual certificate is bundled here. -/
def RepresentsCoupling {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) (u : Fin n → ℝ) (v : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧ P = ScaledCoupling C ε u v

/-- Feasibility alone, over the full original matrix. -/
def IsFeasibleScaling {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (u : Fin n → ℝ) (v : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧
    ScaledCoupling C ε u v ∈ CompOT.Assignment.couplings a b

end ComputationalOTAudit.EntropicDuality


