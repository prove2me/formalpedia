-- Prove2me | Definitions.Def_EssCheck_Accuracy_Model
-- name    : EssCheck_Accuracy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:32.419467+00:00
-- url     : https://prove2.me/theorems/fe6ffe0d-1b11-408d-9cc4-af127aa96e13
-- title:
--   §§2–4 — essentiality checks, licensing, effort, and welfare model
-- statement:
--   The model has finitely many commercial-value states $i$. The upstream innovator's research succeeds with probability $x$ and costs $c(x)$. Success makes its patent essential; failure leads the standard setter to use the status-quo technology. The value distributions after success, after failure on the innovator's technology, and on the status quo are $p^H$, $p^L$, and $p^0$. A non-essential patent is incorrectly certified with probability $1-\beta$. The maximum royalty fraction is $\bar\alpha$, and litigation costs each party $l_i$.
--
--   The standing conditions make the three distributions nonnegative and normalized, put $0<\bar\alpha\le1$ and $0<l_i<\bar\alpha v_i$, impose the paper's ordering of expected values, and require an increasing convex cost with $c'(0)=0$ and $c'(x)\to\infty$ as $x\uparrow1$. The cost is twice continuously differentiable below one.
--
--   For a certified patent, the definition gives the belief $\lambda_i^c$, the hybrid or pooling regime, the high-royalty offer probability $y_i$, and litigation probability $z_i$ from equations (1)–(3). The upstream and downstream payoffs come from Appendix A. The resulting success and failure revenues and surpluses define the primitive welfare function
--   $$w(\beta,x)=xw^H(\beta,x)+(1-x)w^L(\beta,x)-c(x).$$
--   The two investment wedges are the left-hand sides of equations (5) and (7). An equilibrium-effort predicate requires interior effort and the private first-order condition, with the implementer's belief equal to actual effort.
--
--   These shared definitions fix the meaning of every milestone and of Proposition 1. Welfare is computed from the parties' payoffs and certification outcomes, rather than defined by its simplified expression (6).
--
--   **Formalization Note** States are indexed by `Fin n`, and real probability vectors are used. The strictly positive litigation cost $l_i>0$ is an explicit addition needed at degenerate states. At zero-probability states, Lean's total division sets a zero-denominator belief to zero; subsequent theorems handle such states by probability-weighted formulas. Uncertified patents yield no upstream revenue and no litigation cost.
-- source:
--   Schuett & Wipusanawan, Essentiality Checks for Standard Essential Patents, TILEC Discussion Paper DP 2023-21 (Dec. 2023; SSRN 4688864), pp. 9–22 (PDF 10–23), §§2–4, Assumptions 1–2, equations (1)–(7); Appendix A, p. 35 (PDF 36)

import Mathlib

namespace EssCheck.Accuracy

noncomputable section

structure Model (n : ℕ) where
  v : Fin n → ℝ
  l : Fin n → ℝ
  pH : Fin n → ℝ
  pL : Fin n → ℝ
  p0 : Fin n → ℝ
  αbar : ℝ
  c : ℝ → ℝ

def IsDist {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

def Model.Standing {n : ℕ} (M : Model n) : Prop :=
  IsDist M.pH ∧ IsDist M.pL ∧ IsDist M.p0 ∧
  0 < M.αbar ∧ M.αbar ≤ 1 ∧
  (∀ i, 0 < M.l i) ∧
  (∀ i, M.l i < M.αbar * M.v i) ∧
  (∑ i, M.pL i * M.v i) < (∑ i, M.p0 i * M.v i) ∧
  (∑ i, M.p0 i * M.v i) < (∑ i, M.pH i * M.v i) ∧
  ContDiffOn ℝ 2 M.c (Set.Iio 1) ∧
  MonotoneOn M.c (Set.Ico 0 1) ∧
  ConvexOn ℝ (Set.Ico 0 1) M.c ∧
  deriv M.c 0 = 0 ∧
  Filter.Tendsto (deriv M.c) (nhdsWithin 1 (Set.Iio 1)) Filter.atTop

def payU {n : ℕ} (M : Model n) (i : Fin n) (qθ α ζ : ℝ) : ℝ :=
  (1 - ζ) * α * M.v i + ζ * (qθ * M.αbar * M.v i - M.l i)

def payD {n : ℕ} (M : Model n) (i : Fin n) (qθ α ζ : ℝ) : ℝ :=
  (1 - ζ) * (1 - α) * M.v i + ζ * ((1 - qθ * M.αbar) * M.v i - M.l i)

def IsHybridAt {n : ℕ} (M : Model n) (lam : ℝ) (i : Fin n) : Prop :=
  M.l i ≤ (1 - lam) * M.αbar * M.v i

def zt {n : ℕ} (M : Model n) (i : Fin n) : ℝ :=
  (M.αbar * M.v i - M.l i) / (M.αbar * M.v i + M.l i)

noncomputable def yOf {n : ℕ} (M : Model n) (lam : ℝ) (i : Fin n) : ℝ :=
  by classical exact if IsHybridAt M lam i then lam / (1 - lam) * (M.l i / (M.αbar * M.v i - M.l i)) else 1

noncomputable def zOf {n : ℕ} (M : Model n) (lam : ℝ) (i : Fin n) : ℝ :=
  by classical exact if IsHybridAt M lam i then zt M i else 0

def lamC {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : ℝ :=
  xh * M.pH i / (xh * M.pH i + (1 - β) * (1 - xh) * M.p0 i)

def IsHybrid {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : Prop :=
  IsHybridAt M (lamC M β xh i) i

noncomputable def hybridSet {n : ℕ} (M : Model n) (β xh : ℝ) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (IsHybrid M β xh ·)

noncomputable def yAt {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : ℝ :=
  yOf M (lamC M β xh i) i

noncomputable def zAt {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : ℝ :=
  zOf M (lamC M β xh i) i

noncomputable def revH {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : ℝ :=
  payU M i 1 M.αbar (zAt M β xh i)

noncomputable def revL {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : ℝ :=
  yAt M β xh i * payU M i 0 M.αbar (zAt M β xh i) +
  (1 - yAt M β xh i) * payU M i 0 (M.l i / M.v i) 0

noncomputable def surpH {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : ℝ :=
  payU M i 1 M.αbar (zAt M β xh i) + payD M i 1 M.αbar (zAt M β xh i)

noncomputable def surpL {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : ℝ :=
  yAt M β xh i * (payU M i 0 M.αbar (zAt M β xh i) + payD M i 0 M.αbar (zAt M β xh i)) +
  (1 - yAt M β xh i) * (payU M i 0 (M.l i / M.v i) 0 + payD M i 0 (M.l i / M.v i) 0)

noncomputable def piH {n : ℕ} (M : Model n) (β xh : ℝ) : ℝ :=
  ∑ i, M.pH i * revH M β xh i

noncomputable def piL {n : ℕ} (M : Model n) (β xh : ℝ) : ℝ :=
  (1 - β) * ∑ i, M.p0 i * revL M β xh i

noncomputable def wH {n : ℕ} (M : Model n) (β xh : ℝ) : ℝ :=
  ∑ i, M.pH i * surpH M β xh i

noncomputable def wL {n : ℕ} (M : Model n) (β xh : ℝ) : ℝ :=
  ∑ i, M.p0 i * (β * M.v i + (1 - β) * surpL M β xh i)

noncomputable def welfare {n : ℕ} (M : Model n) (β x : ℝ) : ℝ :=
  x * wH M β x + (1 - x) * wL M β x - M.c x

def privateWedge {n : ℕ} (M : Model n) (S : Finset (Fin n)) (β : ℝ) : ℝ :=
  (∑ i ∈ S, M.pH i * (M.αbar * M.v i - zt M i * M.l i)) +
  (∑ i ∈ Finset.univ \ S, M.pH i * (M.αbar * M.v i)) -
  (1 - β) * ((∑ i ∈ S, M.p0 i * M.l i) +
    (∑ i ∈ Finset.univ \ S, M.p0 i * (M.αbar * M.v i)))

def socialWedge {n : ℕ} (M : Model n) (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, M.pH i * (M.v i - 2 * zt M i * M.l i *
    (M.αbar * M.v i / (M.αbar * M.v i - M.l i)))) +
  (∑ i ∈ Finset.univ \ S, M.pH i * M.v i) -
  ((∑ i ∈ S, M.p0 i * M.v i) + (∑ i ∈ Finset.univ \ S, M.p0 i * M.v i))

noncomputable def IsEqEffort {n : ℕ} (M : Model n) (β x : ℝ) : Prop :=
  0 < x ∧ x < 1 ∧ piH M β x - piL M β x = deriv M.c x

def Eq4 {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) : Prop :=
  (1 - β) * (1 - xh) * M.p0 i * (M.αbar * M.v i - M.l i) =
    xh * M.pH i * M.l i

end
end EssCheck.Accuracy


