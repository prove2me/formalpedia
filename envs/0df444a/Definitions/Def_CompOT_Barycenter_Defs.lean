-- Prove2me | Definitions.Def_CompOT_Barycenter_Defs
-- name    : CompOT_Barycenter_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:08.448017+00:00
-- url     : https://prove2.me/theorems/0f330c14-b789-49df-938d-0be217f5281e
-- title:
--   Entropic transport, KL projection, and barycenter dual objectives, (4.1), (4.6), (9.15)–(9.21)
-- statement:
--   Fix a finite set of source histograms $b_s$ with weights $\lambda_s$, a candidate barycenter supported on $n$ sites, a cost matrix $C_s$ for each source, and a regularization parameter $\varepsilon>0$. A family of coupling matrices $(P_s)_s$ is feasible when each matrix is nonnegative, has column marginal $b_s$, and all matrices have the same row marginal. That common marginal is the barycenter histogram.
--
--   The **generalized matrix KL divergence** uses the summand $r\log(r/k)-r+k$ for $r>0$ and $k$ for $r=0$. The Gibbs kernel is $K_{s,ij}=\exp(-C_{s,ij}/\varepsilon)$. The KL barycenter objective and the corresponding entropic transport objective are, respectively,
--   $$\sum_s\lambda_s\varepsilon\,\mathrm{KL}(P_s\mid K_s),\qquad \sum_s\lambda_s\bigl(\langle C_s,P_s\rangle-\varepsilon H(P_s)\bigr),$$
--   where $H(P)=\sum_{i,j}(-P_{ij}\log P_{ij}+P_{ij})$ and $0\log0=0$. An optimal KL barycenter minimizes the first expression over feasible families.
--
--   The dual potentials $(f_s,g_s)_s$ satisfy $\sum_s\lambda_s f_s=0$ coordinatewise. Their objective is
--   $$\sum_s\lambda_s\left[\langle g_s,b_s\rangle-\varepsilon\sum_{i,j}e^{f_{s,i}/\varepsilon}K_{s,ij}e^{g_{s,j}/\varepsilon}\right].$$
--   The definitions also give the single-source $g_s$ block objective and its logarithmic update. Together they provide a reusable finite-dimensional interface for the barycenter duality claim.
--
--   **Formalization Note** Indices are zero based `Fin` types. The entropy convention is used only on nonnegative feasible couplings. The optimality predicates include feasibility and quantify over every feasible competitor; they do not assume an optimizer exists.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (4.1), p. 425; (4.6), p. 428; (9.15)–(9.21), pp. 529–530

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs

namespace CompOT.Barycenter

/-- The matrix pairing used in (2.11) and (9.15). -/
noncomputable def pairing {n m : ℕ} (C P : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, C i j * P i j

/-- The objective of the entropic transport problem (4.2). -/
noncomputable def entropicObjective {n m : ℕ}
    (ε : ℝ) (C P : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  pairing C P - ε * CompOT.EntropicLimit.entropy P

/-- The Gibbs kernel of (9.16), `K = exp (-C/ε)` entrywise. -/
noncomputable def gibbs {n m : ℕ} (ε : ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  Real.exp (-C i j / ε)

/-- One summand of generalized KL (4.6), with `0 log 0 = 0`. -/
noncomputable def klEntry (r k : ℝ) : ℝ :=
  if r = 0 then k else r * Real.log (r / k) - r + k

/-- Generalized KL divergence on matrices as in (4.6). -/
noncomputable def klMatrix {n m : ℕ}
    (P K : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, klEntry (P i j) (K i j)

/-- Feasibility in (9.16): nonnegative matrices, prescribed column marginals,
and the same row marginal for every source. -/
def BarycenterFeasible {S n : ℕ} (ns : Fin S → ℕ)
    (b : (s : Fin S) → Fin (ns s) → ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) : Prop :=
  (∀ s i j, 0 ≤ P s i j) ∧
  (∀ s j, ∑ i, P s i j = b s j) ∧
  (∀ s t i, (∑ j, P s i j) = ∑ j, P t i j)

/-- The weighted objective minimized in the KL projection (9.16). -/
noncomputable def barycenterKLObjective {S n : ℕ} (ns : Fin S → ℕ)
    (ε : ℝ) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (weights : Fin S → ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) : ℝ :=
  ∑ s, weights s * ε * klMatrix (P s) (gibbs ε (C s))

/-- The weighted entropic objective in (9.15), evaluated at couplings with
a shared row marginal. -/
noncomputable def barycenterPrimalObjective {S n : ℕ} (ns : Fin S → ℕ)
    (ε : ℝ) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (weights : Fin S → ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) : ℝ :=
  ∑ s, weights s * entropicObjective ε (C s) (P s)

/-- A solution of the KL projection (9.16). -/
def IsBarycenterKLOptimal {S n : ℕ} (ns : Fin S → ℕ)
    (ε : ℝ) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ) (weights : Fin S → ℝ)
    (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ) : Prop :=
  BarycenterFeasible ns b P ∧
    ∀ Q, BarycenterFeasible ns b Q →
      barycenterKLObjective ns ε C weights P ≤ barycenterKLObjective ns ε C weights Q

/-- The linear constraint on the potentials in (9.21). -/
def DualFeasible {S n : ℕ} (weights : Fin S → ℝ)
    (f : Fin S → Fin n → ℝ) : Prop :=
  ∀ i, (∑ s, weights s * f s i) = 0

/-- The objective of the barycenter dual program (9.21). -/
noncomputable def barycenterDualObjective {S n : ℕ} (ns : Fin S → ℕ)
    (ε : ℝ) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ) (weights : Fin S → ℝ)
    (f : Fin S → Fin n → ℝ) (g : (s : Fin S) → Fin (ns s) → ℝ) : ℝ :=
  ∑ s, weights s * ((∑ j, g s j * b s j) -
    ε * ∑ i, ∑ j, Real.exp (f s i / ε) * gibbs ε (C s) i j *
      Real.exp (g s j / ε))

/-- An attained maximum of (9.21). -/
def IsBarycenterDualOptimal {S n : ℕ} (ns : Fin S → ℕ)
    (ε : ℝ) (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ) (weights : Fin S → ℝ)
    (f : Fin S → Fin n → ℝ) (g : (s : Fin S) → Fin (ns s) → ℝ) : Prop :=
  DualFeasible weights f ∧
    ∀ f' g', DualFeasible weights f' →
      barycenterDualObjective ns ε C b weights f' g' ≤
        barycenterDualObjective ns ε C b weights f g

/-- The part of (9.21) depending on one `g_s`, with `f_s` fixed. -/
noncomputable def gBlockObjective {n m : ℕ} (ε : ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) : ℝ :=
  (∑ j, g j * b j) -
    ε * ∑ i, ∑ j, Real.exp (f i / ε) * gibbs ε C i j *
      Real.exp (g j / ε)

/-- The log-domain column-potential update from (9.18). -/
noncomputable def gBlockUpdate {n m : ℕ} (ε : ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (f : Fin n → ℝ) (j : Fin m) : ℝ :=
  ε * Real.log (b j / (∑ i, gibbs ε C i j * Real.exp (f i / ε)))

end CompOT.Barycenter


