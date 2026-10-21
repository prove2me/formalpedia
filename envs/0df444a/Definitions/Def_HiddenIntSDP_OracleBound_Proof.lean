-- Prove2me | Definitions.Def_HiddenIntSDP_OracleBound_Proof
-- name    : HiddenIntSDP_OracleBound_Proof
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:49.093002+00:00
-- url     : https://prove2.me/theorems/4e753057-8030-434b-9c3c-362b4262db67
-- title:
--   Error decomposition and Oracle IP benchmark
-- statement:
--   This module defines the quantities used in the paper's comparison of the SDP error with the Oracle IP error. The realized noise vectors form the rows of $G$, the cluster centers form the rows of $\mathbb EH$, and $\ell=n/k$. The normalized true assignment matrix $U=F^*/\sqrt\ell$ defines the projection $\mathcal P_T(M)=UU^\top M+MUU^\top-UU^\top MUU^\top$. The four terms $S_1,S_2,S_3,S_4$ are exactly the four terms of (16), and $\gamma=\|Y-Y^*\|_1$.
--
--   For each point $j$ and candidate cluster $a$, the module defines $\beta_{ja}=\langle\mu_a-\mu_{\sigma^*(j)},g_j\rangle-\kappa\|\mu_{\sigma^*(j)}-\mu_a\|_2^2$ and the averaged block error $\widehat X_{ja}$. The integer program value $IP_1$ is the maximum number of off-cluster assignments among zero-one arrays with at most one selection per point and nonnegative $\beta$-weighted objective. The Oracle error is
--
--   $$
--   \max\left\{\tfrac12\|F-F^*\|_1:F\in\mathcal F,\ \eta(F)\le\eta(F^*)\right\}.
--   $$
--
--   These two maxima are the quantities identified in Lemma 2. Both defining value sets are nonempty and bounded on the stated model domain.
--
--   **Formalization Note** Both maxima are represented by real suprema; zero selection and $F^*$ provide feasible points, and zero-one constraints bound the objectives by $n$.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, pp. 17–20, §5, (16), (18)–(20), (23)

import Definitions.Def_HiddenIntSDP_OracleBound_Model

namespace HiddenIntSDP.OracleBound

/-- Matrix whose rows are the realized noise vectors. -/
def Gmat {n d : ℕ} (g : Fin n → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin n) (Fin d) ℝ := fun i c => g i c

/-- Matrix whose rows are the cluster centers. -/
def EH {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) : Matrix (Fin n) (Fin d) ℝ :=
  fun i c => mu (sig i) c

/-- Common cluster size ℓ = n/k. -/
noncomputable def ell (n k : ℕ) : ℝ := (n : ℝ) / k

/-- Normalized true assignment matrix from p. 17. -/
noncomputable def U {n k : ℕ} (sig : Fin n → Fin k) :
    Matrix (Fin n) (Fin k) ℝ :=
  (1 / Real.sqrt (ell n k)) • Fstar sig

/-- Tangent-space projection from p. 17. -/
noncomputable def PT {n k : ℕ} (sig : Fin n → Fin k)
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let Q := U sig * (U sig).transpose
  Q * M + M * Q - Q * M * Q

/-- The SDP error γ. -/
def gamma {n k : ℕ} (sig : Fin n → Fin k)
    (Y : Matrix (Fin n) (Fin n) ℝ) : ℝ := l1 (Y - Ystar sig)

/-- The first noise term in (16). -/
noncomputable def S1 {n k d : ℕ} (sig : Fin n → Fin k)
    (g : Fin n → EuclideanSpace ℝ (Fin d))
    (Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  frob (Y - Ystar sig) (PT sig (Gmat g * (Gmat g).transpose))

/-- The second noise term in (16). -/
noncomputable def S2 {n k d : ℕ} (sig : Fin n → Fin k)
    (g : Fin n → EuclideanSpace ℝ (Fin d))
    (Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  let GG := Gmat g * (Gmat g).transpose
  frob (Y - Ystar sig) (GG - PT sig GG)

/-- The mixed term in (16). -/
noncomputable def S3 {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) (g : Fin n → EuclideanSpace ℝ (Fin d))
    (Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  frob (Y - Ystar sig) (Gmat g * (EH mu sig).transpose)

/-- The signal term in (16). -/
noncomputable def S4 {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) (Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  frob (Y - Ystar sig) (EH mu sig * (EH mu sig).transpose)

/-- The coefficient β of (18). -/
noncomputable def beta {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) (g : Fin n → EuclideanSpace ℝ (Fin d))
    (j : Fin n) (a : Fin k) : ℝ :=
  @inner ℝ _ _ (mu a - mu (sig j)) (g j) -
    kappa * ‖mu (sig j) - mu a‖ ^ 2

/-- Averaged off-block error entries, as on p. 19. -/
noncomputable def Xhat {n k : ℕ} (sig : Fin n → Fin k)
    (Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin k) ℝ :=
  fun j a => (1 / ell n k) *
    ∑ i ∈ Finset.univ.filter (fun i => sig i = a), (Y - Ystar sig) j i

/-- The objective in the integer program (23), also the LP (20) objective. -/
noncomputable def ipObj {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) (g : Fin n → EuclideanSpace ℝ (Fin d))
    (X : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∑ j, ∑ a ∈ Finset.univ.filter (fun a => a ≠ sig j), beta mu sig g j a * X j a

/-- The feasible zero-one arrays in (23). Entries with `a = sig j` are irrelevant. -/
def IPFeasible {n k : ℕ} (sig : Fin n → Fin k)
    (X : Matrix (Fin n) (Fin k) ℝ) : Prop :=
  (∀ j a, a ≠ sig j → X j a = 0 ∨ X j a = 1) ∧
  ∀ j, ∑ a ∈ Finset.univ.filter (fun a => a ≠ sig j), X j a ≤ 1

/-- The maximum number of relabeled points in (23). -/
noncomputable def IP1 {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) (g : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup {v : ℝ | ∃ X : Matrix (Fin n) (Fin k) ℝ,
    IPFeasible sig X ∧ 0 ≤ ipObj mu sig g X ∧
    v = ∑ j, ∑ a ∈ Finset.univ.filter (fun a => a ≠ sig j), X j a}

/-- The worst-case Oracle IP error (12), measured in number of misassigned points. -/
noncomputable def oracleErr {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) (g : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup {v : ℝ | ∃ F : Matrix (Fin n) (Fin k) ℝ,
    IsAssignment F ∧ eta mu sig g F ≤ eta mu sig g (Fstar sig) ∧
    v = (1 / 2 : ℝ) * l1 (F - Fstar sig)}

end HiddenIntSDP.OracleBound


