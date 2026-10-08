-- Prove2me | Definitions.Def_TimeInconsLQ_Deterministic_Model
-- name    : TimeInconsLQ_Deterministic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:03.05051+00:00
-- url     : https://prove2.me/theorems/65c7d5a9-76c2-4742-8d10-c13d22019e7b
-- title:
--   §2 — standing assumptions (entrywise encoding) and the componentwise conditional expectation E_t on the shared model of (2.1)–(2.3)
-- statement:
--   This module adds two objects to the shared model of Hu, Jin and Zhou (§2; the data, filtration, admissible controls, states (2.1), cost (2.3), spike (2.4) and Definition 2.1 live in the shared module `TimeInconsLQ.Sufficient.Model`).
--
--   **Standing assumptions** (pp. 3–4), `Standing`: $\mathbb P$ is a probability measure; the deterministic $A$ is measurable and bounded on $[0,T]$; $B,C^j,D^j,Q,R$ are progressively measurable and essentially bounded on $[0,T]\times\Omega$; $b,\sigma^j\in L^2_{\mathcal F}(0,T;\mathbb R^n)$; $Q_s$ and $R_s$ are symmetric for $s\in[0,T]$, with $Q\succeq0$, $R\succeq0$ for $d\mathbb P\otimes ds$-almost every $(\omega,s)$; $G$ and $h$ are symmetric and $G\succeq0$ ($h$ need not be positive semidefinite; $\mu_1$ is arbitrary).
--
--   **Conditional expectation**, `condVec`: for $t\ge0$ and a vector random variable $Y$, $\mathbb E_t[Y]=\mathbb E[Y\mid\mathcal F_t]$, taken componentwise.
--
--   In this mission only `condVec` is used (in condition (3.4)); the scalar deterministic setting of §4 carries its own standing assumptions (`CoeffsStanding`).
--
--   **Formalization Note.** The filtration is the natural (uncompleted) filtration of $W$ from the published substrate `Peng1990_SMP_Stochastic`. "Essentially bounded" and "a.s., a.e." are read $d\mathbb P\otimes ds$-a.e. on $\Omega\times[0,T]$; boundedness of a matrix is entrywise (equivalent to the norm bound of the shared module). `condVec` coincides with the shared module's `condVec`.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, pp. 3–4, standing assumptions of §2

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model

namespace TimeInconsLQ.Deterministic

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n l d : ℕ}

/-- A matrix-valued process `f` is essentially bounded on `[0, T] × Ω`: there is `K` with
`|f(s, ω)ᵢⱼ| ≤ K` for `dP ⊗ ds`-almost every `(ω, s) ∈ Ω × [0, T]`. -/
def EssBdd (M : TimeInconsLQ.Sufficient.Data Ω n l d) {ι κ : Type*} (f : ℝ≥0 → Ω → Matrix ι κ ℝ) : Prop :=
  ∃ K : ℝ, ∀ᵐ z ∂(M.P.prod (volume.restrict (Set.Icc (0 : ℝ) M.T))),
    ∀ i j, |f z.2.toNNReal z.1 i j| ≤ K

/-- The standing assumptions of §2 (pp. 3–4): `P` is a probability measure; `A` is measurable
and bounded on `[0, T]`; `B, Cʲ, Dʲ, Q, R` are progressively measurable and essentially bounded;
`b, σʲ ∈ L²_𝓕(0, T; ℝⁿ)`; `Q` and `R` take symmetric values on `[0, T]`, with `Q ⪰ 0`,
`R ⪰ 0` for `dP ⊗ ds`-a.e. `(ω, s)`; `G, h` are symmetric and `G ⪰ 0`. -/
structure Standing (M : TimeInconsLQ.Sufficient.Data Ω n l d) : Prop where
  prob : IsProbabilityMeasure M.P
  A_meas : ∀ i j, Measurable (fun s => M.A s i j)
  A_bdd : ∃ K : ℝ, ∀ s ≤ M.T, ∀ i j, |M.A s i j| ≤ K
  B_prog : IsStronglyProgressive (TimeInconsLQ.Sufficient.filt M) M.B
  C_prog : ∀ j, IsStronglyProgressive (TimeInconsLQ.Sufficient.filt M) (M.C j)
  D_prog : ∀ j, IsStronglyProgressive (TimeInconsLQ.Sufficient.filt M) (M.D j)
  Q_prog : IsStronglyProgressive (TimeInconsLQ.Sufficient.filt M) M.Q
  R_prog : IsStronglyProgressive (TimeInconsLQ.Sufficient.filt M) M.R
  B_bdd : EssBdd M M.B
  C_bdd : ∀ j, EssBdd M (M.C j)
  D_bdd : ∀ j, EssBdd M (M.D j)
  Q_bdd : EssBdd M M.Q
  R_bdd : EssBdd M M.R
  b_L2 : Peng1990.SMP.L2F (TimeInconsLQ.Sufficient.filt M) M.P M.T M.b
  σ_L2 : ∀ j, Peng1990.SMP.L2F (TimeInconsLQ.Sufficient.filt M) M.P M.T (M.σ j)
  Q_symm : ∀ s ≤ M.T, ∀ ω, (M.Q s ω).IsSymm
  R_symm : ∀ s ≤ M.T, ∀ ω, (M.R s ω).IsSymm
  Q_psd : ∀ᵐ z ∂(M.P.prod (volume.restrict (Set.Icc (0 : ℝ) M.T))),
    (M.Q z.2.toNNReal z.1).PosSemidef
  R_psd : ∀ᵐ z ∂(M.P.prod (volume.restrict (Set.Icc (0 : ℝ) M.T))),
    (M.R z.2.toNNReal z.1).PosSemidef
  G_symm : M.G.IsSymm
  h_symm : M.h.IsSymm
  G_psd : M.G.PosSemidef

/-- The componentwise conditional expectation `E_t[Y] = E[Y | 𝓕_t]` of a vector random
variable. -/
noncomputable def condVec (M : TimeInconsLQ.Sufficient.Data Ω n l d) (t : ℝ≥0) {ι : Type*} (Y : Ω → ι → ℝ) :
    Ω → ι → ℝ :=
  fun ω i => (M.P[fun ω' => Y ω' i | TimeInconsLQ.Sufficient.filt M t]) ω

end TimeInconsLQ.Deterministic


