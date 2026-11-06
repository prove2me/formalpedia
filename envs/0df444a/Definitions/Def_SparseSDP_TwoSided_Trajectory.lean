-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Trajectory
-- name    : SparseSDP_TwoSided_Trajectory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:48.965241+00:00
-- url     : https://prove2.me/theorems/ff6663b9-d4a6-4567-98d3-bfade5923847
-- title:
--   The quantities of §7 read off a run of Algorithm 7
-- statement:
--   Pure functions of the trace of a run, for the statements of §7, with $G_t=rA_{J_t}$ and $H_t=\sum_{\tau<t}G_\tau$:
--
--   1. $\tilde\rho_t=\tilde\psi_t\tilde\psi_t^\top$, $\tilde X_t=R\tilde\rho_t$ (Eq. (247)), $\rho_t=P_{u_t}(\eta_XH_t)$ (Eq. (246)), $\bar X_t=R\bar P(\eta_XH_t)$ (Eq. (248));
--   2. $X^{\mathrm{out}}=T^{-1}\sum_t\tilde X_t$ (Eq. (229)), $z^{\mathrm{out}}=(r/T)\sum_te_{J_t}$ (Eq. (230));
--   3. the payoff vector $[\tilde c_t]_j=\langle A_j,\tilde X_t\rangle$ (Eq. (231));
--   4. the regrets $E_X(T)=R\lambda_{\max}(\sum_tG_t)-\sum_t\langle G_t,\tilde X_t\rangle$ (Eq. (278)) and $E_y(T)=r[\sum_t[\tilde c_t]_{J_t}-\min_j\sum_t[\tilde c_t]_j]$ (Eq. (330)).
--
--   `Alg7Hyp` collects the standing hypotheses of §7: real symmetric $s$-row-sparse matrices with $\|A_j\|\le\omega$ read through the access, $R,r,\omega>0$, $\delta\in(0,1)$ and $1\le s\le d$. `traj` is the trace of a run from the start of the tape.
--
--   **Formalization Note** The trace is a list, and a sum over rounds carries the number $t$ of preceding rounds, so the paper's round index is $t+1$.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §7.2, pp. 47–48; §7.4, pp. 49–50; Eqs. (229)–(231), (236), (246)–(248), (278), (330)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_alg7

open Matrix
open scoped Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

variable {d k : ℕ}

/-- The sum of `f t x` over the rounds `x` of a trace, with `t` the number of preceding rounds (so
the paper's round index is `t + 1`). -/
noncomputable def sumR {β : Type} [AddMonoid β] (rs : List (Round d k))
    (f : ℕ → Round d k → β) : β :=
  (rs.zipIdx.map fun p => f p.2 p.1).sum

/-- The gain `G_t = r A_{J_t}` of round `x`, Algorithm 7, line 9. -/
noncomputable def gain (M : Fin k → Mat d) (r : ℝ) (x : Round d k) : Mat d := r • M x.J

/-- The Hamiltonian after `t` rounds, `H_{t+1} = ∑_{τ ≤ t} G_τ` (Eq. (351), p. 62). -/
noncomputable def Hof (M : Fin k → Mat d) (r : ℝ) (rs : List (Round d k)) (t : ℕ) : Mat d :=
  ((rs.take t).map (gain M r)).sum

/-- `ρ̃_t = ψ̃_t ψ̃_tᵀ`, Eq. (247), p. 49. -/
def rhoTil (x : Round d k) : Mat d := vecMulVec x.ψ x.ψ

/-- `X̃_t = R ψ̃_t ψ̃_tᵀ`, Algorithm 7, line 13. -/
noncomputable def Xtil (R : ℝ) (x : Round d k) : Mat d := R • rhoTil x

/-- `ρ_t = P_{u_t}(η_X H_t)`, Eq. (246), p. 49, for a round with `t` predecessors. -/
noncomputable def rhoEx (M : Fin k → Mat d) (r η : ℝ) (rs : List (Round d k)) (t : ℕ)
    (x : Round d k) : Mat d :=
  Pu (η • Hof M r rs t) x.u

/-- `X̄_t = R P̄(η_X H_t)`, Eq. (248), p. 50. -/
noncomputable def Xmean (M : Fin k → Mat d) (R r η : ℝ) (rs : List (Round d k)) (t : ℕ) : Mat d :=
  R • Pbar (η • Hof M r rs t)

/-- `X^out = T⁻¹ ∑ₜ X̃_t`, Eq. (229), p. 46. -/
noncomputable def Xout (R : ℝ) (rs : List (Round d k)) : Mat d :=
  (1 / (rs.length : ℝ)) • (rs.map (Xtil R)).sum

/-- `z^out = (r/T) ∑ₜ e_{J_t}`, Eq. (230), p. 47. -/
noncomputable def zout (r : ℝ) (rs : List (Round d k)) : Vec k :=
  (r / (rs.length : ℝ)) • (rs.map fun x => (Pi.single x.J 1 : Vec k)).sum

/-- The payoff vector `[c̃_t]ⱼ = ⟨Aⱼ, X̃_t⟩`, Eq. (231), p. 47. -/
noncomputable def cTil (M : Fin k → Mat d) (R : ℝ) (x : Round d k) : Vec k :=
  fun j => hs (M j) (Xtil R x)

/-- The matrix-side regret `E_X(T) = Rλmax(∑ₜ G_t) − ∑ₜ⟨G_t, X̃_t⟩`, Eqs. (236), (278). -/
noncomputable def EX (M : Fin k → Mat d) (R r : ℝ) (rs : List (Round d k)) : ℝ :=
  R * lamMax (rs.map (gain M r)).sum - (rs.map fun x => hs (gain M r x) (Xtil R x)).sum

/-- The constraint-side regret `E_y(T) = r[∑ₜ[c̃_t]_{J_t} − minⱼ ∑ₜ[c̃_t]ⱼ]`, Eqs. (236), (330). -/
noncomputable def Ey [NeZero k] (M : Fin k → Mat d) (R r : ℝ) (rs : List (Round d k)) : ℝ :=
  r * ((rs.map fun x => cTil M R x x.J).sum - minOver fun j => (rs.map fun x => cTil M R x j).sum)

/-- The standing hypotheses of §7 on an instance of Algorithm 7 (§2.5, p. 16; Theorem 7.1, p. 44):
real symmetric `s`-row-sparse matrices with `‖Mⱼ‖ ≤ ω`, read through `acc`, radii `R, r > 0`,
failure parameter `δ ∈ (0, 1)`, and `1 ≤ s ≤ d`.

**Formalization Note.** `c` bounds the cost of a row read, in units of `s`. -/
structure Alg7Hyp (M : Fin k → Mat d) (acc : RowAccess d k) (s : ℕ) (c ω R r δ : ℝ) : Prop where
  symm : ∀ j, (M j).IsHermitian
  sparse : ∀ j, RowSparse (M j) s
  norm : ∀ j, ‖M j‖ ≤ ω
  spec : acc.Spec M s c
  ω_pos : 0 < ω
  R_pos : 0 < R
  r_pos : 0 < r
  δ_pos : 0 < δ
  δ_lt : δ < 1
  s_pos : 1 ≤ s
  s_le : s ≤ d

/-- The rounds of a run of Algorithm 7 from the start of the tape. -/
noncomputable def traj [NeZero d] [NeZero k] (P : Consts) (acc : RowAccess d k) (s : ℕ)
    (ω R r : ℝ) (T : ℕ) (δ : ℝ) (tape : Tape) : List (Round d k) :=
  (runVal (alg7 P acc s ω R r T δ) tape).rounds

end SparseSDP.TwoSided


