-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Model
-- name    : BauerleRiederMDP_LQ_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:29.676456+00:00
-- url     : https://prove2.me/theorems/5ac26088-71c3-4bab-8947-c38fd80c5938
-- title:
--   The stochastic linear-quadratic problem with random coefficients, its standing assumptions and its minimal cost $V_n$
-- statement:
--   Fix dimensions $m,d$ and a horizon $N$. The **stochastic linear-quadratic problem** has state space $E=\mathbb R^m$, action space $A=\mathbb R^d=D_n(x)$ (every action is admissible) and system equation
--   $$
--   X_{n+1}=A_{n+1}X_n+B_{n+1}a_n,\qquad n=0,\dots,N-1,
--   $$
--   where the disturbance $Z_{n+1}=(A_{n+1},B_{n+1})$ takes values in $\mathbb R^{(m,m)}\times\mathbb R^{(m,d)}$ and has law $\nu_{n+1}$. The one-stage reward is $r_n(x,a)=-x^\top Q_nx$, the terminal reward $g_N(x)=-x^\top Q_Nx$, and there is no discounting.
--
--   The **standing assumptions** of the section are:
--
--   1. $Q_0,\dots,Q_N$ are deterministic, symmetric and positive definite;
--   2. the random matrices have finite expectation and covariance: every entry of $A_k$ and of $B_k$ is square integrable, $k=1,\dots,N$;
--   3. $\mathbb E[B_{n+1}^\top QB_{n+1}]$ is positive definite for every symmetric positive definite $Q$, $n=0,\dots,N-1$.
--
--   For a Markov policy $\pi=(f_0,\dots,f_{N-1})$ of measurable decision rules $f_n:\mathbb R^m\to\mathbb R^d$, the **expected cost** from state $x$ at time $n$ is
--   $$
--   V_{n\pi}(x)=\mathbb E^\pi_{nx}\Big[\sum_{k=n}^{N}X_k^\top Q_kX_k\Big],
--   $$
--   and the **minimal cost** in the period $[n,N]$ is $V_n(x)=\inf_\pi V_{n\pi}(x)$.
--
--   The module also defines the quadratic form $x^\top Qx$ and the entrywise expectation $\mathbb E[F(A,B)]$ of a matrix-valued function of the random pair.
--
--   **Formalization Note** The problem is an instance of the published general Markov Decision Model (`MDPFinance.Bellman.MarkovDecisionModel`, Definition 2.1.1) whose kernel at time $n$ is the law of $A_{n+1}x+B_{n+1}a$ under $\nu_{n+1}$; the independence of $Z_1,Z_2,\dots$ is built into this kernel model. Following Remark 2.3.15 (cost $=$ negative reward), $V_{n\pi}$ and $V_n$ are minus the published expected-reward and value functions `Vpi` and `V` of that model, so $V_n$ is the infimum over all Markov policies of measurable decision rules; values are extended reals. Matrices carry the product σ-algebra of their entries. Mathlib's `PosDef` over $\mathbb R$ includes symmetry. Matrix expectations are Bochner integrals, genuine under assumption 2.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.6.3, pp.50–51 (PDF 65–66), model and data list; Remark 2.3.15, pp.27–28 (PDF 42–43), minimizing cost; §2.2, p.18 (PDF 33), V_{nπ} and V_n

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_BauerleRiederMDP_LQ_DisturbanceKernel

open MeasureTheory ProbabilityTheory Matrix

namespace BauerleRiederMDP.LQ

/-- The measurable space on real matrices: the product σ-algebra of the entries (Mathlib has no
`MeasurableSpace (Matrix m n α)` instance, `Matrix m n α` being a plain `def` for `m → n → α`).
It is needed so that the random coefficient matrices `(A_{n+1}, B_{n+1})` of §2.6.3 have a law. -/
instance instMeasurableSpaceMatrix {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))

/-- The quadratic form `x^⊤ Q x` of a square matrix `Q` at a vector `x` (Bäuerle & Rieder 2011,
§2.6.3, pp.50–52, PDF 65–67). -/
def quadForm {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (Q *ᵥ x)

/-- The expectation `𝔼[F(A, B)]` of a matrix-valued function of the random coefficient pair
`(A, B) ∼ μ`, taken entrywise: `(𝔼[F(A,B)])_{ij} = ∫ F(A,B)_{ij} dμ` (Bäuerle & Rieder 2011, §2.6.3,
pp.50–52, PDF 65–67, notation `𝔼[A_{n+1}^⊤ Q B_{n+1}]` etc.).

**Formalization Note.** A Bochner integral; it is a genuine expectation whenever the entries of
`F(A,B)` are integrable, which the standing assumption `LQData.Standing` (square-integrable entries
of `A`, `B`) guarantees for every `F` used in this mission (products `Aᵀ Q A`, `Aᵀ Q B`, `Bᵀ Q B`,
`Bᵀ Q A` with deterministic `Q`). -/
noncomputable def matExp {m d k l : ℕ}
    (μ : Measure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ))
    (F : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ → Matrix (Fin k) (Fin l) ℝ) :
    Matrix (Fin k) (Fin l) ℝ :=
  Matrix.of fun i j => ∫ z, F z i j ∂μ

/-- The linear transition function `T_n(x, a, A, B) := A x + B a` (Bäuerle & Rieder 2011, §2.6.3,
p.50, PDF 65). -/
def lqTransition {m d : ℕ} (x : Fin m → ℝ) (a : Fin d → ℝ)
    (z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ) : Fin m → ℝ :=
  z.1 *ᵥ x + z.2 *ᵥ a

lemma measurable_lqTransition {m d : ℕ} :
    Measurable (fun p : ((Fin m → ℝ) × (Fin d → ℝ)) ×
        (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ) =>
      lqTransition p.1.1 p.1.2 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  simp only [lqTransition, Pi.add_apply, mulVec, dotProduct]
  refine Measurable.add (Finset.measurable_sum _ fun j _ => ?_)
    (Finset.measurable_sum _ fun j _ => ?_)
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_fst.comp measurable_snd))).mul
      ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_snd.comp measurable_snd))).mul
      ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst))

lemma measurable_quadForm {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (fun x : Fin m → ℝ => quadForm Q x) := by
  have : Continuous (fun x : Fin m → ℝ => quadForm Q x) := by
    unfold quadForm
    fun_prop
  exact this.measurable

lemma measurable_neg_quadForm_fst {m d : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (fun xa : (Fin m → ℝ) × (Fin d → ℝ) => -quadForm Q xa.1) :=
  ((measurable_quadForm Q).comp measurable_fst).neg

/-- **The data of the stochastic linear-quadratic problem** (Bäuerle & Rieder 2011, §2.6.3,
pp.50–51, PDF 65–66): state space `E := ℝ^m`, action space `A := ℝ^d = D_n(x)`, horizon `N`.

* `ν k` is the joint law of the random coefficient pair `Z_k = (A_k, B_k)` with values in
  `𝒵 := ℝ^{(m,m)} × ℝ^{(m,d)}`, `k = 1, …, N` (only these indices are used);
* `Q k` is the deterministic cost matrix `Q_k`, `k = 0, …, N`.

The book's assumptions on these data are `LQData.Standing`. -/
structure LQData (m d N : ℕ) where
  /-- `ν k` = distribution of `Z_k := (A_k, B_k)`. -/
  ν : ℕ → ProbabilityMeasure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ)
  /-- The cost matrices `Q_0, …, Q_N`. -/
  Q : ℕ → Matrix (Fin m) (Fin m) ℝ

namespace LQData

variable {m d N : ℕ}

/-- **The standing assumptions of §2.6.3** (Bäuerle & Rieder 2011, pp.50–51, PDF 65–66):

1. `Q_0, …, Q_N` are deterministic, symmetric and positive definite;
2. the random matrices `Z_k = (A_k, B_k)` "have finite expectation and covariance": every entry of
   `A_k` and of `B_k` is square integrable, `k = 1, …, N`;
3. "`𝔼[B_{n+1}^⊤ Q B_{n+1}]` is positive definite for all symmetric positive definite `Q`",
   `n = 0, …, N − 1`.

**Formalization Note.** Mathlib's `Matrix.PosDef` over `ℝ` includes symmetry (`IsHermitian`).
The independence of `Z_1, Z_2, …` and the fact that the law of `Z_{n+1}` depends neither on the
state nor on the action are built into the Markov Decision Model `toMDP`, whose transition kernel
at time `n` is the law of `A_{n+1} x + B_{n+1} a` under `ν (n+1)`. -/
structure Standing (M : LQData m d N) : Prop where
  posDef_Q : ∀ k ≤ N, (M.Q k).PosDef
  memLp_A : ∀ k, 1 ≤ k → k ≤ N → ∀ i j,
    MemLp (fun z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ => z.1 i j) 2
      (M.ν k : Measure _)
  memLp_B : ∀ k, 1 ≤ k → k ≤ N → ∀ i j,
    MemLp (fun z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ => z.2 i j) 2
      (M.ν k : Measure _)
  posDef_EBQB : ∀ k, 1 ≤ k → k ≤ N → ∀ Q : Matrix (Fin m) (Fin m) ℝ, Q.PosDef →
    (matExp (m := m) (d := d) (M.ν k : Measure _) (fun z => z.2ᵀ * Q * z.2)).PosDef

/-- **The LQ problem as a Markov Decision Model** (Bäuerle & Rieder 2011, §2.6.3, pp.50–51,
PDF 65–66, data list): `E := ℝ^m`, `A := ℝ^d = D_n(x)`, `Q_n(·|x,a)` = law of
`T_n(x, a, A_{n+1}, B_{n+1}) = A_{n+1} x + B_{n+1} a`, one-stage reward `r_n(x,a) := −x^⊤ Q_n x`,
terminal reward `g_N(x) := −x^⊤ Q_N x`, `β := 1`. This is an instance of the general
(non-stationary) Markov Decision Model `MDPFinance.Bellman.MarkovDecisionModel` (Definition 2.1.1). -/
noncomputable def toMDP (M : LQData m d N) :
    MDPFinance.Bellman.MarkovDecisionModel (Fin m → ℝ) (Fin d → ℝ) N where
  D := fun _ => Set.univ
  hD_meas := fun _ _ => MeasurableSet.univ
  hD_sel := fun _ _ => ⟨fun _ => 0, measurable_const, fun _ => Set.mem_univ _⟩
  Q := fun n => disturbanceKernel (E := Fin m → ℝ) (A := Fin d → ℝ)
    (M.ν (n + 1) : Measure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ)) lqTransition
  hQ_prob := fun n _ xa =>
    isProbabilityMeasure_disturbanceKernel
      (M.ν (n + 1) : Measure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ))
      (measurable_lqTransition (m := m) (d := d)) xa
  r := fun n xa => -quadForm (M.Q n) xa.1
  hr_meas := fun n _ => measurable_neg_quadForm_fst (M.Q n)
  g := fun x => -quadForm (M.Q N) x
  hg_meas := (measurable_quadForm (M.Q N)).neg

/-- **The expected cost of a policy** `V_{nπ}(x) = 𝔼^π_{nx}[Σ_{k=n}^{N} X_k^⊤ Q_k X_k]` (Bäuerle &
Rieder 2011, §2.6.3, p.50, PDF 65, and Remark 2.3.15, pp.27–28, PDF 42–43: "We will use the same
notation `V_{nπ}` and `V_n` for the cost functions under policy `π` and the minimal cost function").

**Formalization Note.** By Remark 2.3.15 the cost problem is the reward problem with
`r_n := −c_n`, `g_N := −h_N`; so the expected cost is minus the expected reward
`MDPFinance.Bellman.Vpi` of `toMDP`. It takes values in `[0, ∞]` (`EReal`). -/
noncomputable def VcostPi (M : LQData m d N) (π : MDPFinance.Bellman.Policy M.toMDP) (n : ℕ)
    (x : Fin m → ℝ) : EReal :=
  -MDPFinance.Bellman.Vpi M.toMDP π n x

/-- **The minimal cost** `V_n(x) = inf_π 𝔼^π_{nx}[Σ_{k=n}^{N} X_k^⊤ Q_k X_k]` in the period `[n, N]`
(Bäuerle & Rieder 2011, §2.6.3, p.51, PDF 66: "we suppose that `V_n` is the minimal cost in the
period `[n, N]`"; Remark 2.3.15).

**Formalization Note.** Minus the maximal expected reward `MDPFinance.Bellman.V` of `toMDP`, i.e.
the infimum of `VcostPi` over all Markov policies of measurable decision rules `ℝ^m → ℝ^d`. -/
noncomputable def Vcost (M : LQData m d N) (n : ℕ) (x : Fin m → ℝ) : EReal :=
  -MDPFinance.Bellman.V M.toMDP n x

end LQData

end BauerleRiederMDP.LQ


