-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
-- name    : OAI_Probability_EntangledGames_SamplingStrategy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:57:40.704138+00:00
-- url     : https://prove2.me/theorems/74acb786-b06b-48c4-b0ee-2c5934cbf635
-- title:
--   POVMs, tensor powers, and the first-success measurement on many copies
-- statement:
--   Let $m,n$ be finite index sets and $A$ a finite set of outcomes. For complex matrices, $X^*$ is the conjugate transpose, $\otimes$ the Kronecker product, and $X\le Y$ the Loewner order ($Y-X$ positive semidefinite).
--
--   1. **POVM.** A POVM on $\mathbb{C}^n$ with outcomes in $A$ is a family $P=(P_a)_{a\in A}$ of positive semidefinite $n\times n$ matrices with $\sum_aP_a=I$.
--   2. **Constant POVM.** For $a_0\in A$, $P^{(a_0)}_a=I$ if $a=a_0$ and $0$ otherwise: the measurement that always outputs $a_0$.
--   3. **Pull-back by a matrix.** For a POVM $P$ on $\mathbb{C}^m$ and $K\in\mathbb{C}^{m\times n}$, the family $(K^*P_aK)_{a\in A}$ of $n\times n$ matrices. Each $K^*P_aK$ is positive semidefinite and $\sum_aK^*P_aK=K^*K$.
--   4. **Copies and tensor powers.** The index set $n^{(t)}$ of the $t$-fold tensor power is defined by $n^{(0)}=\{\ast\}$ (one point) and $n^{(t+1)}=n\times n^{(t)}$; it is finite, has decidable equality, and is nonempty when $n$ is. For $D\in\mathbb{C}^{m\times n}$, $D^{\otimes 0}$ is the $1\times 1$ matrix $(1)$ and $D^{\otimes(t+1)}=D\otimes D^{\otimes t}$.
--   5. **First-success measurement.** Given a POVM $P$ on $\mathbb{C}^m$, a matrix $K\in\mathbb{C}^{m\times n}$ with $K^*K\le I$, and a default outcome $a_0\in A$, the POVM $F^{(t)}$ on $(\mathbb{C}^n)^{\otimes t}$ with outcomes in $A$ is defined by $F^{(0)}=P^{(a_0)}$ and
--   $$F^{(t+1)}_a=K^*P_aK\otimes I+(I-K^*K)\otimes F^{(t)}_a .$$
--   Unrolled, $F^{(t)}_a=\sum_{r=1}^{t}(I-K^*K)^{\otimes(r-1)}\otimes K^*P_aK\otimes I^{\otimes(t-r)}+[a=a_0]\,(I-K^*K)^{\otimes t}$: the copies are examined in order with the two-outcome test $\{K^*K,\,I-K^*K\}$; at the first copy where the test succeeds, the outcome of $P$ applied after the filter $K$ is reported, and if all $t$ tests fail the default $a_0$ is reported. Positivity of the effects uses $K^*K\le I$; that they sum to $I$ follows from item 3.
--   6. **Payoff.** For $C\in\mathbb{C}^{m\times n}$, encoding the vector $\operatorname{vec}(C)$ with $\operatorname{vec}(C)_{(i,j)}=C_{ij}$, POVMs $P$ on $\mathbb{C}^m$ and $Q$ on $\mathbb{C}^n$ with outcome sets $A$ and $B$, and an acceptance predicate $V:A\times B\to\{\text{true},\text{false}\}$,
--   $$\operatorname{payoff}(C,P,Q,V)=\sum_{a\in A}\sum_{b\in B}[V(a,b)]\,\operatorname{Re}\bigl\langle\operatorname{vec}(C),(P_a\otimes Q_b)\operatorname{vec}(C)\bigr\rangle .$$
--
--   The file also records that Kronecker products distribute over finite sums in each factor, and that the Born weight $\operatorname{Re}\langle\operatorname{vec}(C),(A\otimes B)\operatorname{vec}(C)\rangle$ is additive over finite sums in $A$ and in $B$.
--
--   These are the ingredients of a sampling strategy: the players share many copies of a resource state (a tensor power), each applies a local filter copy by copy and answers at the first success. The payoff is the winning probability of the measurements $P,Q$ on the possibly unnormalized state $C$ for one question pair with acceptance predicate $V$.
--
--   **Formalization Note** `POVM n A` is a structure with fields `effect`, `pos` and `total`. `Copies n t` is defined by recursion on `t` with `Copies n 0 = Unit`; `tensorPower` and `firstSuccess` follow the same recursion, the new copy being the left Kronecker factor. `firstSuccess` takes the hypothesis `hK : Kᴴ * K ≤ 1` as an argument. The lemmas `kronecker_sum_left`, `kronecker_sum_right`, `prob_sum_left` and `prob_sum_right` are bookkeeping.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/SamplingStrategy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SamplingStrategy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters

namespace OAI

universe u_n u_A u_m u_ι u_p u_q u_B

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker

noncomputable section
namespace ThresholdParallelRepetition.QuantumSampling

structure POVM (n : Type u_n) (A : Type u_A) [Fintype n] [DecidableEq n] [Fintype A] where
  effect : A → Matrix n n ℂ
  pos : ∀ a, (effect a).PosSemidef
  total : ∑ a, effect a = 1

variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A]

def POVM.default (a₀ : A) : POVM n A := by
  classical
  exact { effect := fun a => if a = a₀ then 1 else 0
          pos := fun a => by split <;> first | exact Matrix.PosSemidef.one | exact Matrix.PosSemidef.zero
          total := by simp }

def POVM.pull (P : POVM m A) (K : Matrix m n ℂ) (a : A) : Matrix n n ℂ :=
  Kᴴ * P.effect a * K

omit [DecidableEq n] in
lemma POVM.pull_pos (P : POVM m A) (K : Matrix m n ℂ) (a : A) :
    (P.pull K a).PosSemidef := (P.pos a).conjTranspose_mul_mul_same K
omit [Fintype n] [DecidableEq n] in
lemma POVM.pull_sum (P : POVM m A) (K : Matrix m n ℂ) :
    ∑ a, P.pull K a = Kᴴ * K := by
  simp only [POVM.pull, ← Matrix.sum_mul, ← Matrix.mul_sum, P.total, Matrix.mul_one]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma kronecker_sum_left {ι : Type u_ι} [Fintype ι] (M : ι → Matrix m m ℂ)
    (N : Matrix n n ℂ) : (∑ i, M i) ⊗ₖ N = ∑ i, M i ⊗ₖ N := by
  ext i j; simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]
omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma kronecker_sum_right {ι : Type u_ι} [Fintype ι] (M : Matrix m m ℂ)
    (N : ι → Matrix n n ℂ) : M ⊗ₖ (∑ i, N i) = ∑ i, M ⊗ₖ N i := by
  ext i j; simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

@[reducible] def Copies (n : Type) : ℕ → Type
  | 0 => Unit
  | t+1 => n × Copies n t
instance copiesFintype {n : Type} [Fintype n] : (t : ℕ) → Fintype (Copies n t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t+1 => by
    letI := copiesFintype (n := n) t
    exact inferInstanceAs (Fintype (n × Copies n t))
instance copiesDecidableEq {n : Type} [DecidableEq n] : (t : ℕ) → DecidableEq (Copies n t)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | t+1 => @instDecidableEqProd n (Copies n t) _ (copiesDecidableEq t)
instance copiesNonempty {n : Type} [Nonempty n] : (t : ℕ) → Nonempty (Copies n t)
  | 0 => inferInstanceAs (Nonempty Unit)
  | t+1 => by
    let := copiesNonempty (n := n) t
    exact inferInstanceAs (Nonempty (n × Copies n t))

def tensorPower {m n : Type} (D : Matrix m n ℂ) : (t : ℕ) → Matrix (Copies m t) (Copies n t) ℂ
  | 0 => fun _ _ => 1
  | t+1 => D ⊗ₖ tensorPower D t

def firstSuccess {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Type} [Fintype A] (P : POVM m A) (K : Matrix m n ℂ)
    (hK : Kᴴ*K ≤ 1) (a₀ : A) : (t : ℕ) → POVM (Copies n t) A
  | 0 => POVM.default a₀
  | t+1 => {
      effect := fun a => P.pull K a ⊗ₖ 1 + (1-Kᴴ*K) ⊗ₖ (firstSuccess P K hK a₀ t).effect a
      pos := fun a => ((P.pull_pos K a).kronecker Matrix.PosSemidef.one).add
        ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK)).kronecker
          ((firstSuccess P K hK a₀ t).pos a))
      total := by
        rw [Finset.sum_add_distrib, ← kronecker_sum_left, ← kronecker_sum_right,
          P.pull_sum, (firstSuccess P K hK a₀ t).total, ← Matrix.add_kronecker]
        simp only [add_sub_cancel, Matrix.one_kronecker_one] }

lemma prob_sum_left {m : Type u_m} {n : Type u_n} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype ι]
    (C : Matrix m n ℂ) (A : ι → Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (∑ i, A i) B = ∑ i, prob C (A i) B := by
  simp only [prob, eval_eq_trace, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
lemma prob_sum_right {m : Type u_m} {n : Type u_n} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype ι]
    (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : ι → Matrix n n ℂ) :
    prob C A (∑ i, B i) = ∑ i, prob C A (B i) := by
  simp only [prob, eval_eq_trace, Matrix.transpose_sum, Matrix.mul_sum,
    Matrix.trace_sum, Complex.re_sum]

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]

def payoff (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) : ℝ :=
  ∑ a, ∑ b, if V a b then prob C (P.effect a) (Q.effect b) else 0
end Payoff

section FilterMass
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

end FilterMass

open Filter Topology
end ThresholdParallelRepetition.QuantumSampling

end

end OAI


