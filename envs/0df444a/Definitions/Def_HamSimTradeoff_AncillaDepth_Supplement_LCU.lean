-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_LCU
-- name    : HamSimTradeoff_AncillaDepth_Supplement_LCU
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:32.813448+00:00
-- url     : https://prove2.me/theorems/73ae6601-d705-48dd-8374-a48de6c3c515
-- title:
--   The repeated-query LCU circuit and effective support
-- statement:
--   A repeated-query circuit stores only $a,T$, the ancilla unitaries $V_0,\ldots,V_T$, and logical labels $\alpha_t\in[L]$, independently of all input unitaries. For a fixed system dimension $N$ define
--   $$U(P)=(V_T\otimes I)C(P_{\alpha_T})\cdots(V_1\otimes I)C(P_{\alpha_1})(V_0\otimes I),\quad B(P)=\langle0^a|U(P)|0^a\rangle,$$
--   where $C(P)=|0^a\rangle\langle0^a|\otimes P+(I-|0^a\rangle\langle0^a|)\otimes I$. The target is $\sum_j\lambda_jP_j$. LCUApprox quantifies over all unitary tuples in this one dimension. ProbabilityWeights means nonnegative weights summing to one; zero weights are permitted. The effective support is $J_\tau=\{j:\lambda_j\ge\tau\}$ and the support is $\{j:\lambda_j>0\}$. The functions $q_r$ and $K_r$ use exactly (1.19) and Lemma 5.7. These interfaces contain no success or lower-bound certificate.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), pp. 8–9, Eqs. (1.16)–(1.19); pp. 23, 26

import Definitions.Def_HamSimTradeoff_AncillaDepth_Architecture
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

/-- Input-independent repeated-query circuit of (1.16). -/
structure LCUCircuit (L : ℕ) where
  a : ℕ
  T : ℕ
  V : Fin (T + 1) → Matrix.unitaryGroup (Fin (2 ^ a)) ℂ
  query : Fin T → Fin L

def zeroProjector (a : ℕ) : Mat (2 ^ a) :=
  fun i j => if i = ancillaZero a ∧ j = ancillaZero a then 1 else 0

def controlled {N : ℕ} (a : ℕ) (P : Mat N) :
    Matrix (Fin (2 ^ a) × Fin N) (Fin (2 ^ a) × Fin N) ℂ :=
  Matrix.kronecker (zeroProjector a) P + Matrix.kronecker (1 - zeroProjector a) 1

def lcuUnitary {L N : ℕ} (B : LCUCircuit L) (P : Fin L → Mat N) :
    Matrix (Fin (2 ^ B.a) × Fin N) (Fin (2 ^ B.a) × Fin N) ℂ :=
  ((List.finRange B.T).reverse.map (fun t =>
    Matrix.kronecker (B.V ⟨t.val + 1, by omega⟩ : Mat (2 ^ B.a)) (1 : Mat N) *
      controlled B.a (P (B.query t)))).prod *
    Matrix.kronecker (B.V ⟨0, by omega⟩ : Mat (2 ^ B.a)) (1 : Mat N)

def successBlock {L N : ℕ} (B : LCUCircuit L) (P : Fin L → Mat N) : Mat N :=
  fun i j => lcuUnitary B P (ancillaZero B.a, i) (ancillaZero B.a, j)

def lcuTarget {L N : ℕ} (lam : Fin L → ℝ) (P : Fin L → Mat N) : Mat N :=
  ∑ j, (lam j : ℂ) • P j

def ProbabilityWeights {L : ℕ} (lam : Fin L → ℝ) : Prop :=
  (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1

/-- One fixed system dimension; every tuple of unitary inputs in that dimension. -/
def LCUApprox {L : ℕ} (B : LCUCircuit L) (N : ℕ) (lam : Fin L → ℝ) (eps : ℝ) : Prop :=
  ∀ P : Fin L → Matrix.unitaryGroup (Fin N) ℂ,
    ‖successBlock B (fun j => (P j : Mat N)) - lcuTarget lam (fun j => (P j : Mat N))‖ ≤ eps

def effectiveSupport {L : ℕ} (lam : Fin L → ℝ) (tau : ℝ) : Finset (Fin L) :=
  Finset.univ.filter (fun j => tau ≤ lam j)

def support {L : ℕ} (lam : Fin L → ℝ) : Finset (Fin L) :=
  Finset.univ.filter (fun j => 0 < lam j)

def qConstant (r : ℝ) : ℝ := (Real.sqrt (4 - 2*r) - Real.sqrt (2*r))/2

def K (r : ℝ) : ℝ := r / (1 - Real.sqrt (r*(2-r))) + Real.sqrt (2*r/(1-r))

end
end HamSimTradeoff.AncillaDepth.Supplement


