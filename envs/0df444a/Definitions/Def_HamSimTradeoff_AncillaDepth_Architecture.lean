-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Architecture
-- name    : HamSimTradeoff_AncillaDepth_Architecture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:37.440803+00:00
-- url     : https://prove2.me/theorems/fb4fc5c0-194a-4b2a-b8c4-edc8dd7b2636
-- title:
--   Coherent Suzuki circuits, controller amplitude, and normalized depth
-- statement:
--   An architecture $B$ has integers $k,s\ge1$, $a\ge0$, branch count $R=2^a$, positive integers $m_{\ell r}$, and unitary $R\times R$ controllers $V_0,\ldots,V_s$. It is fixed independently of the system dimension and decomposition. For real $t$, define
--   $$P_\ell(t)=\sum_{r=1}^{R}|r\rangle\langle r|\otimes S_{2k}\!\left(\frac{t}{sm_{\ell r}}\right)^{m_{\ell r}},\quad W(t)=(V_s\otimes I)P_s(t)\cdots(V_1\otimes I)P_1(t)(V_0\otimes I).$$
--   The compressed system operator, ideal amplitude, and normalized depth are
--   $$C(t)=(\langle0^a|\otimes I)W(t)(|0^a\rangle\otimes I),\quad \eta=\langle0^a|V_s\cdots V_0|0^a\rangle,\quad Q=5^{k-1}\sum_{\ell=1}^{s}\max_r m_{\ell r}.$$
--   For a fixed $L$, uniform approximation with error $\varepsilon$ means $\|C(t)-\eta U_A(t)\|\le\varepsilon$ for every positive system dimension, every admissible $L$-term decomposition, and every real $|t|\le1$. This predicate expresses the source's Hamiltonian-independent accuracy requirement.
--
--   **Formalization Note** The ancilla coordinate comes first in the tensor product. Compression takes its $(0,0)$ block. Multiplexing is written directly as diagonal blocks, exactly equal to the projector sum. The finite maximum is `Finset.sup` over all branches, a nonempty set even at $a=0$. The exact expression for $Q$ selects the representative of the source's $\Theta$ definition. All matrix norms are spectral norms.
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), pp.4–5, Eqs. (1.5)–(1.8) and standing convention above (1.7)

import Definitions.Def_HamSimTradeoff_AncillaDepth_Suzuki
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth
noncomputable section

/-- The architecture is independent of the system dimension, weights and Hamiltonian matrices. -/
structure Architecture where
  k : ℕ
  s : ℕ
  a : ℕ
  k_pos : 1 ≤ k
  s_pos : 1 ≤ s
  m : Fin s → Fin (2 ^ a) → ℕ
  m_pos : ∀ ell r, 0 < m ell r
  V : Fin (s + 1) → Matrix.unitaryGroup (Fin (2 ^ a)) ℂ

def ancillaZero (a : ℕ) : Fin (2 ^ a) := ⟨0, by positivity⟩

def controller (B : Architecture) (j : Fin (B.s + 1)) : Mat (2 ^ B.a) := B.V j

def controllerProduct (B : Architecture) : Mat (2 ^ B.a) :=
  ((List.finRange (B.s + 1)).reverse.map (controller B)).prod

def eta (B : Architecture) : ℂ := controllerProduct B (ancillaZero B.a) (ancillaZero B.a)

/-- Exact representative of the Θ-expression in (1.7); Finset.sup is the finite maximum. -/
def depth (B : Architecture) : ℝ :=
  (5 : ℝ) ^ (B.k - 1) * ∑ ell : Fin B.s, ((Finset.univ.sup (B.m ell) : ℕ) : ℝ)

/-- (1.6) written as its diagonal blocks, ancilla index first. -/
def multiplex {L d : ℕ} (B : Architecture) (alpha : Fin L → ℝ) (H : Fin L → Mat d)
    (ell : Fin B.s) (t : ℝ) : Matrix (Fin (2 ^ B.a) × Fin d) (Fin (2 ^ B.a) × Fin d) ℂ :=
  fun i j => if i.1 = j.1 then
    (suzuki B.k alpha H (t / ((B.s : ℝ) * B.m ell i.1)) ^ B.m ell i.1) i.2 j.2 else 0

def circuit {L d : ℕ} (B : Architecture) (alpha : Fin L → ℝ) (H : Fin L → Mat d) (t : ℝ) :
    Matrix (Fin (2 ^ B.a) × Fin d) (Fin (2 ^ B.a) × Fin d) ℂ :=
  ((List.finRange B.s).reverse.map (fun ell =>
    Matrix.kronecker (controller B ⟨ell.val + 1, by omega⟩) (1 : Mat d) *
      multiplex B alpha H ell t)).prod *
    Matrix.kronecker (controller B ⟨0, by have := B.s_pos; omega⟩) (1 : Mat d)

def compression {L d : ℕ} (B : Architecture) (alpha : Fin L → ℝ) (H : Fin L → Mat d)
    (t : ℝ) : Mat d :=
  fun i j => circuit B alpha H t (ancillaZero B.a, i) (ancillaZero B.a, j)

/-- Uniformity includes every positive finite system dimension and every decomposition. -/
def UniformApproximation (B : Architecture) (L : ℕ) (eps : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ D : Decomposition L d, ∀ t : ℝ, |t| ≤ 1 →
    ‖compression B D.alpha D.H t - eta B • evolution (hamiltonian D.alpha D.H) t‖ ≤ eps

end
end HamSimTradeoff.AncillaDepth


