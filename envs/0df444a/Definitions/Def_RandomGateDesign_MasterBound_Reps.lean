-- Prove2me | Definitions.Def_RandomGateDesign_MasterBound_Reps
-- name    : RandomGateDesign_MasterBound_Reps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:05.329986+00:00
-- url     : https://prove2.me/theorems/2bc892b4-98e6-49e6-8890-882ed6e36eb5
-- title:
--   Irreducible unitary blocks and a complete mixed-tensor decomposition
-- statement:
--   A unitary representation $\pi:U(d)\to U(m)$ is irreducible when $m>0$ and its only complex subspaces invariant under every $\pi(U)$ are zero and the whole space. It is nontrivial when some $\pi(U)$ differs from the identity. A moment subrepresentation is given by an isometric intertwiner from $\pi$ into $U\mapsto U^{t,t}$.
--
--   A complete moment decomposition consists of a trivial block and finitely many continuous, irreducible, nontrivial, pairwise inequivalent representations, each with positive multiplicity. Its isometric embeddings have orthogonal ranges, span the entire mixed tensor space, and intertwine the respective actions:
--
--   $$U^{t,t}\simeq 1^{\oplus m_0}\oplus\bigoplus_i\pi_i(U)^{\oplus m_i}.$$
--
--   This structure records an actual unitary equivalence. The completeness condition prevents an empty collection of blocks from certifying a nontrivial tensor representation.
--
--   Weights are taken on the maximal torus of diagonal unitaries $\operatorname{diag}(z_1,\dots,z_d)$, $|z_k|=1$: $\mu\in\mathbb Z^d$ is a weight of $\pi$ when some nonzero $v$ satisfies $\pi(\operatorname{diag}(z))v=\prod_k z_k^{\mu_k}\,v$ for all $z$. For $\mu,\lambda\in\mathbb Z^d$, $\mu\preceq\lambda$ means that $\lambda-\mu$ is a nonnegative integer combination of the simple roots $L_i-L_{i+1}$, i.e. $\sum_k\mu_k=\sum_k\lambda_k$ and $\sum_{k\le j}\mu_k\le\sum_{k\le j}\lambda_k$ for every $j$. A representation has highest weight $\lambda$ (p. 9) when $\lambda$ is a weight and every weight $\mu$ satisfies $\mu\preceq\lambda$.
-- source:
--   Dulian & Sawicki, Matrix concentration inequalities and efficiency of random universal sets of quantum gates, arXiv:2202.05371v3, p. 12, Fact 9 and eq. (22)

import Definitions.Def_RandomGateDesign_MasterBound_Moments

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RandomGateDesign.MasterBound

def IsIrreducible {d m : ℕ} (π : U d →* U m) : Prop :=
  0 < m ∧ ∀ W : Submodule ℂ (Fin m → ℂ),
    (∀ g : U d, ∀ v ∈ W,
      Matrix.mulVec (π g : Matrix (Fin m) (Fin m) ℂ) v ∈ W) → W = ⊥ ∨ W = ⊤

def IsNontrivial {d m : ℕ} (π : U d →* U m) : Prop :=
  ∃ g : U d, π g ≠ 1

def IsMomentSubrep {d m : ℕ} (t : ℕ) (π : U d →* U m) : Prop :=
  ∃ V : Matrix (MIdx d t) (Fin m) ℂ,
    V.conjTranspose * V = 1 ∧
      ∀ g : U d, tensorMoment t (g : Matrix (Fin d) (Fin d) ℂ) * V =
        V * (π g : Matrix (Fin m) (Fin m) ℂ)

/-- `μ ∈ ℤ^d` is a weight of `π`: some nonzero vector `v` satisfies
`π(diag(z₁, …, z_d)) v = (∏ k, z_k ^ μ_k) v` for every diagonal unitary (maximal torus). -/
def IsWeight {d m : ℕ} (π : U d →* U m) (μ : Fin d → ℤ) : Prop :=
  ∃ v : Fin m → ℂ, v ≠ 0 ∧ ∀ (g : U d) (z : Fin d → Circle),
    (g : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal (fun k => (z k : ℂ)) →
      Matrix.mulVec (π g : Matrix (Fin m) (Fin m) ℂ) v = (∏ k : Fin d, (z k : ℂ) ^ μ k) • v

/-- `μ ≤ λ` in the dominance order: `λ - μ` is a nonnegative integer combination of the
simple roots `L_i - L_{i+1}` (equal total sums, partial sums of `μ` below those of `λ`). -/
def WeightLE {d : ℕ} (μ l : Fin d → ℤ) : Prop :=
  (∑ k, μ k = ∑ k, l k) ∧
    ∀ j : Fin d, ∑ k ∈ Finset.Iic j, μ k ≤ ∑ k ∈ Finset.Iic j, l k

/-- `l` is the highest weight of `π`: a weight of `π` above every other weight of `π`. -/
def HasHighestWeight {d m : ℕ} (π : U d →* U m) (l : Fin d → ℤ) : Prop :=
  IsWeight π l ∧ ∀ μ : Fin d → ℤ, IsWeight π μ → WeightLE μ l

structure MomentDecomposition (d t r : ℕ) where
  dim : Fin r → ℕ
  rep : ∀ i : Fin r, U d →* U (dim i)
  rep_continuous : ∀ i, Continuous (fun g : U d => (rep i g : Matrix (Fin (dim i)) (Fin (dim i)) ℂ))
  rep_irreducible : ∀ i, IsIrreducible (rep i)
  rep_nontrivial : ∀ i, IsNontrivial (rep i)
  rep_inequivalent : ∀ i j, i ≠ j →
    ¬ ∃ (W : Matrix (Fin (dim i)) (Fin (dim j)) ℂ)
        (Q : Matrix (Fin (dim j)) (Fin (dim i)) ℂ),
      W * Q = 1 ∧ Q * W = 1 ∧
        (∀ g : U d, (rep i g : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) * W =
          W * (rep j g : Matrix (Fin (dim j)) (Fin (dim j)) ℂ))
  mult : Fin r → ℕ
  mult_pos : ∀ i, 0 < mult i
  m0 : ℕ
  V : ∀ i : Fin r, Fin (mult i) → Matrix (MIdx d t) (Fin (dim i)) ℂ
  V0 : Matrix (MIdx d t) (Fin m0) ℂ
  V_isometry : ∀ i a, (V i a).conjTranspose * V i a = 1
  V0_isometry : V0.conjTranspose * V0 = 1
  V_orthog_same : ∀ i a b, a ≠ b → (V i a).conjTranspose * V i b = 0
  V_orthog_diff : ∀ i j, i ≠ j → ∀ a b,
    (V i a).conjTranspose * V j b = 0
  V0_orthog : ∀ i a, V0.conjTranspose * V i a = 0
  complete : V0 * V0.conjTranspose +
      (∑ i : Fin r, ∑ a : Fin (mult i), V i a * (V i a).conjTranspose) = 1
  intertwine : ∀ i a (g : U d),
    tensorMoment t (g : Matrix (Fin d) (Fin d) ℂ) * V i a =
      V i a * (rep i g : Matrix (Fin (dim i)) (Fin (dim i)) ℂ)
  intertwine0 : ∀ g : U d,
    tensorMoment t (g : Matrix (Fin d) (Fin d) ℂ) * V0 = V0

end RandomGateDesign.MasterBound


