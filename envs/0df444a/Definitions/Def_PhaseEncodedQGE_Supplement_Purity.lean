-- Prove2me | Definitions.Def_PhaseEncodedQGE_Supplement_Purity
-- name    : PhaseEncodedQGE_Supplement_Purity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:30:50.73052+00:00
-- url     : https://prove2.me/theorems/3316c9f9-6187-4e56-a39a-2bf6ea87cad1
-- title:
--   Output purity $M_2$, the pair kernel (53), the class kernels $F_{a,k}$ and the closure coefficients $b_3,b_4,b_D$
-- statement:
--   Let $p_G(x;\beta)$ be the Born probabilities of a circuit on a graph $G$ with $n$ vertices.
--
--   1. The **output purity** is $M_2(G;\beta)=\sum_x p_G(x;\beta)^2$, and $M_2''(G;0)$ is its second derivative in $\beta$ at $\beta=0$.
--   2. With $\phi=E\phi_{\mathrm{prep}}$ the pre-mixer amplitude of one repetition, $\phi_i(x)=\phi(x\oplus e_i)$, $\phi_{ij}(x)=\phi(x\oplus e_i\oplus e_j)$, $p_0=|\phi|^2$ and $p_i=\mathrm{Im}(\bar\phi\,\phi_i)$, the **pair kernel** of two vertices $i\ne j$ is
--   $$\sum_x\Big[4p_ip_j+2p_0\,\mathrm{Re}(\phi_i\overline{\phi_j})-2p_0\,\mathrm{Re}(\bar\phi\,\phi_{ij})\Big].$$
--   3. The **local motif** of class $(a,k)$ has two roots, adjacent iff $a=1$, $k$ shared neighbours, $3-a-k$ private neighbours per root and only root-incident edges: $N=8-2a-k$ vertices. Under the product preparation $|\chi(\theta,\varphi)\rangle^{\otimes n}$, $|\chi(\theta,\varphi)\rangle=\cos(\theta/2)|0\rangle+e^{i\varphi}\sin(\theta/2)|1\rangle$, the **class kernel** is
--   $$F_{a,k}=L^{\,n-N}\,K_{a,k},\qquad L=\cos^4(\theta/2)+\sin^4(\theta/2),$$
--   where $K_{a,k}$ is the pair kernel of the two roots of the motif under $|\chi(\theta,\varphi)\rangle^{\otimes N}$.
--   4. With $v_a=F_{a,1}-F_{a,0}$ and $\delta_a=F_{a,2}-2F_{a,1}+F_{a,0}$, the **closure coefficients** are $b_3=3(v_1-v_0)$, $b_4=2\delta_0$, $b_D=\delta_1-\delta_0$.
--
--   On a cubic graph with the degree-aware preparation ($\theta=\eta$, $\varphi=-\pi/2$) or the Hadamard preparation ($\theta=\pi/2$, $\varphi=0$), the pair kernel of a pair of class $(a,k)$ equals $F_{a,k}$: the summand depends only on the spins of the two roots and their neighbours, and each of the other vertices contributes the factor $L$. The class kernels are the coefficients of the second-order purity in the pair census (Lemma B.16), and the closure coefficients are those of Theorem B.17.
--
--   **Formalization Note** Defining $F_{a,k}$ through the motif makes it a single real number for every $n$ and every class, including classes no cubic graph on $n$ vertices realizes, as the closure coefficients require. The exponent $n-N$ is an integer; $L\ge1/2$. The coefficients are functions of $(\theta,\varphi,\gamma,n)$; PE-X1 is $(\theta,\varphi)=(\eta,-\pi/2)$.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §6, p.12 (PDF p.13); App. B.2.4–B.2.6, pp.30–33 (PDF pp.31–34), eqs. (53), (61), (66)–(67), (72), (74)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

open ComplexConjugate

/-- The output purity `M₂(G; β) = ∑_x p_G(x; β)²` (Miller, Lee, *Structural Accessibility in
Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §6, p.12). -/
noncomputable def purity {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ β : ℝ) : ℝ :=
  ∑ x : Outcome n, born prep P r G γ β x ^ 2

/-- The second derivative `M″₂(G; 0)` of the output purity in the mixer angle `β` at `β = 0`
(§6, p.12: "primes denote derivatives in `β` at `β = 0`"). -/
noncomputable def purityCurv {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) : ℝ :=
  iteratedDeriv 2 (fun β => purity prep P r G γ β) 0

/-- The pair kernel of the vertices `i ≠ j` (App. B.2.4, p.30, eq. (53); Lemma B.16, p.31):
`∑_x [4 p_i p_j + 2 p_0 Re(ϕ_i ϕ̄_j) − 2 p_0 Re(ϕ̄ ϕ_ij)]`, where `ϕ = E ϕ_prep` is the pre-mixer
amplitude of one repetition, `ϕ_i(x) = ϕ(x ⊕ e_i)`, `ϕ_ij(x) = ϕ(x ⊕ e_i ⊕ e_j)`,
`p_0 = |ϕ|²` and `p_i = Im(ϕ̄ ϕ_i)`.

**Formalization Note** `ϕ` is the base `preMixer prep 1 G γ`; the overlines are complex
conjugation (`conj`). The formula is (53) as printed, used for adjacent and nonadjacent pairs
alike (Lemma B.16: "the kernel `F_{a,k}` is (53)"). -/
noncomputable def pairKernel {n : ℕ} (prep : Outcome n → ℂ) (G : SimpleGraph (Fin n)) (γ : ℝ)
    (i j : Fin n) : ℝ :=
  ∑ x : Outcome n,
    (4 * (conj (preMixer prep 1 G γ x) * preMixer prep 1 G γ (flip x i)).im *
        (conj (preMixer prep 1 G γ x) * preMixer prep 1 G γ (flip x j)).im +
      2 * Complex.normSq (preMixer prep 1 G γ x) *
        (preMixer prep 1 G γ (flip x i) * conj (preMixer prep 1 G γ (flip x j))).re -
      2 * Complex.normSq (preMixer prep 1 G γ x) *
        (conj (preMixer prep 1 G γ x) * preMixer prep 1 G γ (flip (flip x i) j)).re)

/-- The number of vertices of the local motif of class `(a, k)`: two roots, `k` shared neighbours
and `3 − a − k` private neighbours per root, `2 + k + 2(3 − a − k) = 8 − 2a − k` vertices
(App. B.2.4, p.30: "The local motif has `2 + k + 2(3 − k) = 8 − k` vertices"). -/
def motifSize (a k : ℕ) : ℕ := k + 2 * (3 - a - k) + 2

/-- The edge relation of the local motif of class `(a, k)` on `{0, …, motifSize a k − 1}`: the
roots are `0` and `1`, adjacent iff `a = 1`; vertices `2, …, k + 1` are the shared neighbours
(adjacent to both roots); the next `3 − a − k` vertices are the private neighbours of root `0`
and the last `3 − a − k` those of root `1`. Only root-incident edges are present. -/
def motifRel (a k : ℕ) (u v : Fin (motifSize a k)) : Prop :=
  (u.val = 0 ∧ v.val = 1 ∧ a = 1) ∨
  (u.val ≤ 1 ∧ 2 ≤ v.val ∧ v.val < 2 + k) ∨
  (u.val = 0 ∧ 2 + k ≤ v.val ∧ v.val < 2 + k + (3 - a - k)) ∨
  (u.val = 1 ∧ 2 + k + (3 - a - k) ≤ v.val)

/-- The local motif `M_{a,k}` of a vertex pair of class `(a, k)` in a cubic graph: the two roots
with their full neighbourhoods and only the root-incident edges (App. B.2.4, p.30; Lemma B.9). -/
def motif (a k : ℕ) : SimpleGraph (Fin (motifSize a k)) := SimpleGraph.fromRel (motifRel a k)

/-- The pair kernel `F_{a,k}(n, θ, φ, γ)` of class `(a, k)` under the product preparation
`|χ(θ, φ)⟩^{⊗n}` (App. B.2.4–B.2.6, pp.30–33, eqs. (53), (61), (72), (74)):
`F_{a,k} = L^{n − N} · K_{M_{a,k}}(0, 1)`, where `N = 8 − 2a − k` is the size of the local motif,
`K_{M_{a,k}}(0, 1)` is the pair kernel (53) of its two roots under `|χ(θ, φ)⟩^{⊗N}`, and
`L = cos⁴(θ/2) + sin⁴(θ/2)` is the factor each spectator vertex contributes (Corollary B.4;
"`F_{0,k}` carries a spectator factor `L^{n−8+k}`", p.30).

**Formalization Note** On every cubic graph on `n` vertices with the degree-aware preparation
(`θ = η`, `φ = −π/2`, since `R_X(η)|0⟩ = |χ(η, −π/2)⟩`) or the Hadamard preparation
(`θ = π/2`, `φ = 0`), the kernel (53) of a pair of class `(a, k)` equals this number (the
summand depends only on the spins of the roots and their neighbours, and a spectator contributes
`∑_z |χ_z|⁴ = L`). Defining `F_{a,k}` through the motif makes it a single real number for every
`n` and every class, including classes no cubic graph on `n` vertices realizes, as the closure
coefficients (66)–(67) require. The exponent `n − N` is an integer (`zpow`); `L ≥ 1/2 > 0`. -/
noncomputable def classKernel (θ φ γ : ℝ) (n a k : ℕ) : ℝ :=
  (Real.cos (θ / 2) ^ 4 + Real.sin (θ / 2) ^ 4) ^ ((n : ℤ) - (motifSize a k : ℤ)) *
    pairKernel (chiPrep (motifSize a k) θ φ) (motif a k) γ
      ⟨0, by unfold motifSize; omega⟩ ⟨1, by unfold motifSize; omega⟩

/-- The closure coefficient `b₃ = 3(v₁ − v₀)` with `v_a = F_{a,1} − F_{a,0}` (Theorem B.17, p.32,
eqs. (66)–(67)), as a function of the preparation angles `(θ, φ)`, the mixer-phase angle `γ` and
`n`. PE-X1 is `(θ, φ) = (η, −π/2)`. -/
noncomputable def closureB3 (θ φ γ : ℝ) (n : ℕ) : ℝ :=
  3 * ((classKernel θ φ γ n 1 1 - classKernel θ φ γ n 1 0) -
    (classKernel θ φ γ n 0 1 - classKernel θ φ γ n 0 0))

/-- The closure coefficient `b₄ = 2δ₀` with `δ_a = F_{a,2} − 2F_{a,1} + F_{a,0}` (Theorem B.17,
p.32, eqs. (66)–(67)). -/
noncomputable def closureB4 (θ φ γ : ℝ) (n : ℕ) : ℝ :=
  2 * (classKernel θ φ γ n 0 2 - 2 * classKernel θ φ γ n 0 1 + classKernel θ φ γ n 0 0)

/-- The closure coefficient `b_D = δ₁ − δ₀` with `δ_a = F_{a,2} − 2F_{a,1} + F_{a,0}`
(Theorem B.17, p.32, eqs. (66)–(67)). -/
noncomputable def closureBD (θ φ γ : ℝ) (n : ℕ) : ℝ :=
  (classKernel θ φ γ n 1 2 - 2 * classKernel θ φ γ n 1 1 + classKernel θ φ γ n 1 0) -
    (classKernel θ φ γ n 0 2 - 2 * classKernel θ φ γ n 0 1 + classKernel θ φ γ n 0 0)

end PhaseEncodedQGE.Supplement


