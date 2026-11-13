-- Prove2me | Definitions.Def_PhaseEncodedQGE_Circuit
-- name    : PhaseEncodedQGE_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:48:42.995102+00:00
-- url     : https://prove2.me/theorems/8b6fbbcc-9eab-4037-8657-9b092df816f7
-- title:
--   The phase-encoded circuit $p^{(P,r)}_G(x;\beta)=|\langle x|(U_M^{(P)}(\beta)U_G(\gamma))^rU_{\mathrm{prep}}|0^n\rangle|^2$ and its first-order value
-- statement:
--   Fix a simple graph $G=(V,E)$ on $n$ vertices, a mixer axis $P\in\{X,Y\}$ and a number $r$ of tied phase–mixer repetitions.
--
--   1. **Rotations.** In the Qiskit convention $R_P(\theta)=e^{-i\theta\sigma_P/2}=\cos(\theta/2)\,I-i\sin(\theta/2)\,\sigma_P$, with $\sigma_X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $\sigma_Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$ in the basis $|0\rangle,|1\rangle$. For a $2\times2$ matrix $A$, $A_i$ denotes $A$ acting on qubit $i$, and $\Sigma=\sum_j\sigma_j$ is the **mixer generator**.
--   2. **Mixer.** $U^{(P)}_M(\beta)=\bigotimes_{v\in V}R_P(\beta)$.
--   3. **Edge phase.** $U_G(\gamma)=\prod_{uv\in E}R^{(uv)}_{ZZ}(\gamma)$ is the diagonal matrix $E$ that multiplies $|x\rangle$ by $\prod_{uv\in E}e^{-i\gamma z_uz_v/2}$.
--   4. **Preparations.** The degree-aware preparation is $U_{\mathrm{prep}}|0^n\rangle=\bigotimes_v R_X(\eta\,d_v/d_{\max})|0\rangle$; on a cubic graph every qubit receives $R_X(\eta)$, so the amplitude of $x$ is $\prod_v a(x_v)$ with $a(0)=c=\cos(\eta/2)$ and $a(1)=-is=-i\sin(\eta/2)$. The Hadamard preparation is $|+\rangle^{\otimes n}$. The phase-general preparation is $|\chi(\theta,\varphi)\rangle^{\otimes n}$ with $|\chi(\theta,\varphi)\rangle=\cos(\theta/2)|0\rangle+e^{i\varphi}\sin(\theta/2)|1\rangle$.
--   5. **Born probabilities.** For a preparation vector $\phi_{\mathrm{prep}}$,
--   $$p^{(P,r)}_G(x;\beta)=\bigl|\bigl((U^{(P)}_M(\beta)\,E)^r\,\phi_{\mathrm{prep}}\bigr)(x)\bigr|^2 .$$
--   6. **First order.** $p_0(x)=p_G(x;0)$, $p_1(x)=\partial_\beta p_G(x;\beta)|_{\beta=0}$, and the **first-order value** is $\lambda(x)=p_1(x)/p_0(x)$. The **pre-mixer amplitude** is $\phi=E^r\phi_{\mathrm{prep}}$.
--
--   The degree-prepared members of the family are PE-X1 ($P=X$, $r=1$), PE-Y1 ($P=Y$, $r=1$) and PE-X2 ($P=X$, $r=2$); PE-QX1 is $P=X$, $r=1$ with the Hadamard preparation.
--
--   **Formalization Note** $\sigma_X,\sigma_Y$ are the platform's published `QAlgorithms.pauliX`, `QAlgorithms.pauliY`. States are vectors indexed by outcomes and gates are matrices over $\mathbb C$; $d_v/d_{\max}$ is a real quotient (Lean's $x/0=0$ only affects the edgeless graph, where the angle is $0$). Each edge is counted once, as an ordered pair $u<v$. $p_1$ is Lean's `deriv` at $0$; $\beta\mapsto p_G(x;\beta)$ is differentiable, so this is the genuine derivative. $\lambda$ uses Lean's $x/0=0$ where $p_0(x)=0$; every statement using $\lambda$ assumes $\cos(\eta/2)\ne0\ne\sin(\eta/2)$, under which $p_0>0$.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §2, p.4 (PDF p.5), eq. (1) and 'The cut phase'; §3, p.6 (PDF p.7); App. A.1.1, p.13 (PDF p.14); App. B.2.6, p.33 (PDF p.34), eq. (72)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_PhaseEncodedQGE_GraphNbhd
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- The two mixer axes `P ∈ {X, Y}` (Miller, Lee, STOC 2027 submission (build 2026-11-03), §2, p.4,
eq. (1)). -/
inductive Axis
  | X
  | Y
  deriving DecidableEq

/-- The Pauli matrix of a mixer axis: `σ_X = [[0,1],[1,0]]` and `σ_Y = [[0,−i],[i,0]]` in the
computational basis, with `false = |0⟩` and `true = |1⟩`. These are the platform's published
`QAlgorithms.pauliX` and `QAlgorithms.pauliY`. -/
def pauli : Axis → Matrix Bool Bool ℂ
  | .X => QAlgorithms.pauliX
  | .Y => QAlgorithms.pauliY

/-- The single-qubit rotation `R_P(θ) = e^{−iθσ_P/2} = cos(θ/2)·I − i sin(θ/2)·σ_P`, in the Qiskit
convention fixed in §2, p.4, below eq. (1). -/
noncomputable def rot (P : Axis) (θ : ℝ) : Matrix Bool Bool ℂ :=
  (Real.cos (θ / 2) : ℂ) • (1 : Matrix Bool Bool ℂ) - (Complex.I * Real.sin (θ / 2)) • pauli P

/-- The `n`-qubit operator acting as the `2 × 2` matrix `A` on qubit `i` and as the identity on the
other qubits, `A_i = I ⊗ ⋯ ⊗ A ⊗ ⋯ ⊗ I` (used for `σ_i` in Lemmas A.1–A.3, pp.13–14). -/
noncomputable def site {n : ℕ} (A : Matrix Bool Bool ℂ) (i : Fin n) :
    Matrix (Outcome n) (Outcome n) ℂ :=
  Matrix.of fun x y => A (x i) (y i) * (if ∀ j, j ≠ i → x j = y j then 1 else 0)

/-- The mixer generator `Σ = ∑_j σ_j` (Lemma A.1, p.13). -/
noncomputable def generator {n : ℕ} (P : Axis) : Matrix (Outcome n) (Outcome n) ℂ :=
  ∑ i : Fin n, site (pauli P) i

/-- The mixer layer `U_M^{(P)}(β) = ∏_{v ∈ V} R_P^{(v)}(β) = ⨂_v R_P(β)` (§2, p.4, eq. (1)). -/
noncomputable def mixer {n : ℕ} (P : Axis) (β : ℝ) : Matrix (Outcome n) (Outcome n) ℂ :=
  Matrix.of fun x y => ∏ v : Fin n, rot P β (x v) (y v)

open Classical in
/-- The scalar by which the edge-phase layer `U_G(γ) = ∏_{uv ∈ E} R_ZZ^{(uv)}(γ)` acts on `|x⟩`:
`∏_{uv ∈ E} e^{−iγ z_u z_v / 2}` (§2, p.4, "The cut phase"). Each edge `uv` is counted once, as the
ordered pair `u < v`. -/
noncomputable def edgePhase {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) : ℂ :=
  ∏ e ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2),
    Complex.exp (-(Complex.I * γ * ((spin x e.1 * spin x e.2 : ℤ) : ℂ)) / 2)

/-- The edge-phase layer as the diagonal matrix `E = U_G(γ)` (§2, eq. (1); "the edge-phase
diagonal", Lemma A.1, p.13). -/
noncomputable def edgeMat {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℝ) :
    Matrix (Outcome n) (Outcome n) ℂ :=
  Matrix.diagonal (edgePhase G γ)

/-- The degree-aware preparation `U_prep|0ⁿ⟩ = ⨂_v R_X(η d_v / d_max)|0⟩` as a vector of
amplitudes (§2, p.4): the amplitude of `x` is `∏_v ⟨x_v| R_X(η d_v/d_max) |0⟩`.

**Formalization Note** `d_v / d_max` is a real quotient; on a cubic graph it equals `1`, so every
vertex receives `R_X(η)` and `⟨0|R_X(η)|0⟩ = cos(η/2) = c`, `⟨1|R_X(η)|0⟩ = −i sin(η/2) = −is`.
For the edgeless graph Lean's `x / 0 = 0` gives the angle `0`. -/
noncomputable def degPrep {n : ℕ} (G : SimpleGraph (Fin n)) (η : ℝ) : Outcome n → ℂ :=
  fun x => ∏ v : Fin n, rot .X (η * (degree G v : ℝ) / (maxDegree G : ℝ)) (x v) false

/-- The Hadamard preparation `|+⟩^{⊗n}`: every amplitude equals `2^{−n/2}` (§2, p.4). -/
noncomputable def hadPrep (n : ℕ) : Outcome n → ℂ :=
  fun _ => ((Real.sqrt 2)⁻¹ : ℂ) ^ n

/-- The phase-general product preparation `|χ(θ, φ)⟩^{⊗n}` with
`|χ(θ, φ)⟩ = cos(θ/2)|0⟩ + e^{iφ} sin(θ/2)|1⟩` on every qubit (App. B.2.6, p.33, eq. (72)). -/
noncomputable def chiPrep (n : ℕ) (θ φ : ℝ) : Outcome n → ℂ :=
  fun x => ∏ v : Fin n,
    if x v then Complex.exp (Complex.I * φ) * (Real.sin (θ / 2) : ℂ) else (Real.cos (θ / 2) : ℂ)

/-- The output state `(U_M^{(P)}(β) U_G(γ))^r U_prep|0ⁿ⟩` of the circuit (1) with mixer axis `P` and
`r` tied phase–mixer repetitions, for a preparation vector `prep` (§2, p.4, eq. (1); App. A.1.1,
p.13: `ψ(β) = (U(β)E)^r ϕ_prep`). -/
noncomputable def circuitState {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ β : ℝ) : Outcome n → ℂ :=
  ((mixer P β * edgeMat G γ) ^ r) *ᵥ prep

/-- The Born probability `p_G^{(P,r)}(x; β) = |⟨x| (U_M^{(P)}(β) U_G(γ))^r U_prep |0ⁿ⟩|²`
(§2, p.4, eq. (1)). -/
noncomputable def born {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ β : ℝ) (x : Outcome n) : ℝ :=
  Complex.normSq (circuitState prep P r G γ β x)

/-- The first-order Born term `p₁(x) = ∂_β p_G(x; β)|_{β=0}` (§3, p.6). `born` is a smooth function
of `β`, so `deriv` is the genuine derivative. -/
noncomputable def bornDeriv {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) : ℝ :=
  deriv (fun β => born prep P r G γ β x) 0

/-- The first-order value `λ(x) = p₁(x) / p₀(x)` with `p₀(x) = p_G(x; 0)` (§3, p.6).

**Formalization Note** Lean's `x / 0 = 0` applies where `p₀(x) = 0`; every statement of the mission
that uses `λ` assumes `cos(η/2) ≠ 0` and `sin(η/2) ≠ 0`, under which `p₀(x) > 0`. -/
noncomputable def firstOrder {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ : ℝ) (x : Outcome n) : ℝ :=
  bornDeriv prep P r G γ x / born prep P r G γ 0 x

/-- The pre-mixer amplitude `ϕ = E^r ϕ_prep`, i.e. `ϕ(x) = (edge phase of x)^r · ϕ_prep(x)`
(§3, p.6; App. A.1.1, p.13). For the degree-aware preparation on a cubic graph and `r = 1` it is
`ϕ(x) = [∏_v a(x_v)] exp[−(iγ/2) ∑_{uv∈E} z_u z_v]` with `a(0) = c`, `a(1) = −is`. -/
noncomputable def preMixer {n : ℕ} (prep : Outcome n → ℂ) (r : ℕ) (G : SimpleGraph (Fin n))
    (γ : ℝ) (x : Outcome n) : ℂ :=
  edgePhase G γ x ^ r * prep x

end PhaseEncodedQGE


